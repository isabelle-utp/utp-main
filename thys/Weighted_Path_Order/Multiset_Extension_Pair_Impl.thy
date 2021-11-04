subsection \<open>Executable version\<close>

theory Multiset_Extension_Pair_Impl
  imports 
    Multiset_Extension_Pair
begin

lemma subset_mult2_alt:
  assumes "X \<subseteq># Y" "(Y, Z) \<in> mult2_alt b ns s" "b \<Longrightarrow> b'"
  shows "(X, Z) \<in> mult2_alt b' ns s"
proof -
  from assms(2) obtain Y1 Y2 Z1 Z2 where *: "Y = Y1 + Y2" "Z = Z1 + Z2"
    "(Y1, Z1) \<in> multpw ns" "b \<or> Z2 \<noteq> {#}" "\<forall>y. y \<in># Y2 \<longrightarrow> (\<exists>z. z \<in># Z2 \<and> (y, z) \<in> s)"
    unfolding mult2_alt_def by blast
  define Y11 Y12 X2 where "Y11 = Y1 \<inter># X" and "Y12 = Y1 - X" and "X2 = X - Y11"
  have **: "X = Y11 + X2" "X2 \<subseteq># Y2" "Y1 = Y11 + Y12" using *(1)
    by (auto simp: Y11_def Y12_def X2_def multiset_eq_iff subseteq_mset_def)
      (metis add.commute assms(1) le_diff_conv subseteq_mset_def)
  obtain Z11 Z12 where ***: "Z = Z11 + (Z12 + Z2)" "Z1 = Z11 + Z12" "(Y11, Z11) \<in> multpw ns"
    using *(2,3) **(3) by (auto elim: multpw_splitR simp: ac_simps)
  moreover have "\<forall>y. y \<in># X2 \<longrightarrow> (\<exists>z. z \<in># Z12 + Z2 \<and> (y, z) \<in> s)" "b \<or> Z12 + Z2 \<noteq> {#}"
    using *(4,5) **(2) by (auto dest!: mset_subset_eqD)
  ultimately show ?thesis using *(2) **(1) assms(3) unfolding mult2_alt_def by blast
qed

text \<open>Case distinction for recursion on left argument\<close>

lemma mem_multiset_diff: "x \<in># A \<Longrightarrow> x \<noteq> y \<Longrightarrow> x \<in># (A - {#y#})" 
  by (metis add_mset_remove_trivial_If diff_single_trivial insert_noteq_member)

lemma mult2_alt_addL: "(add_mset x X, Y) \<in> mult2_alt b ns s \<longleftrightarrow>
  (\<exists>y. y \<in># Y \<and> (x, y) \<in> s \<and> ({# x \<in># X. (x, y) \<notin> s #}, Y - {#y#}) \<in> mult2_alt_ns ns s) \<or>
  (\<exists>y. y \<in># Y \<and> (x, y) \<in> ns \<and> (x, y) \<notin> s \<and> (X, Y - {#y#}) \<in> mult2_alt b ns s)" (is "?L \<longleftrightarrow> ?R1 \<or> ?R2")
proof (intro iffI; (elim disjE)?)
  assume ?L then obtain X1 X2 Y1 Y2 where *: "add_mset x X = X1 + X2" "Y = Y1 + Y2"
    "(X1, Y1) \<in> multpw ns" "b \<or> Y2 \<noteq> {#}" "\<forall>x. x \<in># X2 \<longrightarrow> (\<exists>y. y \<in># Y2 \<and> (x, y) \<in> s)"
    unfolding mult2_alt_def by blast
  from union_single_eq_member[OF this(1)] multi_member_split
  consider X1' where "X1 = add_mset x X1'" "x \<in># X1" | X2' where "X2 = add_mset x X2'" "x \<in># X2"
    unfolding set_mset_union Un_iff by metis
  then show "?R1 \<or> ?R2"
  proof cases
    case 1 then obtain y Y1' where **: "y \<in># Y1" "Y1 = add_mset y Y1'" "(X1', Y1') \<in> multpw ns" "(x, y) \<in> ns"
      using * by (auto elim: multpw_split1R)
    show ?thesis
    proof (cases "(x, y) \<in> s")
      case False then show ?thesis using mult2_altI[OF refl refl **(3) *(4,5)] *
        by (auto simp: 1 ** intro: exI[of _ y])
    next
      case True
      define X2' where "X2' = {# x \<in># X2. (x, y) \<notin> s #}"
      have x3: "\<forall>x. x \<in># X2' \<longrightarrow> (\<exists>z. z \<in># Y2 \<and> (x, z) \<in> s)" using *(5) **(1,2) by (auto simp: X2'_def)
      have x4: "{# x \<in># X. (x, y) \<notin> s#} \<subseteq># X1' + X2'" using *(1) 1
        by (auto simp: X2'_def multiset_eq_iff intro!: mset_subset_eqI split: if_splits elim!: in_countE) (metis le_refl)
      show ?thesis using mult2_alt_nsI[OF refl refl **(3) x3, THEN subset_mult2_alt[OF x4]]
          **(2) *(2) True by (auto intro: exI[of _ y])
    qed
  next
    case 2 then obtain y where **: "y \<in># Y2" "(x, y) \<in> s" using * by blast
    define X2' where "X2' = {# x \<in># X2. (x, y) \<notin> s #}"
    have x3: "\<forall>x. x \<in># X2' \<longrightarrow> (\<exists>z. z \<in># Y2 - {#y#} \<and> (x, z) \<in> s)"
      using *(5) **(1,2) by (auto simp: X2'_def) (metis mem_multiset_diff) 
    have x4: "{# x \<in># X. (x, y) \<notin> s#} \<subseteq># X1 + X2'"
      using *(1) **(2) by (auto simp: X2'_def multiset_eq_iff intro!: mset_subset_eqI split: if_splits)
    show ?thesis
      using mult2_alt_nsI[OF refl refl *(3) x3, THEN subset_mult2_alt[OF x4], of True] **(1,2) *(2)
      by (auto simp: diff_union_single_conv[symmetric])
  qed
next
  assume ?R1
  then obtain y where *: "y \<in># Y" "(x, y) \<in> s" "({# x \<in># X. (x, y) \<notin> s #}, Y - {#y#}) \<in> mult2_alt_ns ns s"
    by blast
  then have **: "({# x \<in># X. (x, y) \<in> s #} + {#x#}, {#y#}) \<in> mult2_alt b ns s"
    "{# x \<in># X. (x, y) \<notin> s #} + {# x \<in># X. (x, y) \<in> s #} = X"
    by (auto intro: mult2_altI[of _ "{#}" _ _ "{#}"] multiset_eqI split: if_splits)
  show ?L using mult2_alt_add[OF *(3) **(1)] * ** by (auto simp: union_assoc[symmetric])
next
  assume ?R2
  then obtain y where *: "y \<in># Y" "(x, y) \<in> ns" "(X, Y - {#y#}) \<in> mult2_alt b ns s" by blast
  then show ?L using mult2_alt_add[OF *(3) multpw_implies_mult2_alt_ns, of "{#x#}" "{#y#}"]
    by (auto intro: multpw_single)
qed

text \<open>Auxiliary version with an extra @{typ bool} argument for distinguishing between the
  non-strict and the strict orders\<close>

context fixes nss :: "'a \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> bool"
begin

fun mult2_impl0 :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool \<Rightarrow> bool"
  and mult2_ex_dom0 :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool \<Rightarrow> bool"
  where
    "mult2_impl0 []       [] b \<longleftrightarrow> b"
  | "mult2_impl0 xs       [] b \<longleftrightarrow> False"
  | "mult2_impl0 []       ys b \<longleftrightarrow> True"
  | "mult2_impl0 (x # xs) ys b \<longleftrightarrow> mult2_ex_dom0 x xs ys [] b"

| "mult2_ex_dom0 x xs []       ys' b \<longleftrightarrow> False"
| "mult2_ex_dom0 x xs (y # ys) ys' b \<longleftrightarrow>
     nss x y False \<and> mult2_impl0 (filter (\<lambda>x. \<not> nss x y False) xs) (ys @ ys') True \<or>
     nss x y True \<and> \<not> nss x y False \<and> mult2_impl0 xs (ys @ ys') b \<or>
     mult2_ex_dom0 x xs ys (y # ys') b"

end

lemma mult2_impl0_sound:
  fixes nss
  defines "ns \<equiv> {(x, y). nss x y True}" and "s \<equiv> {(x, y). nss x y False}"
  shows "mult2_impl0 nss xs ys b \<longleftrightarrow> (mset xs, mset ys) \<in> mult2_alt b ns s"
    "mult2_ex_dom0 nss x xs ys ys' b \<longleftrightarrow>
      (\<exists>y. y \<in># mset ys \<and> (x, y) \<in> s \<and> (mset (filter (\<lambda>x. (x, y) \<notin> s) xs), mset (ys @ ys') - {#y#}) \<in> mult2_alt True ns s) \<or>
      (\<exists>y. y \<in># mset ys \<and> (x, y) \<in> ns \<and> (x, y) \<notin> s \<and> (mset xs, mset (ys @ ys') - {#y#}) \<in> mult2_alt b ns s)"
proof (induct xs ys b and x xs ys ys' b taking: nss rule: mult2_impl0_mult2_ex_dom0.induct)
  case (4 x xs y ys b) show ?case unfolding mult2_impl0.simps 4
    using mult2_alt_addL[of x "mset xs" "mset (y # ys)" b ns s] by (simp add: mset_filter)
next
  case (6 x xs y ys ys' b) show ?case unfolding mult2_ex_dom0.simps 6
    using subset_mult2_alt[of "mset [x\<leftarrow>xs . (x, y) \<notin> s]" "mset xs" "mset (ys @ ys')" b ns s True]
    apply (intro iffI; elim disjE conjE exE; simp add: mset_filter ns_def s_def; (elim disjE)?)
    subgoal by (intro disjI1 exI[of _ y]) auto
    subgoal by (intro disjI2 exI[of _ y]) auto
    subgoal for y' by (intro disjI1 exI[of _ y']) auto
    subgoal for y' by (intro disjI2 exI[of _ y']) auto
    subgoal for y' by simp
    subgoal for y' by (rule disjI2, rule disjI2, rule disjI1, rule exI[of _ y']) simp
    subgoal for y' by simp
    subgoal for y' by (rule disjI2, rule disjI2, rule disjI2, rule exI[of _ y']) simp
    done
qed (auto simp: mult2_alt_emptyL mult2_alt_emptyR)

text \<open>Now, instead of functions of type @{typ "bool \<Rightarrow> bool"}, use pairs of type
  @{typ "bool \<times> bool"}\<close>

definition [simp]: "or2 a b = (fst a \<or> fst b, snd a \<or> snd b)"

context fixes sns :: "'a \<Rightarrow> 'a \<Rightarrow> bool \<times> bool"
begin

fun mult2_impl :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool \<times> bool"
  and mult2_ex_dom :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool \<times> bool"
  where
    "mult2_impl []       [] = (False, True)"
  | "mult2_impl xs       [] = (False, False)"
  | "mult2_impl []       ys = (True, True)"
  | "mult2_impl (x # xs) ys = mult2_ex_dom x xs ys []"

| "mult2_ex_dom x xs []       ys' = (False, False)"
| "mult2_ex_dom x xs (y # ys) ys' =
    (case sns x y of
      (True, _) \<Rightarrow> if snd (mult2_impl (filter (\<lambda>x. \<not> fst (sns x y)) xs) (ys @ ys')) then (True, True)
                   else mult2_ex_dom x xs ys (y # ys')
    | (False, True) \<Rightarrow> or2 (mult2_impl xs (ys @ ys')) (mult2_ex_dom x xs ys (y # ys'))
    | _ \<Rightarrow> mult2_ex_dom x xs ys (y # ys'))"
end

lemma mult2_impl_sound0:
  defines "pair \<equiv> \<lambda>f. (f False, f True)" and "fun \<equiv> \<lambda>p b. if b then snd p else fst p"
  shows "mult2_impl sns xs ys = pair (mult2_impl0 (\<lambda>x y. fun (sns x y)) xs ys)" (is ?P)
    "mult2_ex_dom sns x xs ys ys' = pair (mult2_ex_dom0 (\<lambda>x y. fun (sns x y)) x xs ys ys')" (is ?Q)
proof -
  show ?P ?Q
  proof (induct xs ys and x xs ys ys' taking: sns rule: mult2_impl_mult2_ex_dom.induct)
    case (6 x xs y ys ys')
    show ?case unfolding mult2_ex_dom.simps mult2_ex_dom0.simps
      by (fastforce simp: pair_def fun_def 6 if_bool_eq_conj split: prod.splits bool.splits)
  qed (auto simp: pair_def fun_def if_bool_eq_conj)
qed

lemmas mult2_impl_sound = mult2_impl_sound0(1)[unfolded mult2_impl0_sound if_True if_False]
end
