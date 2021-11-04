subsection \<open>The Bellman-Ford Algorithm\<close>

theory Bellman_Ford
  imports
    "HOL-Library.IArray"
    "HOL-Library.Code_Target_Numeral"
    "HOL-Library.Product_Lexorder"
    "HOL-Library.RBT_Mapping"
    "../heap_monad/Heap_Main"
    Example_Misc
    "../util/Tracing"
    "../util/Ground_Function"
begin

subsubsection \<open>Misc\<close>

lemma nat_le_cases:
  fixes n :: nat
  assumes "i \<le> n"
  obtains "i < n" | "i = n"
  using assms by (cases "i = n") auto

context dp_consistency_iterator
begin

lemma crel_vs_iterate_state:
  "crel_vs (=) () (iter_state f x)" if "((=) ===>\<^sub>T R) g f"
  by (metis crel_vs_iterate_state iter_state_iterate_state that)

lemma consistent_crel_vs_iterate_state:
  "crel_vs (=) () (iter_state f x)" if "consistentDP f"
  using consistentDP_def crel_vs_iterate_state that by simp

end

instance extended :: (countable) countable
proof standard
  obtain to_nat :: "'a \<Rightarrow> nat" where "inj to_nat"
    by auto
  let ?f = "\<lambda> x. case x of Fin n \<Rightarrow> to_nat n + 2 | Pinf \<Rightarrow> 0 | Minf \<Rightarrow> 1"
  from \<open>inj _ \<close> have "inj ?f"
    by (auto simp: inj_def split: extended.split)
  then show "\<exists>to_nat :: 'a extended \<Rightarrow> nat. inj to_nat"
    by auto
qed

instance extended :: (heap) heap ..

instantiation "extended" :: (conditionally_complete_lattice) complete_lattice
begin

definition
  "Inf A = (
    if A = {} \<or> A = {\<infinity>} then \<infinity>
    else if -\<infinity> \<in> A \<or> \<not> bdd_below (Fin -` A) then -\<infinity>
    else Fin (Inf (Fin -` A)))"

definition
  "Sup A = (
    if A = {} \<or> A = {-\<infinity>} then -\<infinity>
    else if \<infinity> \<in> A \<or> \<not> bdd_above (Fin -` A) then \<infinity>
    else Fin (Sup (Fin -` A)))"

instance
proof standard
  have [dest]: "Inf (Fin -` A) \<le> x" if "Fin x \<in> A" "bdd_below (Fin -` A)" for A and x :: 'a
    using that by (intro cInf_lower) auto
  have *: False if "\<not> z \<le> Inf (Fin -` A)" "\<And>x. x \<in> A \<Longrightarrow> Fin z \<le> x" "Fin x \<in> A" for A and x z :: 'a
    using cInf_greatest[of "Fin -` A" z] that vimage_eq by force
  show "Inf A \<le> x" if "x \<in> A" for x :: "'a extended" and A
    using that unfolding Inf_extended_def by (cases x) auto
  show "z \<le> Inf A" if "\<And>x. x \<in> A \<Longrightarrow> z \<le> x" for z :: "'a extended" and A
    using that
    unfolding Inf_extended_def
    apply (clarsimp; safe)
         apply force
        apply force
    subgoal
      by (cases z; force simp: bdd_below_def)
    subgoal
      by (cases z; force simp: bdd_below_def)
    subgoal for x y
      by (cases z; cases y) (auto elim: *)
    subgoal for x y
      by (cases z; cases y; simp; metis * less_eq_extended.elims(2))
    done
  have [dest]: "x \<le> Sup (Fin -` A)" if "Fin x \<in> A" "bdd_above (Fin -` A)" for A and x :: 'a
    using that by (intro cSup_upper) auto
  have *: False if "\<not> Sup (Fin -` A) \<le> z" "\<And>x. x \<in> A \<Longrightarrow> x \<le> Fin z" "Fin x \<in> A" for A and x z :: 'a
    using cSup_least[of "Fin -` A" z] that vimage_eq by force
  show "x \<le> Sup A" if "x \<in> A" for x :: "'a extended" and A
    using that unfolding Sup_extended_def by (cases x) auto
  show "Sup A \<le> z" if "\<And>x. x \<in> A \<Longrightarrow> x \<le> z" for z :: "'a extended" and A
    using that
    unfolding Sup_extended_def
    apply (clarsimp; safe)
         apply force
        apply force
    subgoal
      by (cases z; force)
    subgoal
      by (cases z; force)
    subgoal for x y
      by (cases z; cases y) (auto elim: *)
    subgoal for x y
      by (cases z; cases y; simp; metis * extended.exhaust)
    done
  show "Inf {} = (top::'a extended)"
    unfolding Inf_extended_def top_extended_def by simp
  show "Sup {} = (bot::'a extended)"
    unfolding Sup_extended_def bot_extended_def by simp
qed

end

instance "extended" :: ("{conditionally_complete_lattice,linorder}") complete_linorder ..


lemma Minf_eq_zero[simp]: "-\<infinity> = 0 \<longleftrightarrow> False" and Pinf_eq_zero[simp]: "\<infinity> = 0 \<longleftrightarrow> False"
  unfolding zero_extended_def by auto

lemma Sup_int:
  fixes x :: int and X :: "int set"
  assumes "X \<noteq> {}" "bdd_above X"
  shows "Sup X \<in> X \<and> (\<forall>y\<in>X. y \<le> Sup X)"
proof -
  from assms obtain x y where "X \<subseteq> {..y}" "x \<in> X"
    by (auto simp: bdd_above_def)
  then have *: "finite (X \<inter> {x..y})" "X \<inter> {x..y} \<noteq> {}" and "x \<le> y"
    by (auto simp: subset_eq)
  have "\<exists>!x\<in>X. (\<forall>y\<in>X. y \<le> x)"
  proof
    { fix z assume "z \<in> X"
      have "z \<le> Max (X \<inter> {x..y})"
      proof cases
        assume "x \<le> z" with \<open>z \<in> X\<close> \<open>X \<subseteq> {..y}\<close> *(1) show ?thesis
          by (auto intro!: Max_ge)
      next
        assume "\<not> x \<le> z"
        then have "z < x" by simp
        also have "x \<le> Max (X \<inter> {x..y})"
          using \<open>x \<in> X\<close> *(1) \<open>x \<le> y\<close> by (intro Max_ge) auto
        finally show ?thesis by simp
      qed }
    note le = this
    with Max_in[OF *] show ex: "Max (X \<inter> {x..y}) \<in> X \<and> (\<forall>z\<in>X. z \<le> Max (X \<inter> {x..y}))" by auto

    fix z assume *: "z \<in> X \<and> (\<forall>y\<in>X. y \<le> z)"
    with le have "z \<le> Max (X \<inter> {x..y})"
      by auto
    moreover have "Max (X \<inter> {x..y}) \<le> z"
      using * ex by auto
    ultimately show "z = Max (X \<inter> {x..y})"
      by auto
  qed
  then show "Sup X \<in> X \<and> (\<forall>y\<in>X. y \<le> Sup X)"
    unfolding Sup_int_def by (rule theI')
qed

lemmas Sup_int_in = Sup_int[THEN conjunct1]

lemma Inf_int_in:
  fixes S :: "int set"
  assumes "S \<noteq> {}" "bdd_below S"
  shows "Inf S \<in> S"
  using assms unfolding Inf_int_def by (smt Sup_int_in bdd_above_uminus image_iff image_is_empty)


lemma finite_setcompr_eq_image: "finite {f x |x. P x} \<longleftrightarrow> finite (f ` {x. P x})"
  by (simp add: setcompr_eq_image)

lemma finite_lists_length_le1: "finite {xs. length xs \<le> i \<and> set xs \<subseteq> {0..(n::nat)}}" for i
  by (auto intro: finite_subset[OF _ finite_lists_length_le[OF finite_atLeastAtMost]])

lemma finite_lists_length_le2: "finite {xs. length xs + 1 \<le> i \<and> set xs \<subseteq> {0..(n::nat)}}" for i
  by (auto intro: finite_subset[OF _ finite_lists_length_le1[of "i"]])

lemmas [simp] =
  finite_setcompr_eq_image finite_lists_length_le2[simplified] finite_lists_length_le1


lemma get_return:
  "run_state (State_Monad.bind State_Monad.get (\<lambda> m. State_Monad.return (f m))) m = (f m, m)"
  by (simp add: State_Monad.bind_def State_Monad.get_def)


lemma list_pidgeonhole:
  assumes "set xs \<subseteq> S" "card S < length xs" "finite S"
  obtains as a bs cs where "xs = as @ a # bs @ a # cs"
proof -
  from assms have "\<not> distinct xs"
    by (metis card_mono distinct_card not_le)
  then show ?thesis
    by (metis append.assoc append_Cons not_distinct_conv_prefix split_list that)
qed

lemma path_eq_cycleE:
  assumes "v # ys @ [t] = as @ a # bs @ a # cs"
  obtains (Nil_Nil) "as = []" "cs = []" "v = a" "a = t" "ys = bs"
  | (Nil_Cons) cs' where "as = []" "v = a" "ys = bs @ a # cs'" "cs = cs' @ [t]"
  | (Cons_Nil) as' where "as = v # as'" "cs = []" "a = t" "ys = as' @ a # bs"
  | (Cons_Cons) as' cs' where "as = v # as'" "cs = cs' @ [t]" "ys = as' @ a # bs @ a # cs'"
  using assms by (auto simp: Cons_eq_append_conv append_eq_Cons_conv append_eq_append_conv2)

lemma le_add_same_cancel1:
  "a + b \<ge> a \<longleftrightarrow> b \<ge> 0" if "a < \<infinity>" "-\<infinity> < a" for a b :: "int extended"
  using that by (cases a; cases b) (auto simp add: zero_extended_def)

lemma add_gt_minfI:
  assumes "-\<infinity> < a" "-\<infinity> < b"
  shows "-\<infinity> < a + b"
  using assms by (cases a; cases b) auto

lemma add_lt_infI:
  assumes "a < \<infinity>" "b < \<infinity>"
  shows "a + b < \<infinity>"
  using assms by (cases a; cases b) auto

lemma sum_list_not_infI:
  "sum_list xs < \<infinity>" if "\<forall> x \<in> set xs. x < \<infinity>" for xs :: "int extended list"
  using that
  apply (induction xs)
   apply (simp add: zero_extended_def)+
  by (smt less_extended_simps(2) plus_extended.elims)

lemma sum_list_not_minfI:
  "sum_list xs > -\<infinity>" if "\<forall> x \<in> set xs. x > -\<infinity>" for xs :: "int extended list"
  using that by (induction xs) (auto intro: add_gt_minfI simp: zero_extended_def)



subsubsection \<open>Single-Sink Shortest Path Problem\<close>

datatype bf_result = Path "nat list" int | No_Path | Computation_Error

context
  fixes n :: nat and W :: "nat \<Rightarrow> nat \<Rightarrow> int extended"
begin

context
  fixes t :: nat \<comment> \<open>Final node\<close>
begin

text \<open>
  The correctness proof closely follows Kleinberg \<open>&\<close> Tardos: "Algorithm Design",
  chapter "Dynamic Programming" @{cite "Kleinberg-Tardos"}
\<close>

fun weight :: "nat list \<Rightarrow> int extended" where
  "weight [s] = 0"
| "weight (i # j # xs) = W i j + weight (j # xs)"

definition
  "OPT i v = (
    Min (
      {weight (v # xs @ [t]) | xs. length xs + 1 \<le> i \<and> set xs \<subseteq> {0..n}} \<union>
      {if t = v then 0 else \<infinity>}
    )
  )"

lemma weight_alt_def':
  "weight (s # xs) + w = snd (fold (\<lambda>j (i, x). (j, W i j + x)) xs (s, w))"
  by (induction xs arbitrary: s w; simp; smt add.commute add.left_commute)

lemma weight_alt_def:
  "weight (s # xs) = snd (fold (\<lambda>j (i, x). (j, W i j + x)) xs (s, 0))"
  by (rule weight_alt_def'[of s xs 0, simplified])

lemma weight_append:
  "weight (xs @ a # ys) = weight (xs @ [a]) + weight (a # ys)"
  by (induction xs rule: weight.induct; simp add: add.assoc)

lemma OPT_0:
  "OPT 0 v = (if t = v then 0 else \<infinity>)"
  unfolding OPT_def by simp


subsubsection \<open>Functional Correctness\<close>

lemma OPT_cases:
  obtains (path) xs where "OPT i v = weight (v # xs @ [t])" "length xs + 1 \<le> i" "set xs \<subseteq> {0..n}"
  | (sink) "v = t" "OPT i v = 0"
  | (unreachable) "v \<noteq> t" "OPT i v = \<infinity>"
  unfolding OPT_def
  using Min_in[of "{weight (v # xs @ [t]) |xs. length xs + 1 \<le> i \<and> set xs \<subseteq> {0..n}}
    \<union> {if t = v then 0 else \<infinity>}"]
  by (auto simp: finite_lists_length_le2[simplified] split: if_split_asm)

lemma OPT_Suc:
  "OPT (Suc i) v = min (OPT i v) (Min {OPT i w + W v w | w. w \<le> n})" (is "?lhs = ?rhs")
  if "t \<le> n"
proof -
  have "OPT i w + W v w \<ge> OPT (Suc i) v" if "w \<le> n" for w
    using OPT_cases[of i w]
  proof cases
    case (path xs)
    with \<open>w \<le> n\<close> show ?thesis
      by (subst OPT_def) (auto intro!: Min_le exI[where x = "w # xs"] simp: add.commute)
  next
    case sink
    then show ?thesis
      by (subst OPT_def) (auto intro!: Min_le exI[where x = "[]"])
  next
    case unreachable
    then show ?thesis
      by simp
  qed
  then have "Min {OPT i w + W v w |w. w \<le> n} \<ge> OPT (Suc i) v"
    by (auto intro!: Min.boundedI)
  moreover have "OPT i v \<ge> OPT (Suc i) v"
    unfolding OPT_def by (rule Min_antimono) auto
  ultimately have "?lhs \<le> ?rhs"
    by simp

  from OPT_cases[of "Suc i" v] have "?lhs \<ge> ?rhs"
  proof cases
    case (path xs)
    note [simp] = path(1)
    from path consider
      (zero) "i = 0" "length xs = 0" | (new) "i > 0" "length xs = i" | (old) "length xs < i"
      by (cases "length xs = i") auto
    then show ?thesis
    proof cases
      case zero
      with path have "OPT (Suc i) v = W v t"
        by simp
      also have "W v t = OPT i t + W v t"
        unfolding OPT_def using \<open>i = 0\<close> by auto
      also have "\<dots> \<ge> Min {OPT i w + W v w |w. w \<le> n}"
        using \<open>t \<le> n\<close> by (auto intro: Min_le)
      finally show ?thesis
        by (rule min.coboundedI2)
    next
      case new
      with \<open>_ = i\<close> obtain u ys where [simp]: "xs = u # ys"
        by (cases xs) auto
      from path have "OPT i u \<le> weight (u # ys @ [t])"
        unfolding OPT_def by (intro Min_le) auto
      from path have "Min {OPT i w + W v w |w. w \<le> n} \<le> W v u + OPT i u"
        by (intro Min_le) (auto simp: add.commute)
      also from \<open>OPT i u \<le> _\<close> have "\<dots> \<le> OPT (Suc i) v"
        by (simp add: add_left_mono)
      finally show ?thesis
        by (rule min.coboundedI2)
    next
      case old
      with path have "OPT i v \<le> OPT (Suc i) v"
        by (auto 4 3 intro: Min_le simp: OPT_def)
      then show ?thesis
        by (rule min.coboundedI1)
    qed
  next
    case unreachable
    then show ?thesis
      by simp
  next
    case sink
    then have "OPT i v \<le> OPT (Suc i) v"
      unfolding OPT_def by auto
    then show ?thesis
      by (rule min.coboundedI1)
  qed

  with \<open>?lhs \<le> ?rhs\<close> show ?thesis
    by (rule order.antisym)
qed

fun bf :: "nat \<Rightarrow> nat \<Rightarrow> int extended" where
  "bf 0 j = (if t = j then 0 else \<infinity>)"
| "bf (Suc k) j = min_list
      (bf k j # [W j i + bf k i . i \<leftarrow> [0 ..< Suc n]])"

lemmas [simp del] = bf.simps
lemmas bf_simps[simp] = bf.simps[unfolded min_list_fold]

lemma bf_correct:
  "OPT i j = bf i j" if \<open>t \<le> n\<close>
proof (induction i arbitrary: j)
  case 0
  then show ?case
    by (simp add: OPT_0)
next
  case (Suc i)
  have *:
    "{bf i w + W j w |w. w \<le> n} = set (map (\<lambda>w. W j w + bf i w) [0..<Suc n])"
    by (fastforce simp: add.commute image_def)
  from Suc \<open>t \<le> n\<close> show ?case
    by (simp add: OPT_Suc del: upt_Suc, subst Min.set_eq_fold[symmetric], auto simp: *)
qed


subsubsection \<open>Functional Memoization\<close>

memoize_fun bf\<^sub>m: bf with_memory dp_consistency_mapping monadifies (state) bf.simps

text \<open>Generated Definitions\<close>
context includes state_monad_syntax begin
thm bf\<^sub>m'.simps bf\<^sub>m_def
end

text \<open>Correspondence Proof\<close>
memoize_correct
  by memoize_prover
print_theorems
lemmas [code] = bf\<^sub>m.memoized_correct

interpretation iterator
  "\<lambda> (x, y). x \<le> n \<and> y \<le> n"
  "\<lambda> (x, y). if y < n then (x, y + 1) else (x + 1, 0)"
  "\<lambda> (x, y). x * (n + 1) + y"
  by (rule table_iterator_up)

interpretation bottom_up: dp_consistency_iterator_empty
  "\<lambda> (_::(nat \<times> nat, int extended) mapping). True"
  "\<lambda> (x, y). bf x y"
  "\<lambda> k. do {m \<leftarrow> State_Monad.get; State_Monad.return (Mapping.lookup m k :: int extended option)}"
  "\<lambda> k v. do {m \<leftarrow> State_Monad.get; State_Monad.set (Mapping.update k v m)}"
  "\<lambda> (x, y). x \<le> n \<and> y \<le> n"
  "\<lambda> (x, y). if y < n then (x, y + 1) else (x + 1, 0)"
  "\<lambda> (x, y). x * (n + 1) + y"
  Mapping.empty ..

definition
  "iter_bf = iter_state (\<lambda> (x, y). bf\<^sub>m' x y)"

lemma iter_bf_unfold[code]:
  "iter_bf = (\<lambda> (i, j).
    (if i \<le> n \<and> j \<le> n
     then do {
            bf\<^sub>m' i j;
            iter_bf (if j < n then (i, j + 1) else (i + 1, 0))
          }
     else State_Monad.return ()))"
  unfolding iter_bf_def by (rule ext) (safe, clarsimp simp: iter_state_unfold)

lemmas bf_memoized = bf\<^sub>m.memoized[OF bf\<^sub>m.crel]
lemmas bf_bottom_up = bottom_up.memoized[OF bf\<^sub>m.crel, folded iter_bf_def]

text \<open>
This will be our final implementation, which includes detection of negative cycles.
See the corresponding section below for the correctness proof.
\<close>
definition
  "bellman_ford \<equiv>
    do {
      _  \<leftarrow> iter_bf (n, n);
      xs \<leftarrow> State_Main.map\<^sub>T' (\<lambda>i. bf\<^sub>m' n i) [0..<n+1];
      ys \<leftarrow> State_Main.map\<^sub>T' (\<lambda>i. bf\<^sub>m' (n + 1) i) [0..<n+1];
      State_Monad.return (if xs = ys then Some xs else None)
    }"

context
  includes state_monad_syntax
begin

lemma bellman_ford_alt_def:
  "bellman_ford \<equiv>
    do {
      _  \<leftarrow> iter_bf (n, n);
      (\<langle>\<lambda>xs. \<langle>\<lambda>ys. State_Monad.return (if xs = ys then Some xs else None)\<rangle>
      . (State_Main.map\<^sub>T . \<langle>\<lambda>i. bf\<^sub>m' (n + 1) i\<rangle> . \<langle>[0..<n+1]\<rangle>)\<rangle>)
      . (State_Main.map\<^sub>T . \<langle>\<lambda>i. bf\<^sub>m' n i\<rangle>       . \<langle>[0..<n+1]\<rangle>)
    }"
  unfolding
    State_Monad_Ext.fun_app_lifted_def bellman_ford_def State_Main.map\<^sub>T_def bind_left_identity
  .

end



subsubsection \<open>Imperative Memoization\<close>

context
  fixes mem :: "nat ref \<times> nat ref \<times> int extended option array ref \<times> int extended option array ref"
  assumes mem_is_init: "mem = result_of (init_state (n + 1) 1 0) Heap.empty"
begin

lemma [intro]:
  "dp_consistency_heap_array_pair' (n + 1) fst snd id 1 0 mem"
  by (standard; simp add: mem_is_init injective_def)

interpretation iterator
  "\<lambda> (x, y). x \<le> n \<and> y \<le> n"
  "\<lambda> (x, y). if y < n then (x, y + 1) else (x + 1, 0)"
  "\<lambda> (x, y). x * (n + 1) + y"
  by (rule table_iterator_up)

lemma [intro]:
  "dp_consistency_heap_array_pair_iterator (n + 1) fst snd id 1 0 mem
  (\<lambda> (x, y). if y < n then (x, y + 1) else (x + 1, 0))
  (\<lambda> (x, y). x * (n + 1) + y)
  (\<lambda> (x, y). x \<le> n \<and> y \<le> n)"
  by (standard; simp add: mem_is_init injective_def)

memoize_fun bf\<^sub>h: bf
  with_memory (default_proof) dp_consistency_heap_array_pair_iterator
  where size = "n + 1"
    and key1 = "fst :: nat \<times> nat \<Rightarrow> nat" and key2 = "snd :: nat \<times> nat \<Rightarrow> nat"
    and k1 = "1 :: nat" and k2 = "0 :: nat"
    and to_index = "id :: nat \<Rightarrow> nat"
    and mem = mem
    and cnt = "\<lambda> (x, y). x \<le> n \<and> y \<le> n"
    and nxt = "\<lambda> (x :: nat, y). if y < n then (x, y + 1) else (x + 1, 0)"
    and sizef = "\<lambda> (x, y). x * (n + 1) + y"
monadifies (heap) bf.simps

memoize_correct
  by memoize_prover

lemmas memoized_empty = bf\<^sub>h.memoized_empty[OF bf\<^sub>h.consistent_DP_iter_and_compute[OF bf\<^sub>h.crel]]
lemmas iter_heap_unfold = iter_heap_unfold

end (* Fixed Memory *)


subsubsection \<open>Detecting Negative Cycles\<close>

definition
  "shortest v = (
    Inf (
      {weight (v # xs @ [t]) | xs. set xs \<subseteq> {0..n}} \<union>
      {if t = v then 0 else \<infinity>}
    )
  )"

definition
  "is_path xs \<equiv> weight (xs @ [t]) < \<infinity>"

definition
  "has_negative_cycle \<equiv>
  \<exists>xs a ys. set (a # xs @ ys) \<subseteq> {0..n} \<and> weight (a # xs @ [a]) < 0 \<and> is_path (a # ys)"

definition
  "reaches a \<equiv> \<exists>xs. is_path (a # xs) \<and> a \<le> n \<and> set xs \<subseteq> {0..n}"

lemma fold_sum_aux':
  assumes "\<forall>u \<in> set (a # xs). \<forall>v \<in> set (xs @ [b]). f v + W u v \<ge> f u"
  shows "sum_list (map f (a # xs)) \<le> sum_list (map f (xs @ [b])) + weight (a # xs @ [b])"
  using assms
  by (induction xs arbitrary: a; simp)
     (smt ab_semigroup_add_class.add_ac(1) add.left_commute add_mono)

lemma fold_sum_aux:
  assumes "\<forall>u \<in> set (a # xs). \<forall>v \<in> set (a # xs). f v + W u v \<ge> f u"
  shows "sum_list (map f (a # xs @ [a])) \<le> sum_list (map f (a # xs @ [a])) + weight (a # xs @ [a])"
  using fold_sum_aux'[of a xs a f] assms
  by auto (metis (no_types, hide_lams) add.assoc add.commute add_left_mono)

context
begin

private definition "is_path2 xs \<equiv> weight xs < \<infinity>"

private lemma is_path2_remove_cycle:
  assumes "is_path2 (as @ a # bs @ a # cs)"
  shows "is_path2 (as @ a # cs)"
proof -
  have "weight (as @ a # bs @ a # cs) =
    weight (as @ [a]) + weight (a # bs @ [a]) + weight (a # cs)"
    by (metis Bellman_Ford.weight_append append_Cons append_assoc)
  with assms have "weight (as @ [a]) < \<infinity>" "weight (a # cs) < \<infinity>"
    unfolding is_path2_def
    by (simp, metis Pinf_add_right antisym less_extended_simps(4) not_less add.commute)+
  then show ?thesis
    unfolding is_path2_def by (subst weight_append) (rule add_lt_infI)
qed

private lemma is_path_eq:
  "is_path xs \<longleftrightarrow> is_path2 (xs @ [t])"
  unfolding is_path_def is_path2_def ..

lemma is_path_remove_cycle:
  assumes "is_path (as @ a # bs @ a # cs)"
  shows "is_path (as @ a # cs)"
  using assms unfolding is_path_eq by (simp add: is_path2_remove_cycle)

lemma is_path_remove_cycle2:
  assumes "is_path (as @ t # cs)"
  shows "is_path as"
  using assms unfolding is_path_eq by (simp add: is_path2_remove_cycle)

end (* private lemmas *)

lemma is_path_shorten:
  assumes "is_path (i # xs)" "i \<le> n" "set xs \<subseteq> {0..n}" "t \<le> n" "t \<noteq> i"
  obtains xs where "is_path (i # xs)" "i \<le> n" "set xs \<subseteq> {0..n}" "length xs < n"
proof (cases "length xs < n")
  case True
  with assms show ?thesis
    by (auto intro: that)
next
  case False
  then have "length xs \<ge> n"
    by auto
  with assms(1,3) show ?thesis
  proof (induction "length xs" arbitrary: xs rule: less_induct)
    case less
    then have "length (i # xs @ [t]) > card ({0..n})"
      by auto
    moreover from less.prems \<open>i \<le> n\<close> \<open>t \<le> n\<close> have "set (i # xs @ [t]) \<subseteq> {0..n}"
      by auto
    ultimately obtain a as bs cs where *: "i # xs @ [t] = as @ a # bs @ a # cs"
      by (elim list_pidgeonhole) auto
    obtain ys where ys: "is_path (i # ys)" "length ys < length xs" "set (i # ys) \<subseteq> {0..n}"
      apply atomize_elim
      using *
    proof (cases rule: path_eq_cycleE)
      case Nil_Nil
      with \<open>t \<noteq> i\<close> show "\<exists>ys. is_path (i # ys) \<and> length ys < length xs \<and> set (i # ys) \<subseteq> {0..n}"
        by auto
    next
      case (Nil_Cons cs')
      then show "\<exists>ys. is_path (i # ys) \<and> length ys < length xs \<and> set (i # ys) \<subseteq> {0..n}"
        using \<open>set (i # xs @ [t]) \<subseteq> {0..n}\<close> \<open>is_path (i # xs)\<close> is_path_remove_cycle[of "[]"]
        by - (rule exI[where x = cs'], simp)
    next
      case (Cons_Nil as')
      then show "\<exists>ys. is_path (i # ys) \<and> length ys < length xs \<and> set (i # ys) \<subseteq> {0..n}"
        using \<open>set (i # xs @ [t]) \<subseteq> {0..n}\<close> \<open>is_path (i # xs)\<close>
        by - (rule exI[where x = as'], auto intro: is_path_remove_cycle2)
    next
      case (Cons_Cons as' cs')
      then show "\<exists>ys. is_path (i # ys) \<and> length ys < length xs \<and> set (i # ys) \<subseteq> {0..n}"
        using \<open>set (i # xs @ [t]) \<subseteq> {0..n}\<close> \<open>is_path (i # xs)\<close> is_path_remove_cycle[of "i # as'"]
        by - (rule exI[where x = "as' @ a # cs'"], auto)
    qed
    then show ?thesis
      by (cases "n \<le> length ys") (auto intro: that less)
  qed
qed

lemma reaches_non_inf_path:
  assumes "reaches i" "i \<le> n" "t \<le> n"
  shows "OPT n i < \<infinity>"
proof (cases "t = i")
  case True
  with \<open>i \<le> n\<close> \<open>t \<le> n\<close> have "OPT n i \<le> 0"
    unfolding OPT_def
    by (auto intro: Min_le simp: finite_lists_length_le2[simplified])
  then show ?thesis
    using less_linear by (fastforce simp: zero_extended_def)
next
  case False
  from assms(1) obtain xs where "is_path (i # xs)" "i \<le> n" "set xs \<subseteq> {0..n}"
    unfolding reaches_def by safe
  then obtain xs where xs: "is_path (i # xs)" "i \<le> n" "set xs \<subseteq> {0..n}" "length xs < n"
    using \<open>t \<noteq> i\<close> \<open>t \<le> n\<close> by (auto intro: is_path_shorten)
  then have "weight (i # xs @ [t]) < \<infinity>"
    unfolding is_path_def by auto
  with xs(2-) show ?thesis
    unfolding OPT_def
    by (elim order.strict_trans1[rotated])
       (auto simp: setcompr_eq_image finite_lists_length_le2[simplified])
qed

lemma OPT_sink_le_0:
  "OPT i t \<le> 0"
  unfolding OPT_def by (auto simp: finite_lists_length_le2[simplified])

lemma is_path_appendD:
  assumes "is_path (as @ a # bs)"
  shows "is_path (a # bs)"
  using assms weight_append[of as a "bs @ [t]"] unfolding is_path_def
  by simp (metis Pinf_add_right add.commute less_extended_simps(4) not_less_iff_gr_or_eq)

lemma has_negative_cycleI:
  assumes "set (a # xs @ ys) \<subseteq> {0..n}" "weight (a # xs @ [a]) < 0" "is_path (a # ys)"
  shows has_negative_cycle
  using assms unfolding has_negative_cycle_def by auto

lemma OPT_cases2:
  obtains (path) xs where
    "v \<noteq> t" "OPT i v \<noteq> \<infinity>" "OPT i v = weight (v # xs @ [t])" "length xs + 1 \<le> i" "set xs \<subseteq> {0..n}"
  | (unreachable) "v \<noteq> t" "OPT i v = \<infinity>"
  | (sink) "v = t" "OPT i v \<le> 0"
  unfolding OPT_def
  using Min_in[of "{weight (v # xs @ [t]) |xs. length xs + 1 \<le> i \<and> set xs \<subseteq> {0..n}}
    \<union> {if t = v then 0 else \<infinity>}"]
  by (cases "v = t"; force simp: finite_lists_length_le2[simplified] split: if_split_asm)

lemma shortest_le_OPT:
  assumes "v \<le> n"
  shows "shortest v \<le> OPT i v"
  unfolding OPT_def shortest_def
  apply (subst Min_Inf)
    apply (simp add: setcompr_eq_image finite_lists_length_le2[simplified]; fail)+
  apply (rule Inf_superset_mono)
  apply auto
  done


context
  assumes W_wellformed: "\<forall>i \<le> n. \<forall>j \<le> n. W i j > -\<infinity>"
  assumes "t \<le> n"
begin

lemma weight_not_minfI:
  "-\<infinity> < weight xs" if "set xs \<subseteq> {0..n}" "xs \<noteq> []"
  using that using W_wellformed \<open>t \<le> n\<close>
  by (induction xs rule: induct_list012) (auto intro: add_gt_minfI simp: zero_extended_def)

lemma OPT_not_minfI:
  "OPT n i > -\<infinity>" if "i \<le> n"
proof -
  have "OPT n i \<in>
    {weight (i # xs @ [t]) |xs. length xs + 1 \<le> n \<and> set xs \<subseteq> {0..n}} \<union> {if t = i then 0 else \<infinity>}"
    unfolding OPT_def
    by (rule Min_in) (auto simp: setcompr_eq_image finite_lists_length_le2[simplified])
  with that \<open>t \<le> n\<close> show ?thesis
    by (auto 4 3 intro!: weight_not_minfI simp: zero_extended_def)
qed

theorem detects_cycle:
  assumes has_negative_cycle
  shows "\<exists>i \<le> n. OPT (n + 1) i < OPT n i"
proof -
  from assms \<open>t \<le> n\<close> obtain xs a ys where cycle:
    "a \<le> n" "set xs \<subseteq> {0..n}" "set ys \<subseteq> {0..n}"
    "weight (a # xs @ [a]) < 0" "is_path (a # ys)"
    unfolding has_negative_cycle_def by clarsimp
  then have "reaches a"
    unfolding reaches_def by auto
  have reaches: "reaches x" if "x \<in> set xs" for x
  proof -
    from that obtain as bs where "xs = as @ x # bs"
      by atomize_elim (rule split_list)
    with cycle have "weight (x # bs @ [a]) < \<infinity>"
      using weight_append[of "a # as" x "bs @ [a]"]
      by simp (metis Pinf_add_right Pinf_le add.commute less_eq_extended.simps(2) not_less)

    moreover from \<open>reaches a\<close> obtain cs where "local.weight (a # cs @ [t]) < \<infinity>" "set cs \<subseteq> {0..n}"
      unfolding reaches_def is_path_def by auto
    ultimately show ?thesis
      unfolding reaches_def is_path_def
      using \<open>a \<le> n\<close> weight_append[of "x # bs" a "cs @ [t]"] cycle(2) \<open>xs = _\<close>
      by - (rule exI[where x = "bs @ [a] @ cs"], auto intro: add_lt_infI)
  qed
  let ?S = "sum_list (map (OPT n) (a # xs @ [a]))"
  obtain u v where "u \<le> n" "v \<le> n" "OPT n v + W u v < OPT n u"
  proof (atomize_elim, rule ccontr)
    assume "\<nexists>u v. u \<le> n \<and> v \<le> n \<and> OPT n v + W u v < OPT n u"
    then have "?S \<le> ?S + weight (a # xs @ [a])"
      using cycle(1-3) by (subst fold_sum_aux; fastforce simp: subset_eq)
    moreover have "?S > -\<infinity>"
      using cycle(1-4) by (intro sum_list_not_minfI, auto intro!: OPT_not_minfI)
    moreover have "?S < \<infinity>"
      using reaches \<open>t \<le> n\<close> cycle(1,2)
      by (intro sum_list_not_infI) (auto intro: reaches_non_inf_path \<open>reaches a\<close> simp: subset_eq)
    ultimately have "weight (a # xs @ [a]) \<ge> 0"
      by (simp add: le_add_same_cancel1)
    with \<open>weight _ < 0\<close> show False
      by simp
  qed
  then show ?thesis
    by -
       (rule exI[where x = u],
        auto 4 4 intro: Min.coboundedI min.strict_coboundedI2 elim: order.strict_trans1[rotated]
          simp: OPT_Suc[OF \<open>t \<le> n\<close>])
qed

corollary bf_detects_cycle:
  assumes has_negative_cycle
  shows "\<exists>i \<le> n. bf (n + 1) i < bf n i"
  using detects_cycle[OF assms] unfolding bf_correct[OF \<open>t \<le> n\<close>] .

lemma shortest_cases:
  assumes "v \<le> n"
  obtains (path) xs where "shortest v = weight (v # xs @ [t])" "set xs \<subseteq> {0..n}"
  | (sink) "v = t" "shortest v = 0"
  | (unreachable) "v \<noteq> t" "shortest v = \<infinity>"
  | (negative_cycle) "shortest v = -\<infinity>" "\<forall>x. \<exists>xs. set xs \<subseteq> {0..n} \<and> weight (v # xs @ [t]) < Fin x"
proof -
  let ?S = "{weight (v # xs @ [t]) | xs. set xs \<subseteq> {0..n}} \<union> {if t = v then 0 else \<infinity>}"
  have "?S \<noteq> {}"
    by auto
  have Minf_lowest: False if  "-\<infinity> < a" "-\<infinity> = a" for a :: "int extended"
    using that by auto
  show ?thesis
  proof (cases "shortest v")
    case (Fin x)
    then have "-\<infinity> \<notin> ?S" "bdd_below (Fin -` ?S)" "?S \<noteq> {\<infinity>}" "x = Inf (Fin -` ?S)"
      unfolding shortest_def Inf_extended_def by (auto split: if_split_asm)
    from this(1-3) have "x \<in> Fin -` ?S"
      unfolding \<open>x = _\<close>
      by (intro Inf_int_in, auto simp: zero_extended_def)
        (smt empty_iff extended.exhaust insertI2 mem_Collect_eq vimage_eq)
    with \<open>shortest v = _\<close> show ?thesis
      unfolding vimage_eq by (auto split: if_split_asm intro: that)
  next
    case Pinf
    with \<open>?S \<noteq> {}\<close> have "t \<noteq> v"
      unfolding shortest_def Inf_extended_def by (auto split: if_split_asm)
    with \<open>_ = \<infinity>\<close> show ?thesis
      by (auto intro: that)
  next
    case Minf
    then have "?S \<noteq> {}" "?S \<noteq> {\<infinity>}" "-\<infinity> \<in> ?S \<or> \<not> bdd_below (Fin -` ?S)"
      unfolding shortest_def Inf_extended_def by (auto split: if_split_asm)
    from this(3) have "\<forall>x. \<exists>xs. set xs \<subseteq> {0..n} \<and> weight (v # xs @ [t]) < Fin x"
    proof
      assume "-\<infinity> \<in> ?S"
      with weight_not_minfI have False
        using \<open>v \<le> n\<close> \<open>t \<le> n\<close> by (auto split: if_split_asm elim: Minf_lowest[rotated])
      then show ?thesis ..
    next
      assume "\<not> bdd_below (Fin -` ?S)"
      show ?thesis
      proof
        fix x :: int
        let ?m = "min x (-1)"
        from \<open>\<not> bdd_below _\<close> obtain m where "Fin m \<in> ?S" "m < ?m"
          unfolding bdd_below_def by - (simp, drule spec[of _ "?m"], force)
        then show "\<exists>xs. set xs \<subseteq> {0..n} \<and> weight (v # xs @ [t]) < Fin x"
          by (auto split: if_split_asm simp: zero_extended_def) (metis less_extended_simps(1))+
      qed
    qed
    with \<open>shortest v = _\<close> show ?thesis
      by (auto intro: that)
  qed
qed

lemma simple_paths:
  assumes "\<not> has_negative_cycle" "weight (v # xs @ [t]) < \<infinity>" "set xs \<subseteq> {0..n}" "v \<le> n"
  obtains ys where
    "weight (v # ys @ [t]) \<le> weight (v # xs @ [t])" "set ys \<subseteq> {0..n}" "length ys < n" | "v = t"
  using assms(2-)
proof (atomize_elim, induction "length xs" arbitrary: xs rule: less_induct)
  case (less ys)
  note ys = less.prems(1,2)
  note IH = less.hyps
  have path: "is_path (v # ys)"
    using is_path_def not_less_iff_gr_or_eq ys(1) by fastforce
  show ?case
  proof (cases "length ys \<ge> n")
    case True
    with ys \<open>v \<le> n\<close> \<open>t \<le> n\<close> obtain a as bs cs where "v # ys @ [t] = as @ a # bs @ a # cs"
      by - (rule list_pidgeonhole[of "v # ys @ [t]" "{0..n}"], auto)
    then show ?thesis
    proof (cases rule: path_eq_cycleE)
      case Nil_Nil
      then show ?thesis
        by simp
    next
      case (Nil_Cons cs')
      then have *: "weight (v # ys @ [t]) = weight (a # bs @ [a]) + weight (a # cs' @ [t])"
        by (simp add: weight_append[of "a # bs" a "cs' @ [t]", simplified])
      show ?thesis
      proof (cases "weight (a # bs @ [a]) < 0")
        case True
        with Nil_Cons \<open>set ys \<subseteq> _\<close> path show ?thesis
          using assms(1) by (force intro: has_negative_cycleI[of a bs ys])
      next
        case False
        then have "weight (a # bs @ [a]) \<ge> 0"
          by auto
        with * ys have "weight (a # cs' @ [t]) \<le> weight (v # ys @ [t])"
          using add_mono not_le by fastforce
        with Nil_Cons \<open>length ys \<ge> n\<close> ys show ?thesis
          using IH[of cs'] by simp (meson le_less_trans order_trans)
      qed
    next
      case (Cons_Nil as')
      with ys have *: "weight (v # ys @ [t]) = weight (v # as' @ [t]) + weight (a # bs @ [a])"
        using weight_append[of "v # as'" t "bs @ [t]"] by simp
      show ?thesis
      proof (cases "weight (a # bs @ [a]) < 0")
        case True
        with Cons_Nil \<open>set ys \<subseteq> _\<close> path assms(1) show ?thesis
          using is_path_appendD[of "v # as'"] by (force intro: has_negative_cycleI[of a bs bs])
      next
        case False
        then have "weight (a # bs @ [a]) \<ge> 0"
          by auto
        with * ys(1) have "weight (v # as' @ [t]) \<le> weight (v # ys @ [t])"
          using add_left_mono by fastforce
        with Cons_Nil \<open>length ys \<ge> n\<close> \<open>v \<le> n\<close> ys show ?thesis
          using IH[of as'] by simp (meson le_less_trans order_trans)
      qed
    next
      case (Cons_Cons as' cs')
      with ys have *:
        "weight (v # ys @ [t]) = weight (v # as' @ a # cs' @ [t]) + weight (a # bs @ [a])"
        using
          weight_append[of "v # as'" a "bs @ a # cs' @ [t]"]
          weight_append[of "a # bs" a "cs' @ [t]"]
          weight_append[of "v # as'" a "cs' @ [t]"]
        by (simp add: algebra_simps)
      show ?thesis
      proof (cases "weight (a # bs @ [a]) < 0")
        case True
        with Cons_Cons \<open>set ys \<subseteq> _\<close> path assms(1) show ?thesis
          using is_path_appendD[of "v # as'"]
          by (force intro: has_negative_cycleI[of a bs "bs @ a # cs'"])
      next
        case False
        then have "weight (a # bs @ [a]) \<ge> 0"
          by auto
        with * ys have "weight (v # as' @ a # cs' @ [t]) \<le> weight (v # ys @ [t])"
          using add_left_mono by fastforce
        with Cons_Cons \<open>v \<le> n\<close> ys show ?thesis
          using is_path_remove_cycle2 IH[of "as' @ a # cs'"]
          by simp (meson le_less_trans order_trans)
      qed
    qed
  next
    case False
    with \<open>set ys \<subseteq> _\<close> show ?thesis
      by auto
  qed
qed

theorem shorter_than_OPT_n_has_negative_cycle:
  assumes "shortest v < OPT n v" "v \<le> n"
  shows has_negative_cycle
proof -
  from assms obtain ys where ys:
    "weight (v # ys @ [t]) < OPT n v" "set ys \<subseteq> {0..n}"
    apply (cases rule: OPT_cases2[of v n]; cases rule: shortest_cases[OF \<open>v \<le> n\<close>]; simp)
      apply (metis uminus_extended.cases)
    using less_extended_simps(2) less_trans apply blast
    apply (metis less_eq_extended.elims(2) less_extended_def zero_extended_def)
    done
  show ?thesis
  proof (cases "v = t")
    case True
    with ys \<open>t \<le> n\<close> show ?thesis
      using OPT_sink_le_0[of n] unfolding has_negative_cycle_def is_path_def
      using less_extended_def by force
  next
    case False
    show ?thesis
    proof (rule ccontr)
      assume "\<not> has_negative_cycle"
      with False False ys \<open>v \<le> n\<close> obtain xs where
        "weight (v # xs @ [t]) \<le> weight (v # ys @ [t])" "set xs \<subseteq> {0..n}" "length xs < n"
        using less_extended_def by (fastforce elim!: simple_paths[of v ys])
      then have "OPT n v \<le> weight (v # xs @ [t])"
        unfolding OPT_def by (intro Min_le) auto
      with \<open>_ \<le> weight (v # ys @ [t])\<close> \<open>weight (v # ys @ [t]) < OPT n v\<close> show False
        by simp
    qed
  qed
qed

corollary detects_cycle_has_negative_cycle:
  assumes "OPT (n + 1) v < OPT n v" "v \<le> n"
  shows has_negative_cycle
  using assms shortest_le_OPT[of v "n + 1"] shorter_than_OPT_n_has_negative_cycle[of v] by auto

corollary bellman_ford_detects_cycle:
  "has_negative_cycle \<longleftrightarrow> (\<exists>v \<le> n. OPT (n + 1) v < OPT n v)"
  using detects_cycle_has_negative_cycle detects_cycle by blast

corollary bellman_ford_shortest_paths:
  assumes "\<not> has_negative_cycle"
  shows "\<forall>v \<le> n. bf n v = shortest v"
proof -
  have "OPT n v \<le> shortest v" if "v \<le> n" for v
    using that assms shorter_than_OPT_n_has_negative_cycle[of v] by force
  then show ?thesis
    unfolding bf_correct[OF \<open>t \<le> n\<close>, symmetric]
    by (safe, rule order.antisym) (auto elim: shortest_le_OPT)
qed

lemma OPT_mono:
  "OPT m v \<le> OPT n v" if \<open>v \<le> n\<close> \<open>n \<le> m\<close>
  using that unfolding OPT_def by (intro Min_antimono) auto

corollary bf_fix:
  assumes "\<not> has_negative_cycle" "m \<ge> n"
  shows "\<forall>v \<le> n. bf m v = bf n v"
proof (intro allI impI)
  fix v assume "v \<le> n"
  from \<open>v \<le> n\<close> \<open>n \<le> m\<close> have "shortest v \<le> OPT m v"
    by (simp add: shortest_le_OPT)
  moreover from \<open>v \<le> n\<close> \<open>n \<le> m\<close> have "OPT m v \<le> OPT n v"
    by (rule OPT_mono)
  moreover from \<open>v \<le> n\<close> assms have "OPT n v \<le> shortest v"
    using shorter_than_OPT_n_has_negative_cycle[of v] by force
  ultimately show "bf m v = bf n v"
    unfolding bf_correct[OF \<open>t \<le> n\<close>, symmetric] by simp
qed

lemma bellman_ford_correct':
  "bf\<^sub>m.crel_vs (=) (if has_negative_cycle then None else Some (map shortest [0..<n+1])) bellman_ford"
proof -
  include state_monad_syntax app_syntax
  let ?l = "if has_negative_cycle then None else Some (map shortest [0..<n + 1])"
  let ?r = "(\<lambda>xs. (\<lambda>ys. (if xs = ys then Some xs else None))
    $ (map $ \<llangle>bf (n + 1)\<rrangle> $ \<llangle>[0..<n + 1]\<rrangle>)) $ (map $ \<llangle>bf n\<rrangle> $ \<llangle>[0..<n + 1]\<rrangle>)"
  note crel_bf\<^sub>m' = bf\<^sub>m.crel[unfolded bf\<^sub>m.consistentDP_def, THEN rel_funD,
      of "(m, x)" "(m, y)" for m x y, unfolded prod.case]
  have "?l = ?r"
    supply [simp del] = bf_simps
    supply [simp add] =
      bf_fix[rule_format, symmetric] bellman_ford_shortest_paths[rule_format, symmetric]
    unfolding Wrap_def App_def using bf_detects_cycle by (fastforce elim: nat_le_cases)
  \<comment> \<open>Slightly transform the goal, then apply parametric reasoning like usual.\<close>
  show ?thesis
    \<comment> \<open>Roughly \<close>
    unfolding bellman_ford_alt_def \<open>?l = ?r\<close> \<comment> \<open>Obtain parametric form.\<close>
    apply (rule bf\<^sub>m.crel_vs_bind_ignore[rotated]) \<comment> \<open>Drop bind.\<close>
     apply (rule bottom_up.consistent_crel_vs_iterate_state[OF bf\<^sub>m.crel, folded iter_bf_def])
    apply (subst Transfer.Rel_def[symmetric]) \<comment> \<open>Setup typical goal for automated reasoner.\<close>
    \<comment> \<open>We need to reason manually because we are not in the context where \<open>bf\<^sub>m\<close> was defined.\<close>
    \<comment> \<open>This is roughly what @{method "memoize_prover_match_step"}/\<open>Transform_Tactic.step_tac\<close> does.\<close>
    ML_prf \<open>val ctxt = @{context}\<close>
    apply (tactic \<open>Transform_Tactic.solve_relator_tac ctxt 1\<close>
          | rule HOL.refl
          | rule bf\<^sub>m.dp_match_rule
          | rule bf\<^sub>m.crel_vs_return_ext
          | (subst Rel_def, rule crel_bf\<^sub>m')
          | tactic \<open>Transform_Tactic.transfer_raw_tac ctxt 1\<close>)+
    done
qed

theorem bellman_ford_correct:
  "fst (run_state bellman_ford Mapping.empty) =
  (if has_negative_cycle then None else Some (map shortest [0..<n+1]))"
  using bf\<^sub>m.cmem_empty bellman_ford_correct'[unfolded bf\<^sub>m.crel_vs_def, rule_format, of Mapping.empty]
  unfolding bf\<^sub>m.crel_vs_def by auto

end (* Wellformedness *)

end (* Final Node *)

end (* Bellman Ford *)



subsubsection \<open>Extracting an Executable Constant for the Imperative Implementation\<close>

ground_function (prove_termination) bf\<^sub>h'_impl: bf\<^sub>h'.simps

lemma bf\<^sub>h'_impl_def:
  fixes n :: nat
  fixes mem :: "nat ref \<times> nat ref \<times> int extended option array ref \<times> int extended option array ref"
  assumes mem_is_init: "mem = result_of (init_state (n + 1) 1 0) Heap.empty"
  shows "bf\<^sub>h'_impl n w t mem = bf\<^sub>h' n w t mem"
proof -
  have "bf\<^sub>h'_impl n w t mem i j = bf\<^sub>h' n w t mem i j" for i j
    by (induction rule: bf\<^sub>h'.induct[OF mem_is_init];
        simp add: bf\<^sub>h'.simps[OF mem_is_init]; solve_cong simp
       )
  then show ?thesis
    by auto
qed

definition
  "iter_bf_heap n w t mem = iterator_defs.iter_heap
      (\<lambda>(x, y). x \<le> n \<and> y \<le> n)
      (\<lambda>(x, y). if y < n then (x, y + 1) else (x + 1, 0))
      (\<lambda>(x, y). bf\<^sub>h'_impl n w t mem x y)"

lemma iter_bf_heap_unfold[code]:
  "iter_bf_heap n w t mem = (\<lambda> (i, j).
    (if i \<le> n \<and> j \<le> n
     then do {
            bf\<^sub>h'_impl n w t mem i j;
            iter_bf_heap n w t mem (if j < n then (i, j + 1) else (i + 1, 0))
          }
     else Heap_Monad.return ()))"
  unfolding iter_bf_heap_def by (rule ext) (safe, simp add: iter_heap_unfold)

definition
  "bf_impl n w t i j = do {
    mem \<leftarrow> (init_state (n + 1) (1::nat) (0::nat) ::
      (nat ref \<times> nat ref \<times> int extended option array ref \<times> int extended option array ref) Heap);
    iter_bf_heap n w t mem (0, 0);
    bf\<^sub>h'_impl n w t mem i j
  }"

lemma bf_impl_correct:
  "bf n w t i j = result_of (bf_impl n w t i j) Heap.empty"
  using memoized_empty[OF HOL.refl, of n w t "(i, j)"]
  by (simp add:
        execute_bind_success[OF succes_init_state] bf_impl_def bf\<^sub>h'_impl_def iter_bf_heap_def
      )


subsubsection \<open>Test Cases\<close>

definition
  "G\<^sub>1_list = [[(1 :: nat,-6 :: int), (2,4), (3,5)], [(3,10)], [(3,2)], []]"

definition
  "G\<^sub>2_list = [[(1 :: nat,-6 :: int), (2,4), (3,5)], [(3,10)], [(3,2)], [(0, -5)]]"

definition
  "G\<^sub>3_list = [[(1 :: nat,-1 :: int), (2,2)], [(2,5), (3,4)], [(3,2), (4,3)], [(2,-2), (4,2)], []]"

definition
  "G\<^sub>4_list = [[(1 :: nat,-1 :: int), (2,2)], [(2,5), (3,4)], [(3,2), (4,3)], [(2,-3), (4,2)], []]"

definition
  "graph_of a i j = case_option \<infinity> (Fin o snd) (List.find (\<lambda> p. fst p = j) (a !! i))"

definition "test_bf = bf_impl 3 (graph_of (IArray G\<^sub>1_list)) 3 3 0"

code_reflect Test functions test_bf

text \<open>One can see a trace of the calls to the memory in the output\<close>
ML \<open>Test.test_bf ()\<close>

lemma bottom_up_alt[code]:
  "bf n W t i j =
     fst (run_state
      (iter_bf n W t (0, 0) \<bind> (\<lambda>_. bf\<^sub>m' n W t i j))
      Mapping.empty)"
  using bf_bottom_up by auto

definition
  "bf_ia n W t i j = (let W' = graph_of (IArray W) in
    fst (run_state
      (iter_bf n W' t (i, j) \<bind> (\<lambda>_. bf\<^sub>m' n W' t i j))
      Mapping.empty)
  )"

\<comment> \<open>Component tests.\<close>
lemma
  "fst (run_state (bf\<^sub>m' 3 (graph_of (IArray G\<^sub>1_list)) 3 3 0) Mapping.empty) = 4"
  "bf 3 (graph_of (IArray G\<^sub>1_list)) 3 3 0 = 4"
  by eval+

\<comment> \<open>Regular test cases.\<close>
lemma
  "fst (run_state (bellman_ford 3 (graph_of (IArray G\<^sub>1_list)) 3) Mapping.empty) = Some [4, 10, 2, 0]"
  "fst (run_state (bellman_ford 4 (graph_of (IArray G\<^sub>3_list)) 4) Mapping.empty) = Some [4, 5, 3, 1, 0]"
  by eval+

\<comment> \<open>Test detection of negative cycles.\<close>
lemma
  "fst (run_state (bellman_ford 3 (graph_of (IArray G\<^sub>2_list)) 3) Mapping.empty) = None"
  "fst (run_state (bellman_ford 4 (graph_of (IArray G\<^sub>4_list)) 4) Mapping.empty) = None"
  by eval+

end (* Theory *)