section\<open>Values\<close>

text\<open>Our EFSM implementation can currently handle integers and strings. Here we define a sum type
which combines these. We also define an arithmetic in terms of values such that EFSMs do not need
to be strongly typed.\<close>

theory Value
imports Trilean
begin

text_raw\<open>\snip{valuetype}{1}{2}{%\<close>
datatype "value" = Num int | Str String.literal
text_raw\<open>}%endsnip\<close>

fun is_Num :: "value \<Rightarrow> bool" where
  "is_Num (Num _) = True" |
  "is_Num (Str _) = False"

text_raw\<open>\snip{maybeIntArith}{1}{2}{%\<close>
fun maybe_arith_int :: "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> value option \<Rightarrow> value option \<Rightarrow> value option" where
  "maybe_arith_int f (Some (Num x)) (Some (Num y)) = Some (Num (f x y))" |
  "maybe_arith_int _ _ _ = None"
text_raw\<open>}%endsnip\<close>

lemma maybe_arith_int_not_None:
  "maybe_arith_int f a b \<noteq> None = (\<exists>n n'. a = Some (Num n) \<and> b = Some (Num n'))"
  using maybe_arith_int.elims maybe_arith_int.simps(1) by blast

lemma maybe_arith_int_Some:
  "maybe_arith_int f a b = Some (Num x) = (\<exists>n n'. a = Some (Num n) \<and> b = Some (Num n') \<and> f n n' = x)"
  using maybe_arith_int.elims maybe_arith_int.simps(1) by blast

lemma maybe_arith_int_None:
  "(maybe_arith_int f a1 a2 = None) = (\<nexists>n n'. a1 = Some (Num n) \<and> a2 = Some (Num n'))"
  using maybe_arith_int_not_None by blast

lemma maybe_arith_int_Not_Num:
  "(\<forall>n. maybe_arith_int f a1 a2 \<noteq> Some (Num n)) = (maybe_arith_int f a1 a2 = None)"
  by (metis maybe_arith_int.elims option.distinct(1))

lemma maybe_arith_int_never_string: "maybe_arith_int f a b \<noteq> Some (Str x)"
  using maybe_arith_int.elims by blast

definition "value_plus = maybe_arith_int (+)"

lemma value_plus_never_string: "value_plus a b \<noteq> Some (Str x)"
  by (simp add: value_plus_def maybe_arith_int_never_string)

lemma value_plus_symmetry: "value_plus x y = value_plus y x"
  apply (induct x y rule: maybe_arith_int.induct)
  by (simp_all add: value_plus_def)

definition "value_minus = maybe_arith_int (-)"

lemma value_minus_never_string: "value_minus a b \<noteq> Some (Str x)"
  by (simp add: maybe_arith_int_never_string value_minus_def)

definition "value_times = maybe_arith_int (*)"

lemma value_times_never_string: "value_times a b \<noteq> Some (Str x)"
  by (simp add: maybe_arith_int_never_string value_times_def)

fun MaybeBoolInt :: "(int \<Rightarrow> int \<Rightarrow> bool) \<Rightarrow> value option \<Rightarrow> value option \<Rightarrow> trilean" where
  "MaybeBoolInt f (Some (Num a)) (Some (Num b)) = (if f a b then true else false)" |
  "MaybeBoolInt _ _ _ = invalid"

lemma MaybeBoolInt_not_num_1:
  "\<forall>n. r \<noteq> Some (Num n) \<Longrightarrow> MaybeBoolInt f n r = invalid"
  using MaybeBoolInt.elims by blast

definition value_gt :: "value option \<Rightarrow> value option \<Rightarrow> trilean"  where
  "value_gt a b \<equiv> MaybeBoolInt (>) a b"

fun value_eq :: "value option \<Rightarrow> value option \<Rightarrow> trilean" where
  "value_eq None _ = invalid" |
  "value_eq _ None = invalid" |
  "value_eq (Some a) (Some b) = (if a = b then true else false)"

lemma value_eq_true: "(value_eq a b = true) = (\<exists>x y. a = Some x \<and> b = Some y \<and> x = y)"
  by (cases a; cases b, auto)

lemma value_eq_false: "(value_eq a b = false) = (\<exists>x y. a = Some x \<and> b = Some y \<and> x \<noteq> y)"
  by (cases a; cases b, auto)

lemma value_gt_true_Some: "value_gt a b = true \<Longrightarrow> (\<exists>x. a = Some x) \<and> (\<exists>y. b = Some y)"
  by (cases a; cases b, auto simp: value_gt_def)

lemma value_gt_true: "(value_gt a b = true) = (\<exists>x y. a = Some (Num x) \<and> b = Some (Num y) \<and> x > y)"
  apply (cases a)
  using value_gt_true_Some apply blast
  apply (cases b)
  using value_gt_true_Some apply blast
  subgoal for aa bb by (cases aa; cases bb, auto simp: value_gt_def)
  done

lemma value_gt_false_Some: "value_gt a b = false \<Longrightarrow> (\<exists>x. a = Some x) \<and> (\<exists>y. b = Some y)"
  by (cases a; cases b, auto simp: value_gt_def)

end
