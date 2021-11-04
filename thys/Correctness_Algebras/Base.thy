(* Title:      Base
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Base\<close>

theory Base

imports Stone_Relation_Algebras.Semirings

begin

class while =
  fixes while :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<star>" 59)

class n =
  fixes n :: "'a \<Rightarrow> 'a"

class diamond =
  fixes diamond :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("| _ > _" [50,90] 95)

class box =
  fixes box :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("| _ ] _" [50,90] 95)

context ord
begin

definition ascending_chain :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool"
  where "ascending_chain f \<equiv> \<forall>n . f n \<le> f (Suc n)"

definition descending_chain :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool"
  where "descending_chain f \<equiv> \<forall>n . f (Suc n) \<le> f n"

definition directed :: "'a set \<Rightarrow> bool"
  where "directed X \<equiv> X \<noteq> {} \<and> (\<forall>x\<in>X . \<forall>y\<in>X . \<exists>z\<in>X . x \<le> z \<and> y \<le> z)"

definition co_directed :: "'a set \<Rightarrow> bool"
  where "co_directed X \<equiv> X \<noteq> {} \<and> (\<forall>x\<in>X . \<forall>y\<in>X . \<exists>z\<in>X . z \<le> x \<and> z \<le> y)"

definition chain :: "'a set \<Rightarrow> bool"
  where "chain X \<equiv> \<forall>x\<in>X . \<forall>y\<in>X . x \<le> y \<or> y \<le> x"

end

context order
begin

lemma ascending_chain_k:
  "ascending_chain f \<Longrightarrow> f m \<le> f (m + k)"
  apply (induct k)
  apply simp
  using le_add1 lift_Suc_mono_le ord.ascending_chain_def by blast

lemma ascending_chain_isotone:
  "ascending_chain f \<Longrightarrow> m \<le> k \<Longrightarrow> f m \<le> f k"
  using lift_Suc_mono_le ord.ascending_chain_def by blast

lemma ascending_chain_comparable:
  "ascending_chain f \<Longrightarrow> f k \<le> f m \<or> f m \<le> f k"
  by (meson ascending_chain_isotone linear)

lemma ascending_chain_chain:
  "ascending_chain f \<Longrightarrow> chain (range f)"
  by (simp add: ascending_chain_comparable chain_def)

lemma chain_directed:
  "X \<noteq> {} \<Longrightarrow> chain X \<Longrightarrow> directed X"
  by (metis chain_def directed_def)

lemma ascending_chain_directed:
  "ascending_chain f \<Longrightarrow> directed (range f)"
  by (simp add: ascending_chain_chain chain_directed)

lemma descending_chain_k:
  "descending_chain f \<Longrightarrow> f (m + k) \<le> f m"
  apply (induct k)
  apply simp
  using le_add1 lift_Suc_antimono_le ord.descending_chain_def by blast

lemma descending_chain_antitone:
  "descending_chain f \<Longrightarrow> m \<le> k \<Longrightarrow> f k \<le> f m"
  using descending_chain_def lift_Suc_antimono_le by blast

lemma descending_chain_comparable:
  "descending_chain f \<Longrightarrow> f k \<le> f m \<or> f m \<le> f k"
  by (meson descending_chain_antitone nat_le_linear)

lemma descending_chain_chain:
  "descending_chain f \<Longrightarrow> chain (range f)"
  by (simp add: descending_chain_comparable chain_def)

lemma chain_co_directed:
  "X \<noteq> {} \<Longrightarrow> chain X \<Longrightarrow> co_directed X"
  by (metis chain_def co_directed_def)

lemma descending_chain_codirected:
  "descending_chain f \<Longrightarrow> co_directed (range f)"
  by (simp add: chain_co_directed descending_chain_chain)

end

context semilattice_sup
begin

lemma ascending_chain_left_sup:
  "ascending_chain f \<Longrightarrow> ascending_chain (\<lambda>n . x \<squnion> f n)"
  using ascending_chain_def sup_right_isotone by blast

lemma ascending_chain_right_sup:
  "ascending_chain f \<Longrightarrow> ascending_chain (\<lambda>n . f n \<squnion> x)"
  using ascending_chain_def sup_left_isotone by auto

lemma descending_chain_left_add:
  "descending_chain f \<Longrightarrow> descending_chain (\<lambda>n . x \<squnion> f n)"
  using descending_chain_def sup_right_isotone by blast

lemma descending_chain_right_add:
  "descending_chain f \<Longrightarrow> descending_chain (\<lambda>n . f n \<squnion> x)"
  using descending_chain_def sup_left_isotone by auto

primrec pSum0 :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a"
  where "pSum0 f 0 = f 0"
      | "pSum0 f (Suc m) = pSum0 f m \<squnion> f m"

lemma pSum0_below:
 "\<forall>i . f i \<le> x \<Longrightarrow> pSum0 f m \<le> x"
  apply (induct m)
  by auto

end

context non_associative_left_semiring
begin

lemma ascending_chain_left_mult:
  "ascending_chain f \<Longrightarrow> ascending_chain (\<lambda>n . x * f n)"
  by (simp add: mult_right_isotone ord.ascending_chain_def)

lemma ascending_chain_right_mult:
  "ascending_chain f \<Longrightarrow> ascending_chain (\<lambda>n . f n * x)"
  by (simp add: mult_left_isotone ord.ascending_chain_def)

lemma descending_chain_left_mult:
  "descending_chain f \<Longrightarrow> descending_chain (\<lambda>n . x * f n)"
  by (simp add: descending_chain_def mult_right_isotone)

lemma descending_chain_right_mult:
  "descending_chain f \<Longrightarrow> descending_chain (\<lambda>n . f n * x)"
  by (simp add: descending_chain_def mult_left_isotone)

end

context complete_lattice
begin

lemma sup_Sup:
  "A \<noteq> {} \<Longrightarrow> sup x (Sup A) = Sup ((sup x) ` A)"
  apply (rule order.antisym)
  apply (meson ex_in_conv imageI SUP_upper2 Sup_mono sup.boundedI sup_left_divisibility sup_right_divisibility)
  by (meson SUP_least Sup_upper sup_right_isotone)

lemma sup_SUP:
  "Y \<noteq> {} \<Longrightarrow> sup x (SUP y\<in>Y . f y) = (SUP y\<in>Y. sup x (f y))"
  apply (subst sup_Sup)
  by (simp_all add: image_image)

lemma inf_Inf:
  "A \<noteq> {} \<Longrightarrow> inf x (Inf A) = Inf ((inf x) ` A)"
  apply (rule order.antisym)
  apply (meson INF_greatest Inf_lower inf.sup_right_isotone)
  by (simp add: INF_inf_const1)

lemma inf_INF:
  "Y \<noteq> {} \<Longrightarrow> inf x (INF y\<in>Y . f y) = (INF y\<in>Y. inf x (f y))"
  apply (subst inf_Inf)
  by (simp_all add: image_image)

lemma SUP_image_id[simp]:
  "(SUP x\<in>f`A . x) = (SUP x\<in>A . f x)"
  by simp

lemma INF_image_id[simp]:
  "(INF x\<in>f`A . x) = (INF x\<in>A . f x)"
  by simp

end

lemma image_Collect_2:
  "f ` { g x | x . P x } = { f (g x) | x . P x }"
  by auto

text \<open>The following instantiation and four lemmas are from Jose Divason Mallagaray.\<close>

instantiation "fun" :: (type, type) power
begin

definition one_fun :: "'a \<Rightarrow> 'a"
  where one_fun_def: "one_fun \<equiv> id"

definition times_fun :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)"
  where times_fun_def: "times_fun \<equiv> comp"

instance
  by intro_classes

end

lemma id_power:
  "id^m = id"
  apply (induct m)
  apply (simp add: one_fun_def)
  by (simp add: times_fun_def)

lemma power_zero_id:
  "f^0 = id"
  by (simp add: one_fun_def)

lemma power_succ_unfold:
  "f^Suc m = f \<circ> f^m"
  by (simp add: times_fun_def)

lemma power_succ_unfold_ext:
  "(f^Suc m) x = f ((f^m) x)"
  by (simp add: times_fun_def)

end

