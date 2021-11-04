(* Title:      Lattice-Ordered Semirings
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Lattice-Ordered Semirings\<close>

theory Lattice_Ordered_Semirings

imports Stone_Relation_Algebras.Semirings

begin

text \<open>Many results in this theory are taken from a joint paper with Rudolf Berghammer.\<close>

text \<open>M0-algebra\<close>

class lattice_ordered_pre_left_semiring = pre_left_semiring + bounded_distrib_lattice
begin

subclass bounded_pre_left_semiring
  apply unfold_locales
  by simp

lemma top_mult_right_one:
  "x * top = x * top * 1"
  by (metis order.antisym mult_sub_right_one mult_sup_associative_one surjective_one_closed)

lemma mult_left_sub_dist_inf_left:
  "x * (y \<sqinter> z) \<le> x * y"
  by (simp add: mult_right_isotone)

lemma mult_left_sub_dist_inf_right:
  "x * (y \<sqinter> z) \<le> x * z"
  by (simp add: mult_right_isotone)

lemma mult_right_sub_dist_inf_left:
  "(x \<sqinter> y) * z \<le> x * z"
  by (simp add: mult_left_isotone)

lemma mult_right_sub_dist_inf_right:
  "(x \<sqinter> y) * z \<le> y * z"
  by (simp add: mult_left_isotone)

lemma mult_right_sub_dist_inf:
  "(x \<sqinter> y) * z \<le> x * z \<sqinter> y * z"
  by (simp add: mult_right_sub_dist_inf_left mult_right_sub_dist_inf_right)

text \<open>Figure 1: fundamental properties\<close>

definition co_total          :: "'a \<Rightarrow> bool" where "co_total x \<equiv> x * bot = bot"
definition up_closed         :: "'a \<Rightarrow> bool" where "up_closed x \<equiv> x * 1 = x"
definition sup_distributive  :: "'a \<Rightarrow> bool" where "sup_distributive x \<equiv> (\<forall>y z . x * (y \<squnion> z) = x * y \<squnion> x * z)"
definition inf_distributive  :: "'a \<Rightarrow> bool" where "inf_distributive x \<equiv> (\<forall>y z . x * (y \<sqinter> z) = x * y \<sqinter> x * z)"
definition contact           :: "'a \<Rightarrow> bool" where "contact x \<equiv> x * x \<squnion> 1 = x"
definition kernel            :: "'a \<Rightarrow> bool" where "kernel x \<equiv> x * x \<sqinter> 1 = x * 1"
definition sup_dist_contact  :: "'a \<Rightarrow> bool" where "sup_dist_contact x \<equiv> sup_distributive x \<and> contact x"
definition inf_dist_kernel   :: "'a \<Rightarrow> bool" where "inf_dist_kernel x \<equiv> inf_distributive x \<and> kernel x"
definition test              :: "'a \<Rightarrow> bool" where "test x \<equiv> x * top \<sqinter> 1 = x"
definition co_test           :: "'a \<Rightarrow> bool" where "co_test x \<equiv> x * bot \<squnion> 1 = x"
definition co_vector         :: "'a \<Rightarrow> bool" where "co_vector x \<equiv> x * bot = x"

text \<open>AAMP Theorem 6 / Figure 2: relations between properties\<close>

lemma reflexive_total:
  "reflexive x \<Longrightarrow> total x"
  using sup_left_divisibility total_sup_closed by force

lemma reflexive_dense:
  "reflexive x \<Longrightarrow> dense_rel x"
  using mult_left_isotone by fastforce

lemma reflexive_transitive_up_closed:
  "reflexive x \<Longrightarrow> transitive x \<Longrightarrow> up_closed x"
  by (metis antisym_conv mult_isotone mult_sub_right_one reflexive_dense up_closed_def)

lemma coreflexive_co_total:
  "coreflexive x \<Longrightarrow> co_total x"
  by (metis co_total_def order.eq_iff mult_left_isotone mult_left_one bot_least)

lemma coreflexive_transitive:
  "coreflexive x \<Longrightarrow> transitive x"
  by (simp add: coreflexive_transitive)

lemma idempotent_transitive_dense:
  "idempotent x \<longleftrightarrow> transitive x \<and> dense_rel x"
  by (simp add: order.eq_iff)

lemma contact_reflexive:
  "contact x \<Longrightarrow> reflexive x"
  using contact_def sup_right_divisibility by auto

lemma contact_transitive:
  "contact x \<Longrightarrow> transitive x"
  using contact_def sup_left_divisibility by blast

lemma contact_dense:
  "contact x \<Longrightarrow> dense_rel x"
  by (simp add: contact_reflexive reflexive_dense)

lemma contact_idempotent:
  "contact x \<Longrightarrow> idempotent x"
  by (simp add: contact_dense contact_transitive idempotent_transitive_dense)

lemma contact_up_closed:
  "contact x \<Longrightarrow> up_closed x"
  by (simp add: contact_reflexive contact_transitive reflexive_transitive_up_closed)

lemma contact_reflexive_idempotent_up_closed:
  "contact x \<longleftrightarrow> reflexive x \<and> idempotent x \<and> up_closed x"
  by (metis contact_def contact_idempotent contact_reflexive contact_up_closed sup_absorb2 sup_monoid.add_commute)

lemma kernel_coreflexive:
  "kernel x \<Longrightarrow> coreflexive x"
  by (metis kernel_def inf.boundedE mult_sub_right_one)

lemma kernel_transitive:
  "kernel x \<Longrightarrow> transitive x"
  by (simp add: coreflexive_transitive kernel_coreflexive)

lemma kernel_dense:
  "kernel x \<Longrightarrow> dense_rel x"
  by (metis kernel_def inf.boundedE mult_sub_right_one)

lemma kernel_idempotent:
  "kernel x \<Longrightarrow> idempotent x"
  by (simp add: idempotent_transitive_dense kernel_dense kernel_transitive)

lemma kernel_up_closed:
  "kernel x \<Longrightarrow> up_closed x"
  by (metis kernel_coreflexive kernel_def kernel_idempotent inf.absorb1 up_closed_def)

lemma kernel_coreflexive_idempotent_up_closed:
  "kernel x \<longleftrightarrow> coreflexive x \<and> idempotent x \<and> up_closed x"
  by (metis kernel_coreflexive kernel_def kernel_idempotent inf.absorb1 up_closed_def)

lemma test_coreflexive:
  "test x \<Longrightarrow> coreflexive x"
  using inf.sup_right_divisibility test_def by blast

lemma test_up_closed:
  "test x \<Longrightarrow> up_closed x"
  by (metis order.eq_iff mult_left_one mult_sub_right_one mult_right_sub_dist_inf test_def top_mult_right_one up_closed_def)

lemma co_test_reflexive:
  "co_test x \<Longrightarrow> reflexive x"
  using co_test_def sup_right_divisibility by blast

lemma co_test_transitive:
  "co_test x \<Longrightarrow> transitive x"
  by (smt co_test_def sup_assoc le_iff_sup mult_left_one mult_left_zero mult_right_dist_sup mult_semi_associative)

lemma co_test_idempotent:
  "co_test x \<Longrightarrow> idempotent x"
  by (simp add: co_test_reflexive co_test_transitive idempotent_transitive_dense reflexive_dense)

lemma co_test_up_closed:
  "co_test x \<Longrightarrow> up_closed x"
  by (simp add: co_test_reflexive co_test_transitive reflexive_transitive_up_closed)

lemma co_test_contact:
  "co_test x \<Longrightarrow> contact x"
  by (simp add: co_test_idempotent co_test_reflexive co_test_up_closed contact_reflexive_idempotent_up_closed)

lemma vector_transitive:
  "vector x \<Longrightarrow> transitive x"
  by (metis mult_right_isotone top.extremum)

lemma vector_up_closed:
  "vector x \<Longrightarrow> up_closed x"
  by (metis top_mult_right_one up_closed_def)

text \<open>AAMP Theorem 10 / Figure 3: closure properties\<close>

text \<open>total\<close>

lemma one_total:
  "total 1"
  by simp

lemma top_total:
  "total top"
  by simp

lemma sup_total:
  "total x \<Longrightarrow> total y \<Longrightarrow> total (x \<squnion> y)"
  by (simp add: total_sup_closed)

text \<open>co-total\<close>

lemma zero_co_total:
  "co_total bot"
  by (simp add: co_total_def)

lemma one_co_total:
  "co_total 1"
  by (simp add: co_total_def)

lemma sup_co_total:
  "co_total x \<Longrightarrow> co_total y \<Longrightarrow> co_total (x \<squnion> y)"
  by (simp add: co_total_def mult_right_dist_sup)

lemma inf_co_total:
  "co_total x \<Longrightarrow> co_total y \<Longrightarrow> co_total (x \<sqinter> y)"
  by (metis co_total_def order.antisym bot_least mult_right_sub_dist_inf_right)

lemma comp_co_total:
  "co_total x \<Longrightarrow> co_total y \<Longrightarrow> co_total (x * y)"
  by (metis co_total_def order.eq_iff mult_semi_associative bot_least)

text \<open>sub-transitive\<close>

lemma zero_transitive:
  "transitive bot"
  by (simp add: vector_transitive)

lemma one_transitive:
  "transitive 1"
  by simp

lemma top_transitive:
  "transitive top"
  by simp

lemma inf_transitive:
  "transitive x \<Longrightarrow> transitive y \<Longrightarrow> transitive (x \<sqinter> y)"
  by (meson inf_mono order_trans mult_left_sub_dist_inf_left mult_left_sub_dist_inf_right mult_right_sub_dist_inf)

text \<open>dense\<close>

lemma zero_dense:
  "dense_rel bot"
  by simp

lemma one_dense:
  "dense_rel 1"
  by simp

lemma top_dense:
  "dense_rel top"
  by simp

lemma sup_dense:
  assumes "dense_rel x"
      and "dense_rel y"
    shows "dense_rel (x \<squnion> y)"
proof -
  have "x \<le> x * x \<and> y \<le> y * y"
    using assms by auto
  hence "x \<le> (x \<squnion> y) * (x \<squnion> y) \<and> y \<le> (x \<squnion> y) * (x \<squnion> y)"
    by (meson dense_sup_closed order_trans sup.cobounded1 sup.cobounded2)
  hence "x \<squnion> y \<le> (x \<squnion> y) * (x \<squnion> y)"
    by simp
  thus "dense_rel (x \<squnion> y)"
    by simp
qed

text \<open>reflexive\<close>

lemma one_reflexive:
  "reflexive 1"
  by simp

lemma top_reflexive:
  "reflexive top"
  by simp

lemma sup_reflexive:
  "reflexive x \<Longrightarrow> reflexive y \<Longrightarrow> reflexive (x \<squnion> y)"
  by (simp add: reflexive_sup_closed)

lemma inf_reflexive:
  "reflexive x \<Longrightarrow> reflexive y \<Longrightarrow> reflexive (x \<sqinter> y)"
  by simp

lemma comp_reflexive:
  "reflexive x \<Longrightarrow> reflexive y \<Longrightarrow> reflexive (x * y)"
  using reflexive_mult_closed by auto

text \<open>co-reflexive\<close>

lemma zero_coreflexive:
  "coreflexive bot"
  by simp

lemma one_coreflexive:
  "coreflexive 1"
  by simp

lemma sup_coreflexive:
  "coreflexive x \<Longrightarrow> coreflexive y \<Longrightarrow> coreflexive (x \<squnion> y)"
  by simp

lemma inf_coreflexive:
  "coreflexive x \<Longrightarrow> coreflexive y \<Longrightarrow> coreflexive (x \<sqinter> y)"
  by (simp add: le_infI1)

lemma comp_coreflexive:
  "coreflexive x \<Longrightarrow> coreflexive y \<Longrightarrow> coreflexive (x * y)"
  by (simp add: coreflexive_mult_closed)

text \<open>idempotent\<close>

lemma zero_idempotent:
  "idempotent bot"
  by simp

lemma one_idempotent:
  "idempotent 1"
  by simp

lemma top_idempotent:
  "idempotent top"
  by simp

text \<open>up-closed\<close>

lemma zero_up_closed:
  "up_closed bot"
  by (simp add: up_closed_def)

lemma one_up_closed:
  "up_closed 1"
  by (simp add: up_closed_def)

lemma top_up_closed:
  "up_closed top"
  by (simp add: vector_up_closed)

lemma sup_up_closed:
  "up_closed x \<Longrightarrow> up_closed y \<Longrightarrow> up_closed (x \<squnion> y)"
  by (simp add: mult_right_dist_sup up_closed_def)

lemma inf_up_closed:
  "up_closed x \<Longrightarrow> up_closed y \<Longrightarrow> up_closed (x \<sqinter> y)"
  by (metis order.antisym mult_sub_right_one mult_right_sub_dist_inf up_closed_def)

lemma comp_up_closed:
  "up_closed x \<Longrightarrow> up_closed y \<Longrightarrow> up_closed (x * y)"
  by (metis order.antisym mult_semi_associative mult_sub_right_one up_closed_def)

text \<open>add-distributive\<close>

lemma zero_sup_distributive:
  "sup_distributive bot"
  by (simp add: sup_distributive_def)

lemma one_sup_distributive:
  "sup_distributive 1"
  by (simp add: sup_distributive_def)

lemma sup_sup_distributive:
  "sup_distributive x \<Longrightarrow> sup_distributive y \<Longrightarrow> sup_distributive (x \<squnion> y)"
  using sup_distributive_def mult_right_dist_sup sup_monoid.add_assoc sup_monoid.add_commute by auto

text \<open>inf-distributive\<close>

lemma zero_inf_distributive:
  "inf_distributive bot"
  by (simp add: inf_distributive_def)

lemma one_inf_distributive:
  "inf_distributive 1"
  by (simp add: inf_distributive_def)

text \<open>contact\<close>

lemma one_contact:
  "contact 1"
  by (simp add: contact_def)

lemma top_contact:
  "contact top"
  by (simp add: contact_def)

lemma inf_contact:
  "contact x \<Longrightarrow> contact y \<Longrightarrow> contact (x \<sqinter> y)"
  by (meson contact_reflexive_idempotent_up_closed contact_transitive inf_reflexive inf_transitive inf_up_closed preorder_idempotent)

text \<open>kernel\<close>

lemma zero_kernel:
  "kernel bot"
  by (simp add: kernel_def)

lemma one_kernel:
  "kernel 1"
  by (simp add: kernel_def)

lemma sup_kernel:
  "kernel x \<Longrightarrow> kernel y \<Longrightarrow> kernel (x \<squnion> y)"
  using kernel_coreflexive_idempotent_up_closed order.antisym coreflexive_transitive sup_dense sup_up_closed by force

text \<open>add-distributive contact\<close>

lemma one_sup_dist_contact:
  "sup_dist_contact 1"
  by (simp add: sup_dist_contact_def one_sup_distributive one_contact)

text \<open>inf-distributive kernel\<close>

lemma zero_inf_dist_kernel:
  "inf_dist_kernel bot"
  by (simp add: inf_dist_kernel_def zero_kernel zero_inf_distributive)

lemma one_inf_dist_kernel:
  "inf_dist_kernel 1"
  by (simp add: inf_dist_kernel_def one_kernel one_inf_distributive)

text \<open>test\<close>

lemma zero_test:
  "test bot"
  by (simp add: test_def)

lemma one_test:
  "test 1"
  by (simp add: test_def)

lemma sup_test:
  "test x \<Longrightarrow> test y \<Longrightarrow> test (x \<squnion> y)"
  by (simp add: inf_sup_distrib2 mult_right_dist_sup test_def)

lemma inf_test:
  "test x \<Longrightarrow> test y \<Longrightarrow> test (x \<sqinter> y)"
  by (smt (z3) inf.left_commute idempotent_one_closed inf.le_iff_sup inf_top.right_neutral mult_right_isotone mult_sub_right_one mult_right_sub_dist_inf test_def top_mult_right_one)

text \<open>co-test\<close>

lemma one_co_test:
  "co_test 1"
  by (simp add: co_test_def)

lemma sup_co_test:
  "co_test x \<Longrightarrow> co_test y \<Longrightarrow> co_test (x \<squnion> y)"
  by (smt (z3) co_test_def mult_right_dist_sup sup.left_idem sup_assoc sup_commute)

text \<open>vector\<close>

lemma zero_vector:
  "vector bot"
  by simp

lemma top_vector:
  "vector top"
  by simp

lemma sup_vector:
  "vector x \<Longrightarrow> vector y \<Longrightarrow> vector (x \<squnion> y)"
  by (simp add: vector_sup_closed)

lemma inf_vector:
  "vector x \<Longrightarrow> vector y \<Longrightarrow> vector (x \<sqinter> y)"
  by (metis order.antisym top_right_mult_increasing mult_right_sub_dist_inf)

lemma comp_vector:
  "vector y \<Longrightarrow> vector (x * y)"
  by (simp add: vector_mult_closed)

end

class lattice_ordered_pre_left_semiring_1 = non_associative_left_semiring + bounded_distrib_lattice +
  assumes mult_associative_one: "x * (y * z) = (x * (y * 1)) * z"
  assumes mult_right_dist_inf_one: "(x * 1 \<sqinter> y * 1) * z = x * z \<sqinter> y * z"
begin

subclass pre_left_semiring
  apply unfold_locales
  by (metis mult_associative_one mult_left_isotone mult_right_isotone mult_sub_right_one)

subclass lattice_ordered_pre_left_semiring ..

lemma mult_zero_associative:
  "x * bot * y = x * bot"
  by (metis mult_associative_one mult_left_zero)

lemma mult_zero_sup_one_dist:
  "(x * bot \<squnion> 1) * z = x * bot \<squnion> z"
  by (simp add: mult_right_dist_sup mult_zero_associative)

lemma mult_zero_sup_dist:
  "(x * bot \<squnion> y) * z = x * bot \<squnion> y * z"
  by (simp add: mult_right_dist_sup mult_zero_associative)

lemma vector_zero_inf_one_comp:
  "(x * bot \<sqinter> 1) * y = x * bot \<sqinter> y"
  by (metis mult_left_one mult_right_dist_inf_one mult_zero_associative)

text \<open>AAMP Theorem 6 / Figure 2: relations between properties\<close>

lemma co_test_inf_distributive:
  "co_test x \<Longrightarrow> inf_distributive x"
  by (metis co_test_def distrib_imp1 inf_sup_distrib1 inf_distributive_def mult_zero_sup_one_dist)

lemma co_test_sup_distributive:
  "co_test x \<Longrightarrow> sup_distributive x"
  by (metis sup_sup_distributive sup_distributive_def co_test_def one_sup_distributive sup.idem mult_zero_associative)

lemma co_test_sup_dist_contact:
  "co_test x \<Longrightarrow> sup_dist_contact x"
  by (simp add: co_test_sup_distributive sup_dist_contact_def co_test_contact)

text \<open>AAMP Theorem 10 / Figure 3: closure properties\<close>

text \<open>co-test\<close>

lemma inf_co_test:
  "co_test x \<Longrightarrow> co_test y \<Longrightarrow> co_test (x \<sqinter> y)"
  by (smt (z3) co_test_def co_test_up_closed mult_right_dist_inf_one sup_commute sup_inf_distrib1 up_closed_def)

lemma comp_co_test:
  "co_test x \<Longrightarrow> co_test y \<Longrightarrow> co_test (x * y)"
  by (metis co_test_def mult_associative_one sup_assoc mult_zero_sup_one_dist)

end

class lattice_ordered_pre_left_semiring_2 = lattice_ordered_pre_left_semiring +
  assumes mult_sub_associative_one: "x * (y * z) \<le> (x * (y * 1)) * z"
  assumes mult_right_dist_inf_one_sub: "x * z \<sqinter> y * z \<le> (x * 1 \<sqinter> y * 1) * z"
begin

subclass lattice_ordered_pre_left_semiring_1
  apply unfold_locales
  apply (simp add: order.antisym mult_sub_associative_one mult_sup_associative_one)
  by (metis order.eq_iff mult_one_associative mult_right_dist_inf_one_sub mult_right_sub_dist_inf)

end

class multirelation_algebra_1 = lattice_ordered_pre_left_semiring +
  assumes mult_left_top: "top * x = top"
begin

text \<open>AAMP Theorem 10 / Figure 3: closure properties\<close>

lemma top_sup_distributive:
  "sup_distributive top"
  by (simp add: sup_distributive_def mult_left_top)

lemma top_inf_distributive:
  "inf_distributive top"
  by (simp add: inf_distributive_def mult_left_top)

lemma top_sup_dist_contact:
  "sup_dist_contact top"
  by (simp add: sup_dist_contact_def top_contact top_sup_distributive)

lemma top_co_test:
  "co_test top"
  by (simp add: co_test_def mult_left_top)

end

text \<open>M1-algebra\<close>

class multirelation_algebra_2 = multirelation_algebra_1 + lattice_ordered_pre_left_semiring_2
begin

lemma mult_top_associative:
  "x * top * y = x * top"
  by (metis mult_left_top mult_associative_one)

lemma vector_inf_one_comp:
  "(x * top \<sqinter> 1) * y = x * top \<sqinter> y"
  by (metis vector_zero_inf_one_comp mult_top_associative)

lemma vector_left_annihilator:
  "vector x \<Longrightarrow> x * y = x"
  by (metis mult_top_associative)

text \<open>properties\<close>

lemma test_comp_inf:
  "test x \<Longrightarrow> test y \<Longrightarrow> x * y = x \<sqinter> y"
  by (metis inf.absorb1 inf.left_commute test_coreflexive test_def vector_inf_one_comp)

text \<open>AAMP Theorem 6 / Figure 2: relations between properties\<close>

lemma test_sup_distributive:
  "test x \<Longrightarrow> sup_distributive x"
  by (metis sup_distributive_def inf_sup_distrib1 test_def vector_inf_one_comp)

lemma test_inf_distributive:
  "test x \<Longrightarrow> inf_distributive x"
  by (smt (verit, ccfv_SIG) inf.commute inf.sup_monoid.add_assoc inf_distributive_def test_def inf.idem vector_inf_one_comp)

lemma test_inf_dist_kernel:
  "test x \<Longrightarrow> inf_dist_kernel x"
  by (simp add: kernel_def inf_dist_kernel_def one_test test_comp_inf test_inf_distributive)

lemma vector_idempotent:
  "vector x \<Longrightarrow> idempotent x"
  using vector_left_annihilator by blast

lemma vector_sup_distributive:
  "vector x \<Longrightarrow> sup_distributive x"
  by (simp add: sup_distributive_def vector_left_annihilator)

lemma vector_inf_distributive:
  "vector x \<Longrightarrow> inf_distributive x"
  by (simp add: inf_distributive_def vector_left_annihilator)

lemma vector_co_vector:
  "vector x \<longleftrightarrow> co_vector x"
  by (metis co_vector_def mult_zero_associative mult_top_associative)

text \<open>AAMP Theorem 10 / Figure 3: closure properties\<close>

text \<open>test\<close>

lemma comp_test:
  "test x \<Longrightarrow> test y \<Longrightarrow> test (x * y)"
  by (simp add: inf_test test_comp_inf)

end

class dual =
  fixes dual :: "'a \<Rightarrow> 'a" ("_\<^sup>d" [100] 100)

class multirelation_algebra_3 = lattice_ordered_pre_left_semiring + dual +
  assumes dual_involutive: "x\<^sup>d\<^sup>d = x"
  assumes dual_dist_sup: "(x \<squnion> y)\<^sup>d = x\<^sup>d \<sqinter> y\<^sup>d"
  assumes dual_one: "1\<^sup>d = 1"
begin

lemma dual_dist_inf:
  "(x \<sqinter> y)\<^sup>d = x\<^sup>d \<squnion> y\<^sup>d"
  by (metis dual_dist_sup dual_involutive)

lemma dual_antitone:
  "x \<le> y \<Longrightarrow> y\<^sup>d \<le> x\<^sup>d"
  using dual_dist_sup sup_right_divisibility by fastforce

lemma dual_zero:
  "bot\<^sup>d = top"
  by (metis dual_antitone bot_least dual_involutive top_le)

lemma dual_top:
  "top\<^sup>d = bot"
  using dual_zero dual_involutive by auto

text \<open>AAMP Theorem 10 / Figure 3: closure properties\<close>

lemma reflexive_coreflexive_dual:
  "reflexive x \<longleftrightarrow> coreflexive (x\<^sup>d)"
  using dual_antitone dual_involutive dual_one by fastforce

end

class multirelation_algebra_4 = multirelation_algebra_3 +
  assumes dual_sub_dist_comp: "(x * y)\<^sup>d \<le> x\<^sup>d * y\<^sup>d"
begin

subclass multirelation_algebra_1
  apply unfold_locales
  by (metis order.antisym top.extremum dual_zero dual_sub_dist_comp dual_involutive mult_left_zero)

lemma dual_sub_dist_comp_one:
  "(x * y)\<^sup>d \<le> (x * 1)\<^sup>d * y\<^sup>d"
  by (metis dual_sub_dist_comp mult_one_associative)

text \<open>AAMP Theorem 10 / Figure 3: closure properties\<close>

lemma co_total_total_dual:
  "co_total x \<Longrightarrow> total (x\<^sup>d)"
  by (metis co_total_def dual_sub_dist_comp dual_zero top_le)

lemma transitive_dense_dual:
  "transitive x \<Longrightarrow> dense_rel (x\<^sup>d)"
  using dual_antitone dual_sub_dist_comp inf.order_lesseq_imp by blast

end

text \<open>M2-algebra\<close>

class multirelation_algebra_5 = multirelation_algebra_3 +
  assumes dual_dist_comp_one: "(x * y)\<^sup>d = (x * 1)\<^sup>d * y\<^sup>d"
begin

subclass multirelation_algebra_4
  apply unfold_locales
  by (metis dual_antitone mult_sub_right_one mult_left_isotone dual_dist_comp_one)

lemma strong_up_closed:
  "x * 1 \<le> x \<Longrightarrow> x\<^sup>d * y\<^sup>d \<le> (x * y)\<^sup>d"
  by (simp add: dual_dist_comp_one antisym_conv mult_sub_right_one)

lemma strong_up_closed_2:
  "up_closed x \<Longrightarrow> (x * y)\<^sup>d = x\<^sup>d * y\<^sup>d"
  by (simp add: dual_dist_comp_one up_closed_def)

subclass lattice_ordered_pre_left_semiring_2
  apply unfold_locales
  apply (smt comp_up_closed dual_antitone dual_dist_comp_one dual_involutive dual_one mult_left_one mult_one_associative mult_semi_associative up_closed_def strong_up_closed_2)
  by (smt dual_dist_comp_one dual_dist_inf dual_involutive eq_refl mult_one_associative mult_right_dist_sup)

text \<open>AAMP Theorem 8\<close>

subclass multirelation_algebra_2 ..

text \<open>AAMP Theorem 10 / Figure 3: closure properties\<close>

text \<open>up-closed\<close>

lemma dual_up_closed:
  "up_closed x \<longleftrightarrow> up_closed (x\<^sup>d)"
  by (metis dual_involutive dual_one up_closed_def strong_up_closed_2)

text \<open>contact\<close>

lemma contact_kernel_dual:
  "contact x \<longleftrightarrow> kernel (x\<^sup>d)"
  by (metis contact_def contact_up_closed dual_dist_sup dual_involutive dual_one kernel_def kernel_up_closed up_closed_def strong_up_closed_2)

text \<open>add-distributive contact\<close>

lemma sup_dist_contact_inf_dist_kernel_dual:
  "sup_dist_contact x \<longleftrightarrow> inf_dist_kernel (x\<^sup>d)"
proof
  assume 1: "sup_dist_contact x"
  hence 2: "up_closed x"
    using sup_dist_contact_def contact_up_closed by auto
  have "sup_distributive x"
    using 1 sup_dist_contact_def by auto
  hence "inf_distributive (x\<^sup>d)"
    using 2 by (smt sup_distributive_def dual_dist_comp_one dual_dist_inf dual_involutive inf_distributive_def up_closed_def)
  thus "inf_dist_kernel (x\<^sup>d)"
    using 1 contact_kernel_dual sup_dist_contact_def inf_dist_kernel_def by blast
next
  assume 3: "inf_dist_kernel (x\<^sup>d)"
  hence 4: "up_closed (x\<^sup>d)"
    using kernel_up_closed inf_dist_kernel_def by auto
  have "inf_distributive (x\<^sup>d)"
    using 3 inf_dist_kernel_def by auto
  hence "sup_distributive (x\<^sup>d\<^sup>d)"
    using 4 by (smt inf_distributive_def sup_distributive_def dual_dist_sup dual_involutive strong_up_closed_2)
  thus "sup_dist_contact x"
    using 3 contact_kernel_dual sup_dist_contact_def dual_involutive inf_dist_kernel_def by auto
qed

text \<open>test\<close>

lemma test_co_test_dual:
  "test x \<longleftrightarrow> co_test (x\<^sup>d)"
  by (smt (z3) co_test_def co_test_up_closed dual_dist_comp_one dual_dist_inf dual_involutive dual_one dual_top test_def test_up_closed up_closed_def)

text \<open>vector\<close>

lemma vector_dual:
  "vector x \<longleftrightarrow> vector (x\<^sup>d)"
  by (metis dual_dist_comp_one dual_involutive mult_top_associative)

end

class multirelation_algebra_6 = multirelation_algebra_4 +
  assumes dual_sub_dist_comp_one: "(x * 1)\<^sup>d * y\<^sup>d \<le> (x * y)\<^sup>d"
begin

subclass multirelation_algebra_5
  apply unfold_locales
  by (metis dual_sub_dist_comp dual_sub_dist_comp_one order.eq_iff mult_one_associative)

(*
lemma "dense_rel x \<and> coreflexive x \<longrightarrow> up_closed x" nitpick [expect=genuine,card=5] oops
lemma "x * top \<sqinter> y * z \<le> (x * top \<sqinter> y) * z" nitpick [expect=genuine,card=8] oops
*)

end

text \<open>M3-algebra\<close>

class up_closed_multirelation_algebra = multirelation_algebra_3 +
  assumes dual_dist_comp: "(x * y)\<^sup>d = x\<^sup>d * y\<^sup>d"
begin

lemma mult_right_dist_inf:
  "(x \<sqinter> y) * z = x * z \<sqinter> y * z"
  by (metis dual_dist_sup dual_dist_comp dual_involutive mult_right_dist_sup)

text \<open>AAMP Theorem 9\<close>

subclass idempotent_left_semiring
  apply unfold_locales
  apply (metis order.antisym dual_antitone dual_dist_comp dual_involutive mult_semi_associative)
  apply simp
  by (metis order.antisym dual_antitone dual_dist_comp dual_involutive dual_one mult_sub_right_one)

subclass multirelation_algebra_6
  apply unfold_locales
  by (simp_all add: dual_dist_comp)

lemma vector_inf_comp:
  "(x * top \<sqinter> y) * z = x * top \<sqinter> y * z"
  by (simp add: vector_left_annihilator mult_right_dist_inf mult.assoc)

lemma vector_zero_inf_comp:
  "(x * bot \<sqinter> y) * z = x * bot \<sqinter> y * z"
  by (simp add: mult_right_dist_inf mult.assoc)

text \<open>AAMP Theorem 10 / Figure 3: closure properties\<close>

text \<open>total\<close>

lemma inf_total:
  "total x \<Longrightarrow> total y \<Longrightarrow> total (x \<sqinter> y)"
  by (simp add: mult_right_dist_inf)

lemma comp_total:
  "total x \<Longrightarrow> total y \<Longrightarrow> total (x * y)"
  by (simp add: mult_assoc)

lemma total_co_total_dual:
  "total x \<longleftrightarrow> co_total (x\<^sup>d)"
  by (metis co_total_def dual_dist_comp dual_involutive dual_top)

text \<open>dense\<close>

lemma transitive_iff_dense_dual:
  "transitive x \<longleftrightarrow> dense_rel (x\<^sup>d)"
  by (metis dual_antitone dual_dist_comp dual_involutive)

text \<open>idempotent\<close>

lemma idempotent_dual:
  "idempotent x \<longleftrightarrow> idempotent (x\<^sup>d)"
  using dual_involutive idempotent_transitive_dense transitive_iff_dense_dual by auto

text \<open>add-distributive\<close>

lemma comp_sup_distributive:
  "sup_distributive x \<Longrightarrow> sup_distributive y \<Longrightarrow> sup_distributive (x * y)"
  by (simp add: sup_distributive_def mult.assoc)

lemma sup_inf_distributive_dual:
  "sup_distributive x \<longleftrightarrow> inf_distributive (x\<^sup>d)"
  by (smt (verit, ccfv_threshold) sup_distributive_def dual_dist_sup dual_dist_comp dual_dist_inf dual_involutive inf_distributive_def)

text \<open>inf-distributive\<close>

lemma inf_inf_distributive:
  "inf_distributive x \<Longrightarrow> inf_distributive y \<Longrightarrow> inf_distributive (x \<sqinter> y)"
  by (metis sup_inf_distributive_dual sup_sup_distributive dual_dist_inf dual_involutive)

lemma comp_inf_distributive:
  "inf_distributive x \<Longrightarrow> inf_distributive y \<Longrightarrow> inf_distributive (x * y)"
  by (simp add: inf_distributive_def mult.assoc)

(*
lemma "co_total x \<and> transitive x \<and> up_closed x \<longrightarrow> coreflexive x" nitpick [expect=genuine,card=5] oops
lemma "total x \<and> dense_rel x \<and> up_closed x \<longrightarrow> reflexive x" nitpick [expect=genuine,card=5] oops
lemma "x * top \<sqinter> x\<^sup>d * bot = bot" nitpick [expect=genuine,card=6] oops
*)

end

class multirelation_algebra_7 = multirelation_algebra_4 +
  assumes vector_inf_comp: "(x * top \<sqinter> y) * z = x * top \<sqinter> y * z"
begin

lemma vector_zero_inf_comp:
  "(x * bot \<sqinter> y) * z = x * bot \<sqinter> y * z"
  by (metis vector_inf_comp vector_mult_closed zero_vector)

lemma test_sup_distributive:
  "test x \<Longrightarrow> sup_distributive x"
  by (metis sup_distributive_def inf_sup_distrib1 mult_left_one test_def vector_inf_comp)

lemma test_inf_distributive:
  "test x \<Longrightarrow> inf_distributive x"
  by (smt (z3) inf.right_idem inf.sup_monoid.add_assoc inf.sup_monoid.add_commute inf_distributive_def mult_left_one test_def vector_inf_comp)

lemma test_inf_dist_kernel:
  "test x \<Longrightarrow> inf_dist_kernel x"
  by (metis inf.idem inf.sup_monoid.add_assoc kernel_def inf_dist_kernel_def mult_left_one test_def test_inf_distributive vector_inf_comp)

lemma co_test_inf_distributive:
  assumes "co_test x"
    shows "inf_distributive x"
proof -
  have "x = x * bot \<squnion> 1"
    using assms co_test_def by auto
  hence "\<forall>y z . x * y \<sqinter> x * z = x * (y \<sqinter> z)"
    by (metis distrib_imp1 inf_sup_absorb inf_sup_distrib1 mult_left_one mult_left_top mult_right_dist_sup sup_top_right vector_zero_inf_comp)
  thus "inf_distributive x"
    by (simp add: inf_distributive_def)
qed

lemma co_test_sup_distributive:
  assumes "co_test x"
    shows "sup_distributive x"
proof -
  have "x = x * bot \<squnion> 1"
    using assms co_test_def by auto
  hence "\<forall>y z . x * (y \<squnion> z) = x * y \<squnion> x * z"
    by (metis sup_sup_distributive sup_distributive_def inf_sup_absorb mult_left_top one_sup_distributive sup.idem sup_top_right vector_zero_inf_comp)
  thus "sup_distributive x"
    by (simp add: sup_distributive_def)
qed

lemma co_test_sup_dist_contact:
  "co_test x \<Longrightarrow> sup_dist_contact x"
  by (simp add: sup_dist_contact_def co_test_sup_distributive co_test_contact)

end

end

