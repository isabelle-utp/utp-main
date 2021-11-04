(* Title:      Hoare Calculus and Modal Operators
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Hoare Calculus and Modal Operators\<close>

theory Hoare_Modal

imports Stone_Kleene_Relation_Algebras.Kleene_Algebras Complete_Domain Hoare Relative_Modal

begin

class box_precondition = relative_box_semiring + pre +
  assumes pre_def: "x\<guillemotleft>p = |x]p"
begin

text \<open>Theorem 47\<close>

subclass precondition
  apply unfold_locales
  apply (simp add: box_x_a pre_def)
  apply (simp add: box_left_mult pre_def)
  using box_def box_right_submult_a_a pre_def tests_dual.sba_dual.greatest_lower_bound apply fastforce
  by (simp add: box_1_a pre_def)

subclass precondition_test_test
  apply unfold_locales
  by (simp add: a_box_a_a pre_def)

subclass precondition_promote
  apply unfold_locales
  using a_mult_d box_def pre_def pre_test_test by auto

subclass precondition_test_box
  apply unfold_locales
  by (simp add: box_a_a d_def pre_def)

lemma pre_Z:
  "-p \<le> x\<guillemotleft>-q \<longleftrightarrow> -p * x * --q \<le> Z"
  by (simp add: box_demodalisation_2 pre_def)

lemma pre_left_dist_add:
  "x\<squnion>y\<guillemotleft>-q = (x\<guillemotleft>-q) * (y\<guillemotleft>-q)"
  by (simp add: box_left_dist_sup pre_def)

lemma pre_left_antitone:
  "x \<le> y \<Longrightarrow> y\<guillemotleft>-q \<le> x\<guillemotleft>-q"
  by (simp add: box_antitone_isotone pre_def)

lemma pre_promote_neg:
  "(x\<guillemotleft>-q) * x * --q \<le> Z"
  by (simp add: box_below_Z pre_def)

lemma pre_pc_Z:
  "x\<guillemotleft>1 = 1 \<longleftrightarrow> x * bot \<le> Z"
  by (simp add: a_strict box_x_1 pre_def)

(*
lemma pre_sub_promote: "(x\<guillemotleft>-q) * x \<le> (x\<guillemotleft>-q) * x * -q \<squnion> Z" nitpick [expect=genuine,card=6] oops
lemma pre_promote: "(x\<guillemotleft>-q) * x \<squnion> Z = (x\<guillemotleft>-q) * x * -q \<squnion> Z" nitpick [expect=genuine,card=6] oops
lemma pre_mult_sub_promote: "(x*y\<guillemotleft>-q) * x \<le> (x*y\<guillemotleft>-q) * x * (y\<guillemotleft>-q) \<squnion> Z" nitpick [expect=genuine,card=6] oops
lemma pre_mult_promote: "(x*y\<guillemotleft>-q) * x * (y\<guillemotleft>-q) \<squnion> Z = (x*y\<guillemotleft>-q) * x \<squnion> Z" nitpick [expect=genuine,card=6] oops
*)

end

class left_zero_box_precondition = box_precondition + relative_left_zero_antidomain_semiring
begin

lemma pre_sub_promote:
  "(x\<guillemotleft>-q) * x \<le> (x\<guillemotleft>-q) * x * -q \<squnion> Z"
  using case_split_right_sup pre_promote_neg by blast

lemma pre_promote:
  "(x\<guillemotleft>-q) * x \<squnion> Z = (x\<guillemotleft>-q) * x * -q \<squnion> Z"
  apply (rule sup_same_context)
  apply (simp add: pre_sub_promote)
  by (metis a_below_one le_supI1 mult_1_right mult_right_isotone)

lemma pre_mult_sub_promote:
  "(x*y\<guillemotleft>-q) * x \<le> (x*y\<guillemotleft>-q) * x * (y\<guillemotleft>-q) \<squnion> Z"
  by (metis pre_closed pre_seq pre_sub_promote)

lemma pre_mult_promote_sub:
  "(x*y\<guillemotleft>-q) * x * (y\<guillemotleft>-q) \<le> (x*y\<guillemotleft>-q) * x"
  by (metis mult_right_isotone mult_1_right pre_below_one)

lemma pre_mult_promote:
  "(x*y\<guillemotleft>-q) * x * (y\<guillemotleft>-q) \<squnion> Z = (x*y\<guillemotleft>-q) * x \<squnion> Z"
  by (metis sup_ge1 sup_same_context order_trans pre_mult_sub_promote pre_mult_promote_sub)

end

class diamond_precondition = relative_box_semiring + pre +
  assumes pre_def: "x\<guillemotleft>p = |x>p"
begin

text \<open>Theorem 47\<close>

subclass precondition
  apply unfold_locales
  apply (simp add: d_def diamond_def pre_def)
  apply (simp add: diamond_left_mult pre_def)
  apply (metis a_antitone a_dist_sup box_antitone_isotone box_deMorgan_1 order.refl pre_def sup_right_divisibility)
  by (simp add: diamond_1_a pre_def)

subclass precondition_test_test
  apply unfold_locales
  by (metis diamond_a_a_same diamond_a_export diamond_associative diamond_right_mult pre_def)

subclass precondition_promote
  apply unfold_locales
  using d_def diamond_def pre_def pre_test_test tests_dual.sub_sup_closed by force

subclass precondition_test_diamond
  apply unfold_locales
  by (simp add: diamond_a_a pre_def)

lemma pre_left_dist_add:
  "x\<squnion>y\<guillemotleft>-q = (x\<guillemotleft>-q) \<squnion> (y\<guillemotleft>-q)"
  by (simp add: diamond_left_dist_sup pre_def)

lemma pre_left_isotone:
  "x \<le> y \<Longrightarrow> x\<guillemotleft>-q \<le> y\<guillemotleft>-q"
  by (metis diamond_left_isotone pre_def)

end

class box_while = box_precondition + bounded_left_conway_semiring + ite + while +
  assumes ite_def:   "x\<lhd>p\<rhd>y = p * x \<squnion> -p * y"
  assumes while_def: "p\<star>x = (p * x)\<^sup>\<circ> * -p"
begin

subclass bounded_relative_antidomain_semiring ..

lemma Z_circ_left_zero:
  "Z * x\<^sup>\<circ> = Z"
  using Z_left_zero_above_one circ_plus_one sup.absorb_iff2 by auto

subclass ifthenelse
  apply unfold_locales
  by (smt a_d_closed box_a_export box_left_dist_sup box_x_a tests_dual.case_duality d_def ite_def pre_def)

text \<open>Theorem 48.1\<close>

subclass whiledo
  apply unfold_locales
  apply (smt circ_loop_fixpoint ite_def ite_pre mult_assoc mult_1_right pre_one pre_seq while_def)
  using pre_mult_test_promote while_def by auto

lemma pre_while_1:
  "-p*(-p\<star>x)\<guillemotleft>1 = -p\<star>x\<guillemotleft>1"
proof -
  have "--p*(-p*(-p\<star>x)\<guillemotleft>1) = --p*(-p\<star>x\<guillemotleft>1)"
    by (metis mult_1_right pre_closed pre_seq pre_test_neg tests_dual.sba_dual.top_double_complement while_pre_else)
  thus ?thesis
    by (smt (z3) pre_closed pre_import tests_dual.sba_dual.top_double_complement tests_dual.sup_eq_cases)
qed

lemma aL_one_circ:
  "aL = a(1\<^sup>\<circ>*bot)"
  by (metis aL_def box_left_mult box_x_a idempotent_bot_closed idempotent_one_closed pre_def tests_dual.sba_dual.one_def while_def tests_dual.one_def)

end

class diamond_while = diamond_precondition + bounded_left_conway_semiring + ite + while +
  assumes ite_def:   "x\<lhd>p\<rhd>y = p * x \<squnion> -p * y"
  assumes while_def: "p\<star>x = (p * x)\<^sup>\<circ> * -p"
begin

subclass bounded_relative_antidomain_semiring ..

lemma Z_circ_left_zero:
  "Z * x\<^sup>\<circ> = Z"
  by (simp add: Z_left_zero_above_one circ_reflexive)

subclass ifthenelse
  apply unfold_locales
  by (simp add: ite_def pre_export pre_left_dist_add)

text \<open>Theorem 48.2\<close>

subclass whiledo
  apply unfold_locales
  apply (smt circ_loop_fixpoint ite_def ite_pre mult_assoc mult_1_right pre_one pre_seq while_def)
  by (simp add: pre_mult_test_promote while_def)

lemma aL_one_circ:
  "aL = d(1\<^sup>\<circ>*bot)"
  by (metis aL_def tests_dual.complement_bot diamond_x_1 mult_left_one pre_def while_def)

end

class box_while_program = box_while + atoms
begin

subclass while_program ..

end

class diamond_while_program = diamond_while + atoms
begin

subclass while_program ..

end

class box_hoare_calculus = box_while_program + complete_antidomain_semiring
begin

subclass hoare_calculus ..

end

class diamond_hoare_calculus = diamond_while_program + complete_antidomain_semiring
begin

subclass hoare_calculus ..

end

class box_hoare_sound = box_hoare_calculus + relative_domain_semiring_split + left_kleene_conway_semiring +
  assumes aL_circ: "aL * x\<^sup>\<circ> \<le> x\<^sup>\<star>"
begin

lemma aL_circ_ext:
  "|x\<^sup>\<star>]y \<le> |aL * x\<^sup>\<circ>]y"
  by (simp add: aL_circ box_left_antitone)

lemma box_star_induct:
  assumes "-p \<le> |x](-p)"
    shows "-p \<le> |x\<^sup>\<star>](-p)"
proof -
  have 1: "x*--p*top \<le> Z \<squnion> --p*top"
    by (metis assms Z_top sup_commute box_demodalisation_2 mult_assoc mult_left_isotone shunting_Z)
  have "x*(Z \<squnion> --p*top) \<le> x*--p*top \<squnion> Z"
    using split_Z sup_monoid.add_commute mult_assoc by force
  also have "... \<le> Z \<squnion> --p*top"
    using 1 by simp
  finally have "x*(Z \<squnion> --p*top) \<squnion> --p \<le> Z \<squnion> --p*top"
    using le_supI2 sup.bounded_iff top_right_mult_increasing by auto
  thus ?thesis
    by (metis sup_commute box_demodalisation_2 mult_assoc shunting_Z star_left_induct)
qed

lemma box_circ_induct:
  "-p \<le> |x](-p) \<Longrightarrow> -p*aL \<le> |x\<^sup>\<circ>](-p)"
  by (smt aL_circ_ext aL_test box_left_mult box_star_induct order_trans tests_dual.inf_commutative pre_closed pre_def pre_test tests_dual.shunting_right)

lemma a_while_soundness:
  assumes "-p*-q \<le> |x](-q)"
    shows "aL*-q \<le> |(-p*x)\<^sup>\<circ>*--p](-q)"
proof -
  have "|(-p*x)\<^sup>\<circ>](-q) \<le> |(-p*x)\<^sup>\<circ>*--p](-q)"
    by (meson box_left_antitone circ_mult_upper_bound circ_reflexive order.refl order.trans tests_dual.sub_bot_least)
  thus ?thesis
    by (smt assms box_import_shunting box_circ_induct order_trans sub_comm aL_test)
qed

subclass hoare_calculus_sound
  apply unfold_locales
  by (simp add: a_while_soundness pre_def while_def)

end

class diamond_hoare_sound = diamond_hoare_calculus + left_kleene_conway_semiring +
  assumes aL_circ: "aL * x\<^sup>\<circ> \<le> x\<^sup>\<star>"
begin

lemma aL_circ_equal:
  "aL * x\<^sup>\<circ> = aL * x\<^sup>\<star>"
  apply (rule order.antisym)
  using aL_circ aL_one_circ d_restrict_iff_1 apply force
  by (simp add: mult_right_isotone star_below_circ)

lemma aL_zero:
  "aL = bot"
  by (smt aL_circ_equal aL_one_circ d_export d_idempotent diamond_d_bot diamond_def mult_assoc mult_1_right star_one)

subclass hoare_calculus_sound
  apply unfold_locales
  using aL_zero by auto

end

class box_hoare_complete = box_hoare_calculus + left_kleene_conway_semiring +
  assumes box_circ_induct_2: "-p*|x](-q) \<le> -q \<longrightarrow> |x\<^sup>\<circ>](-p) \<le> -q\<squnion>aL"
  assumes aL_zero_or_one: "aL = bot \<or> aL = 1"
  assumes while_mult_left_dist_Prod: "x \<in> While_program \<and> descending_chain t \<and> test_seq t \<longrightarrow> x*Prod t = Prod (\<lambda>n . x*t n)"
begin

subclass hoare_calculus_complete
  apply unfold_locales
  apply (metis aL_zero_or_one bot_least order.eq_iff mult_1_right pre_closed tests_dual.sup_right_zero)
  subgoal
    apply (unfold pre_def box_def)
    by (metis a_ascending_chain a_dist_Prod a_dist_Sum descending_chain_left_mult while_mult_left_dist_Prod test_seq_def)
  by (smt box_circ_induct_2 tests_dual.double_negation tests_dual.greatest_lower_bound tests_dual.upper_bound_left mult_right_dist_sup pre_closed pre_def pre_import pre_seq pre_test sub_mult_closed while_def)

end

class diamond_hoare_complete = diamond_hoare_calculus + relative_domain_semiring_split + left_kleene_conway_semiring +
  assumes dL_circ: "-aL*x\<^sup>\<circ> \<le> x\<^sup>\<star>"
  assumes aL_zero_or_one: "aL = bot \<or> aL = 1"
  assumes while_mult_left_dist_Sum: "x \<in> While_program \<and> ascending_chain t \<and> test_seq t \<longrightarrow> x*Sum t = Sum (\<lambda>n . x*t n)"
begin

lemma diamond_star_induct_var:
  assumes "|x>(d p) \<le> d p"
    shows "|x\<^sup>\<star>>(d p) \<le> d p"
proof -
  have "x * (d p * x\<^sup>\<star> \<squnion> Z) \<le> d p * x * x\<^sup>\<star> \<squnion> Z * x\<^sup>\<star> \<squnion> Z"
    by (metis assms sup_left_isotone d_mult_d diamond_def diamond_demodalisation_3 mult_assoc mult_left_isotone mult_right_dist_sup order_trans split_Z)
  also have "... \<le> d p * x\<^sup>\<star> \<squnion> Z"
    by (metis Z_mult_decreasing mult_right_isotone star.left_plus_below_circ sup.bounded_iff sup_ge1 sup_mono sup_monoid.add_commute mult_assoc)
  finally show ?thesis
    by (smt sup_commute le_sup_iff sup_ge2 d_mult_d diamond_def diamond_demodalisation_3 order_trans star.circ_back_loop_prefixpoint star_left_induct)
qed

lemma diamond_star_induct:
  "d q \<squnion> |x>(d p) \<le> d p \<Longrightarrow> |x\<^sup>\<star>>(d q) \<le> d p"
  by (metis le_sup_iff diamond_star_induct_var diamond_right_isotone order_trans)

lemma while_completeness_1:
  assumes "-p*(x\<guillemotleft>-q) \<le> -q"
    shows "-p\<star>x\<guillemotleft>-q \<le> -q\<squnion>aL"
proof -
  have "--p*-q \<squnion> |-p*x>(-q) \<le> -q"
    using assms pre_def pre_export tests_dual.upper_bound_right by auto
  hence "|(-p*x)\<^sup>\<star>>(--p*-q) \<le> -q"
    by (smt diamond_star_induct d_def sub_mult_closed tests_dual.double_negation)
  hence "|-aL*(-p*x)\<^sup>\<circ>>(--p*-q) \<le> -q"
    by (meson dL_circ diamond_isotone order.eq_iff order.trans)
  thus ?thesis
    by (smt aL_test diamond_a_export diamond_def mult_assoc tests_dual.inf_commutative pre_closed pre_def tests_dual.shunting while_def)
qed

subclass hoare_calculus_complete
  apply unfold_locales
  apply (metis aL_test aL_zero_or_one bot_least order.eq_iff pre_closed pre_test pre_test_one tests_dual.sup_right_zero)
  subgoal
    apply (unfold pre_def diamond_def)
    by (simp add: ascending_chain_left_mult d_dist_Sum while_mult_left_dist_Sum)
  by (simp add: while_completeness_1)

end

class box_hoare_valid = box_hoare_sound + box_hoare_complete + hoare_triple +
  assumes hoare_triple_def: "p\<lbrace>x\<rbrace>q \<longleftrightarrow> p \<le> |x]q"
begin

text \<open>Theorem 49.2\<close>

subclass hoare_calculus_valid
  apply unfold_locales
  by (simp add: hoare_triple_def pre_def)

lemma rule_skip_valid:
  "-p\<lbrace>1\<rbrace>-p"
  by (simp add: rule_skip)

end

class diamond_hoare_valid = diamond_hoare_sound + diamond_hoare_complete + hoare_triple +
  assumes hoare_triple_def: "p\<lbrace>x\<rbrace>q \<longleftrightarrow> p \<le> |x>q"
begin

lemma circ_star_equal:
  "x\<^sup>\<circ> = x\<^sup>\<star>"
  by (metis aL_zero order.antisym dL_circ mult_left_one one_def star_below_circ)

text \<open>Theorem 49.1\<close>

subclass hoare_calculus_valid
  apply unfold_locales
  by (simp add: hoare_triple_def pre_def)

end

class diamond_hoare_sound_2 = diamond_hoare_calculus + left_kleene_conway_semiring +
  assumes diamond_circ_induct_2: "--p*-q \<le> |x>(-q) \<longrightarrow>  aL*-q \<le> |x\<^sup>\<circ>>(-p)"
begin

subclass hoare_calculus_sound
  apply unfold_locales
  by (smt a_export diamond_associative diamond_circ_induct_2 tests_dual.double_negation tests_dual.sup_complement_intro pre_def pre_import_equiv_mult sub_comm sub_mult_closed while_def)

end

class diamond_hoare_valid_2 = diamond_hoare_sound_2 + diamond_hoare_complete + hoare_triple +
  assumes hoare_triple_def: "p\<lbrace>x\<rbrace>q \<longleftrightarrow> p \<le> |x>q"
begin

subclass hoare_calculus_valid
  apply unfold_locales
  by (simp add: hoare_triple_def pre_def)

end

end

