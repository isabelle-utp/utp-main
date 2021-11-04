(* Title:      Pre-Post Specifications and Modal Operators
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Pre-Post Specifications and Modal Operators\<close>

theory Pre_Post_Modal

imports Pre_Post Hoare_Modal

begin

class pre_post_spec_whiledo = pre_post_spec_greatest + whiledo
begin

lemma nat_test_pre_post:
  "nat_test t s \<Longrightarrow> -q \<le> s \<Longrightarrow> (\<forall>n . x \<le> t n*-p*-q\<stileturn>(pSum t n*-q)) \<Longrightarrow> -p\<star>x \<le> -q\<stileturn>--p*-q"
  by (smt (verit, ccfv_threshold) nat_test_def nat_test_pre pSum_test_nat pre_post_galois tests_dual.sub_sup_closed)

lemma nat_test_pre_post_2:
  "nat_test t s \<Longrightarrow> -r \<le> s \<Longrightarrow> (\<forall>n . x \<le> t n*-p\<stileturn>(pSum t n)) \<Longrightarrow> -p\<star>x \<le> -r\<stileturn>1"
  by (smt (verit, ccfv_threshold) nat_test_def nat_test_pre_2 one_def pSum_test_nat pre_post_galois tests_dual.sub_sup_closed)

end

class pre_post_spec_hoare = pre_post_spec_whiledo + hoare_calculus_sound
begin

lemma pre_post_while:
  "x \<le> -p*-q\<stileturn>-q \<longrightarrow> -p\<star>x \<le> aL*-q\<stileturn>-q"
  by (smt aL_test pre_post_galois sub_mult_closed while_soundness)

text \<open>Theorem 43.1\<close>

lemma while_soundness_3:
  "test_seq t \<Longrightarrow> -q \<le> Sum t \<Longrightarrow> x \<le> t 0*-p*-q\<stileturn>aL*-q \<Longrightarrow> (\<forall>n>0 . x \<le> t n*-p*-q\<stileturn>pSum t n*-q) \<Longrightarrow> -p\<star>x \<le> -q\<stileturn>--p*-q"
  by (smt (verit, del_insts) aL_test pSum_test tests_dual.inf_closed pre_post_galois sub_mult_closed test_seq_def while_soundness_1)

text \<open>Theorem 43.2\<close>

lemma while_soundness_4:
  "test_seq t \<Longrightarrow> -r \<le> Sum t \<Longrightarrow> (\<forall>n . x \<le> t n*-p\<stileturn>pSum t n) \<Longrightarrow> -p\<star>x \<le> -r\<stileturn>1"
  by (smt one_def pSum_test pre_post_galois sub_mult_closed test_seq_def while_soundness_2)

end

class pre_post_spec_hoare_pc_2 = pre_post_spec_hoare + hoare_calculus_pc_2
begin

text \<open>Theorem 43.3\<close>

lemma pre_post_while_pc:
  "x \<le> -p*-q\<stileturn>-q \<longrightarrow> -p\<star>x \<le> -q\<stileturn>--p*-q"
  by (metis pre_post_galois sub_mult_closed while_soundness_pc)

end

class pre_post_spec_hoare_pc = pre_post_spec_hoare + hoare_calculus_pc
begin

subclass pre_post_spec_hoare_pc_2 ..

lemma pre_post_one_one_top:
  "1\<stileturn>1 = top"
  using order.eq_iff pre_one_one pre_post_one_one by auto

end

class pre_post_spec_H = pre_post_spec_greatest + box_precondition + havoc +
  assumes H_zero_2: "H * bot = bot"
  assumes H_split_2: "x \<le> x * -q * top \<squnion> H * --q"
begin

subclass idempotent_left_semiring_H
  apply unfold_locales
  apply (rule H_zero_2)
  by (smt H_split_2 tests_dual.complement_bot mult_assoc mult_left_zero mult_1_right one_def)

lemma pre_post_def_iff:
  "-p * x * --q \<le> Z \<longleftrightarrow> x \<le> Z \<squnion> --p * top \<squnion> H * -q"
proof (rule iffI)
  assume "-p * x * --q \<le> Z"
  hence "x * --q * top \<le> Z \<squnion> --p * top"
    by (smt (verit, ccfv_threshold) Z_left_zero_above_one case_split_left_sup mult_assoc mult_left_isotone mult_right_dist_sup mult_right_isotone top_greatest top_mult_top)
  thus "x \<le> Z \<squnion> --p * top \<squnion> H * -q"
    by (metis sup_left_isotone order_trans H_split_2 tests_dual.double_negation)
next
  assume "x \<le> Z \<squnion> --p * top \<squnion> H * -q"
  hence "-p * x * --q \<le> -p * (Z * --q \<squnion> --p * top * --q \<squnion> H * -q * --q)"
    by (metis mult_left_isotone mult_right_dist_sup mult_right_isotone mult_assoc)
  thus "-p * x * --q \<le> Z"
    by (metis H_zero_2 Z_mult_decreasing sup_commute sup_bot_left mult_assoc mult_right_dist_sup mult_right_isotone order_trans test_mult_left_dist_shunt test_mult_left_sub_dist_shunt tests_dual.top_def)
qed

lemma pre_post_def:
  "-p\<stileturn>-q = Z \<squnion> --p*top \<squnion> H*-q"
  by (meson order.antisym order_refl pre_Z pre_post_galois pre_post_def_iff)

end

class pre_post_L = pre_post_spec_greatest + box_while + left_conway_semiring_L + left_kleene_conway_semiring +
  assumes circ_below_L_add_star: "x\<^sup>\<circ> \<le> L \<squnion> x\<^sup>\<star>"
begin

text \<open>a loop does not abort if its body does not abort\<close>
text \<open>this avoids abortion from all states* alternatively from states in -r if -r is an invariant\<close>

lemma body_abort_loop:
  assumes "Z = L"
      and "x \<le> -p\<stileturn>1"
    shows "-p\<star>x \<le> 1\<stileturn>1"
proof -
  have "-p * x * bot \<le> L"
    by (metis assms pre_Z pre_post_galois tests_dual.sba_dual.one_def tests_dual.top_double_complement)
  hence "(-p * x)\<^sup>\<star> * bot \<le> L"
    by (metis L_split le_iff_sup star_left_induct sup_bot_left)
  hence "(-p * x)\<^sup>\<circ> * bot \<le> L"
    by (smt L_left_zero L_split sup_commute circ_below_L_add_star le_iff_sup mult_right_dist_sup)
  thus ?thesis
    by (metis assms(1) a_restrict mult_isotone pre_pc_Z pre_post_compose_2 pre_post_one_one tests_dual.sba_dual.one_def while_def tests_dual.sup_right_zero)
qed

end

class pre_post_spec_Hd = pre_post_spec_least + diamond_precondition + idempotent_left_semiring_Hd +
  assumes d_mult_top: "d(x) * top = x * top"
begin

subclass pre_post_spec_least_Hd
  apply unfold_locales
  by (simp add: d_mult_top diamond_x_1 pre_def)

end

end

