(*
  File:    Puiseux_Laurent_Library.thy
  Author:  Manuel Eberl, TU München
*)
subsection \<open>Facts about Laurent series\<close>
theory Puiseux_Laurent_Library
  imports "HOL-Computational_Algebra.Computational_Algebra"
begin

lemma filterlim_at_top_div_const_nat:
  assumes "c > 0"
  shows   "filterlim (\<lambda>x::nat. x div c) at_top at_top"
  unfolding filterlim_at_top
proof
  fix C :: nat
  have *: "n div c \<ge> C" if "n \<ge> C * c" for n
    using assms that by (metis div_le_mono div_mult_self_is_m)
  have "eventually (\<lambda>n. n \<ge> C * c) at_top"
    by (rule eventually_ge_at_top)
  thus "eventually (\<lambda>n. n div c \<ge> C) at_top"
    by eventually_elim (use * in auto)
qed

lemma fls_eq_iff: "f = g \<longleftrightarrow> (\<forall>n. fls_nth f n = fls_nth g n)"
  by transfer auto

lemma fls_shift_eq_1_iff: "fls_shift n f = 1 \<longleftrightarrow> f = fls_shift (-n) 1"
proof -
  have "fls_shift n f = 1 \<longleftrightarrow> fls_shift n f = fls_shift n (fls_shift (-n) 1)"
    by (simp del: fls_shift_eq_iff)
  also have "\<dots> \<longleftrightarrow> f = fls_shift (-n) 1"
    by (subst fls_shift_eq_iff) auto
  finally show ?thesis .
qed

lemma fps_to_fls_eq_iff [simp]: "fps_to_fls f = fps_to_fls g \<longleftrightarrow> f = g"
proof safe
  assume "fps_to_fls f = fps_to_fls g"
  hence *: "n < 0 \<or> f $ nat n = g $ nat n" for n
    by (force simp: fls_eq_iff split: if_splits)
  have "f $ n = g $ n" for n
    using *[of "int n"] by auto
  thus "f = g"
    by (auto simp: fps_eq_iff)
qed

lemma fps_to_fls_eq_0_iff [simp]: "fps_to_fls f = 0 \<longleftrightarrow> f = 0"
  using fps_to_fls_eq_iff[of f 0] by (simp del: fps_to_fls_eq_iff)

lemma fps_to_fls_eq_1_iff [simp]: "fps_to_fls f = 1 \<longleftrightarrow> f = 1"
  using fps_to_fls_eq_iff[of f 1] by (simp del: fps_to_fls_eq_iff)

lemma fps_to_fls_power: "fps_to_fls (f ^ n) = fps_to_fls f ^ n"
  by (induction n) (auto simp: fls_times_fps_to_fls)

lemma fls_as_fps:
  fixes f :: "'a :: zero fls" and n :: int
  assumes n: "n \<ge> -fls_subdegree f"
  obtains f' where "f = fls_shift n (fps_to_fls f')"
proof -
  have "fls_subdegree (fls_shift (- n) f) \<ge> 0"
    by (rule fls_shift_nonneg_subdegree) (use n in simp)
  hence "f = fls_shift n (fps_to_fls (fls_regpart (fls_shift (-n) f)))"
    by (subst fls_regpart_to_fls_trivial) simp_all
  thus ?thesis
    by (rule that)
qed

lemma fls_as_fps':
  fixes f :: "'a :: zero fls" and n :: int
  assumes n: "n \<ge> -fls_subdegree f"
  shows "\<exists>f'. f = fls_shift n (fps_to_fls f')"
  using fls_as_fps[OF assms] by metis


definition fls_compose_fps :: "'a :: field fls \<Rightarrow> 'a fps \<Rightarrow> 'a fls" where
  "fls_compose_fps f g =
     (if f = 0 then 0
      else if fls_subdegree f \<ge> 0 then fps_to_fls (fps_compose (fls_regpart f) g)
      else fps_to_fls (fps_compose (fls_base_factor_to_fps f) g) /
             fps_to_fls g ^ nat (-fls_subdegree f))"

lemma fls_compose_fps_fps [simp]:
  "fls_compose_fps (fps_to_fls f) g = fps_to_fls (fps_compose f g)"
  by (auto simp: fls_compose_fps_def fls_subdegree_fls_to_fps)

lemma fls_const_transfer [transfer_rule]:
  "rel_fun (=) (pcr_fls (=))
     (\<lambda>c n. if n = 0 then c else 0) fls_const"
  by (auto simp: fls_const_def rel_fun_def pcr_fls_def OO_def cr_fls_def)

lemma fls_shift_transfer [transfer_rule]:
  "rel_fun (=) (rel_fun (pcr_fls (=)) (pcr_fls (=)))
     (\<lambda>n f k. f (k+n)) fls_shift"
  by (auto simp: fls_const_def rel_fun_def pcr_fls_def OO_def cr_fls_def)

lift_definition fls_compose_power :: "'a :: zero fls \<Rightarrow> nat \<Rightarrow> 'a fls" is
  "\<lambda>f d n. if d > 0 \<and> int d dvd n then f (n div int d) else 0"
proof -
  fix f :: "int \<Rightarrow> 'a" and d :: nat
  assume *: "eventually (\<lambda>n. f (-int n) = 0) cofinite"
  show "eventually (\<lambda>n. (if d > 0 \<and> int d dvd -int n then f (-int n div int d) else 0) = 0) cofinite"
  proof (cases "d = 0")
    case False
    from * have "eventually (\<lambda>n. f (-int n) = 0) at_top"
      by (simp add: cofinite_eq_sequentially)
    hence "eventually (\<lambda>n. f (-int (n div d)) = 0) at_top"
      by (rule eventually_compose_filterlim[OF _ filterlim_at_top_div_const_nat]) (use False in auto)
    hence "eventually (\<lambda>n. (if d > 0 \<and> int d dvd -int n then f (-int n div int d) else 0) = 0) at_top"
      by eventually_elim (auto simp: zdiv_int dvd_neg_div)
    thus ?thesis
      by (simp add: cofinite_eq_sequentially)
  qed auto
qed

lemma fls_nth_compose_power:
  assumes "d > 0"
  shows   "fls_nth (fls_compose_power f d) n = (if int d dvd n then fls_nth f (n div int d) else 0)"
  using assms by transfer auto
     

lemma fls_compose_power_0_left [simp]: "fls_compose_power 0 d = 0"
  by transfer auto

lemma fls_compose_power_1_left [simp]: "d > 0 \<Longrightarrow> fls_compose_power 1 d = 1"
  by transfer (auto simp: fun_eq_iff)

lemma fls_compose_power_const_left [simp]:
  "d > 0 \<Longrightarrow> fls_compose_power (fls_const c) d = fls_const c"
  by transfer (auto simp: fun_eq_iff)

lemma fls_compose_power_shift [simp]:
  "d > 0 \<Longrightarrow> fls_compose_power (fls_shift n f) d = fls_shift (d * n) (fls_compose_power f d)"
  by transfer (auto simp: fun_eq_iff add_ac mult_ac)

lemma fls_compose_power_X_intpow [simp]:
  "d > 0 \<Longrightarrow> fls_compose_power (fls_X_intpow n) d = fls_X_intpow (int d * n)"
  by simp

lemma fls_compose_power_X [simp]:
  "d > 0 \<Longrightarrow> fls_compose_power fls_X d = fls_X_intpow (int d)"
  by transfer (auto simp: fun_eq_iff)

lemma fls_compose_power_X_inv [simp]:
  "d > 0 \<Longrightarrow> fls_compose_power fls_X_inv d = fls_X_intpow (-int d)"
  by (simp add: fls_X_inv_conv_shift_1)

lemma fls_compose_power_0_right [simp]: "fls_compose_power f 0 = 0"
  by transfer auto

lemma fls_compose_power_add [simp]:
  "fls_compose_power (f + g) d = fls_compose_power f d + fls_compose_power g d"
  by transfer auto

lemma fls_compose_power_diff [simp]:
  "fls_compose_power (f - g) d = fls_compose_power f d - fls_compose_power g d"
  by transfer auto

lemma fls_compose_power_uminus [simp]:
  "fls_compose_power (-f) d = -fls_compose_power f d"
  by transfer auto

lemma fps_nth_compose_X_power:
  "fps_nth (f oo (fps_X ^ d)) n = (if d dvd n then fps_nth f (n div d) else 0)"
proof -
  have "fps_nth (f oo (fps_X ^ d)) n = (\<Sum>i = 0..n. f $ i * (fps_X ^ (d * i)) $ n)"
    unfolding fps_compose_def by (simp add: power_mult)
  also have "\<dots> = (\<Sum>i\<in>(if d dvd n then {n div d} else {}). f $ i * (fps_X ^ (d * i)) $ n)"
    by (intro sum.mono_neutral_right) auto
  also have "\<dots> = (if d dvd n then fps_nth f (n div d) else 0)"
    by auto
  finally show ?thesis .
qed

lemma fls_compose_power_fps_to_fls:
  assumes "d > 0"
  shows   "fls_compose_power (fps_to_fls f) d = fps_to_fls (fps_compose f (fps_X ^ d))"
  using assms
  by (intro fls_eqI) (auto simp: fls_nth_compose_power fps_nth_compose_X_power
                                 pos_imp_zdiv_neg_iff div_neg_pos_less0 nat_div_distrib
                           simp flip: int_dvd_int_iff)

lemma fls_compose_power_mult [simp]:
  "fls_compose_power (f * g :: 'a :: idom fls) d = fls_compose_power f d * fls_compose_power g d"
proof (cases "d > 0")
  case True
  define n where "n = nat (max 0 (max (- fls_subdegree f) (- fls_subdegree g)))"
  have n_ge: "-fls_subdegree f \<le> int n" "-fls_subdegree g \<le> int n"
    unfolding n_def by auto
  obtain f' where f': "f = fls_shift n (fps_to_fls f')"
    using fls_as_fps[OF n_ge(1)] by (auto simp: n_def)
  obtain g' where g': "g = fls_shift n (fps_to_fls g')"
    using fls_as_fps[OF n_ge(2)] by (auto simp: n_def)
  show ?thesis using \<open>d > 0\<close>
    by (simp add: f' g' fls_shifted_times_simps mult_ac fls_compose_power_fps_to_fls
                  fps_compose_mult_distrib flip: fls_times_fps_to_fls)
qed auto

lemma fls_compose_power_power [simp]:
  assumes "d > 0 \<or> n > 0"
  shows   "fls_compose_power (f ^ n :: 'a :: idom fls) d = fls_compose_power f d ^ n"
proof (cases "d > 0")
  case True
  thus ?thesis by (induction n) auto
qed (use assms in auto)

lemma fls_nth_compose_power' [simp]:
  "d = 0 \<or> \<not>d dvd n \<Longrightarrow> fls_nth (fls_compose_power f d) n = 0"
  "d dvd n \<Longrightarrow> d > 0 \<Longrightarrow> fls_nth (fls_compose_power f d) n = fls_nth f (n div d)"
  by (transfer; force; fail)+

end