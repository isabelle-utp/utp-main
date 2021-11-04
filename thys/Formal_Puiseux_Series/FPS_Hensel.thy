(*
  File:    FPS_Hensel.thy
  Author:  Manuel Eberl, TU München
*)
section \<open>Hensel's lemma for formal power series\<close>
theory FPS_Hensel
  imports "HOL-Computational_Algebra.Computational_Algebra" Puiseux_Polynomial_Library
begin

text \<open>
  The following proof of Hensel's lemma for formal power series follows the book
  ``Algebraic Geometry for Scientists and Engineers'' by Abhyankar~\cite[p.~90--92]{abhyankar1990}.
\<close>

definition fps_poly_swap1 :: "'a :: zero fps poly \<Rightarrow> 'a poly fps" where
  "fps_poly_swap1 p = Abs_fps (\<lambda>m. Abs_poly (\<lambda>n. fps_nth (coeff p n) m))"

lemma coeff_fps_nth_fps_poly_swap1 [simp]:
  "coeff (fps_nth (fps_poly_swap1 p) m) n = fps_nth (coeff p n) m"
proof -
  have "\<forall>\<^sub>\<infinity>n. poly.coeff p n = 0"
    using MOST_coeff_eq_0 by blast
  hence "\<forall>\<^sub>\<infinity>n. poly.coeff p n $ m = 0"
    by eventually_elim auto
  thus ?thesis
    by (simp add: fps_poly_swap1_def poly.Abs_poly_inverse)
qed

definition fps_poly_swap2 :: "'a :: zero poly fps \<Rightarrow> 'a fps poly" where
  "fps_poly_swap2 p = Abs_poly (\<lambda>m. Abs_fps (\<lambda>n. coeff (fps_nth p n) m))"

lemma fps_nth_coeff_fps_poly_swap2:
  assumes "\<And>n. degree (fps_nth p n) \<le> d"
  shows   "fps_nth (coeff (fps_poly_swap2 p) m) n = coeff (fps_nth p n) m"
proof -
  have "\<forall>\<^sub>\<infinity>n. n > d"
    using MOST_nat by blast
  hence "\<forall>\<^sub>\<infinity>n. (\<lambda>m. poly.coeff (p $ m) n) = (\<lambda>_. 0)"
    by eventually_elim (auto simp: fun_eq_iff intro!: coeff_eq_0 le_less_trans[OF assms(1)])
  hence ev: "\<forall>\<^sub>\<infinity>n. Abs_fps (\<lambda>m. poly.coeff (p $ m) n) = 0"
    by eventually_elim (simp add: fps_zero_def)

  have "fps_nth (coeff (fps_poly_swap2 p) m) n =
          poly.coeff (Abs_poly (\<lambda>m. Abs_fps (\<lambda>n. poly.coeff (p $ n) m))) m $ n"
    by (simp add: fps_poly_swap2_def)
  also have "\<dots> = Abs_fps (\<lambda>n. poly.coeff (p $ n) m) $ n"
    using ev by (subst poly.Abs_poly_inverse) auto
  finally show "fps_nth (coeff (fps_poly_swap2 p) m) n = coeff (fps_nth p n) m"
    by simp
qed

lemma degree_fps_poly_swap2_le:
  assumes "\<And>n. degree (fps_nth p n) \<le> d"
  shows   "degree (fps_poly_swap2 p) \<le> d"
proof (safe intro!: degree_le)
  fix n assume "n > d"
  show "poly.coeff (fps_poly_swap2 p) n = 0"
  proof (rule fps_ext)
    fix m
    have "poly.coeff (fps_poly_swap2 p) n $ m = poly.coeff (p $ m) n"
      by (subst fps_nth_coeff_fps_poly_swap2[OF assms]) auto
    also have "\<dots> = 0"
      by (intro coeff_eq_0 le_less_trans[OF assms \<open>n > d\<close>])
    finally show "poly.coeff (fps_poly_swap2 p) n $ m = 0 $ m"
      by simp
  qed
qed

lemma degree_fps_poly_swap2_eq:
  assumes "\<And>n. degree (fps_nth p n) \<le> d"
  assumes "d > 0 \<or> fps_nth p n \<noteq> 0"
  assumes "degree (fps_nth p n) = d"
  shows   "degree (fps_poly_swap2 p) = d"
proof (rule antisym)
  have "fps_nth (coeff (fps_poly_swap2 p) d) n = poly.coeff (fps_nth p n) d"
    by (subst fps_nth_coeff_fps_poly_swap2[OF assms(1)]) auto
  also have "\<dots> \<noteq> 0"
    using assms(2,3) by force
  finally have "coeff (fps_poly_swap2 p) d \<noteq> 0"
    by force
  thus "degree (fps_poly_swap2 p) \<ge> d"
    using le_degree by blast
next
  show "degree (fps_poly_swap2 p) \<le> d"
    by (intro degree_fps_poly_swap2_le) fact
qed

definition reduce_fps_poly :: "'a :: zero fps poly \<Rightarrow> 'a poly" where
  "reduce_fps_poly F = fps_nth (fps_poly_swap1 F) 0"

lemma
  fixes F :: "'a :: field fps poly"
  assumes "lead_coeff F = 1"
  shows   degree_reduce_fps_poly_monic: "degree (reduce_fps_poly F) = degree F"
    and   reduce_fps_poly_monic: "lead_coeff (reduce_fps_poly F) = 1"
proof -
  have eq1: "coeff (reduce_fps_poly F) (degree F) = 1"
    unfolding reduce_fps_poly_def by (simp add: assms)
  have eq2: "coeff (reduce_fps_poly F) n = 0" if "n > degree F" for n
    unfolding reduce_fps_poly_def using that by (simp add: coeff_eq_0)

  have "degree (reduce_fps_poly F) \<le> degree F"
    by (rule degree_le) (auto simp: eq2)
  moreover have "degree (reduce_fps_poly F) \<ge> degree F"
    by (rule le_degree) (simp add: eq1)
  from eq1 eq2 show "degree (reduce_fps_poly F) = degree F"
    by (intro antisym le_degree degree_le) auto
  with eq1 show "lead_coeff (reduce_fps_poly F) = 1"  
    by simp
qed

locale fps_hensel_aux =
  fixes F :: "'a :: field_gcd poly fps"
  fixes g h :: "'a poly"
  assumes coprime: "coprime g h" and deg_g: "degree g > 0" and deg_h: "degree h > 0"
begin

context
  fixes g' h' :: "'a poly"
  defines "h' \<equiv> fst (bezout_coefficients g h)" and "g' \<equiv> snd (bezout_coefficients g h)"
begin

fun hensel_fpxs_aux :: "nat \<Rightarrow> 'a poly \<times> 'a poly" where
  "hensel_fpxs_aux n = (if n = 0 then (g, h) else
     (let
        U = fps_nth F n -
              (\<Sum>(i,j) | i < n \<and> j < n \<and> i + j = n. fst (hensel_fpxs_aux i) * snd (hensel_fpxs_aux j))
      in (U * g' + g * ((U * h') div h), (U * h') mod h)))"

lemmas [simp del] = hensel_fpxs_aux.simps

lemma hensel_fpxs_aux_0 [simp]: "hensel_fpxs_aux 0 = (g, h)"
  by (subst hensel_fpxs_aux.simps) auto

definition hensel_fpxs1 :: "'a poly fps"
  where "hensel_fpxs1 = Abs_fps (fst \<circ> hensel_fpxs_aux)"

definition hensel_fpxs2 :: "'a poly fps"
  where "hensel_fpxs2 = Abs_fps (snd \<circ> hensel_fpxs_aux)"

lemma hensel_fpxs1_0 [simp]: "hensel_fpxs1 $ 0 = g"
  by (simp add: hensel_fpxs1_def)

lemma hensel_fpxs2_0 [simp]: "hensel_fpxs2 $ 0 = h"
  by (simp add: hensel_fpxs2_def)

theorem fps_hensel_aux:
  defines "f \<equiv> fps_nth F 0"
  assumes "f = g * h"
  assumes "\<forall>n>0. degree (fps_nth F n) < degree f"
  defines "G \<equiv> hensel_fpxs1" and "H \<equiv> hensel_fpxs2"
  shows "F = G * H" "fps_nth G 0 = g" "fps_nth H 0 = h"
        "\<forall>n>0. degree (fps_nth G n) < degree g"
        "\<forall>n>0. degree (fps_nth H n) < degree h"
proof -
  show "fps_nth G 0 = g" "fps_nth H 0 = h"
    by (simp_all add: G_def H_def hensel_fpxs1_def hensel_fpxs2_def)

  have deg_f: "degree f = degree g + degree h"
    unfolding \<open>f = g * h\<close> using assms by (intro degree_mult_eq) auto

  have deg_H: "degree (fps_nth H n) < degree h" if \<open>n > 0\<close> for n
  proof (cases "snd (hensel_fpxs_aux n) = 0")
    case False
    thus ?thesis
      using deg_h \<open>n > 0\<close>
      by (auto simp: hensel_fpxs_aux.simps[of n] hensel_fpxs2_def H_def intro: degree_mod_less')
  qed (use assms deg_h in \<open>auto simp: hensel_fpxs2_def\<close>)
  thus "\<forall>n>0. degree (fps_nth H n) < degree h"
    by blast

  have *: "fps_nth F n = fps_nth (G * H) n \<and> (n > 0 \<longrightarrow> degree (fps_nth G n) < degree g)" for n
  proof (induction n rule: less_induct)
    case (less n)
    have fin: "finite {p. fst p < n \<and> snd p < n \<and> fst p + snd p = n}"
      by (rule finite_subset[of _ "{..n} \<times> {..n}"]) auto
    show ?case
    proof (cases "n = 0")
      case True
      thus ?thesis using assms
        by (auto simp: hensel_fpxs1_def hensel_fpxs2_def)
    next
      case False
      define U where "U = fps_nth F n -
         (\<Sum>(i,j) | i < n \<and> j < n \<and> i + j = n. fst (hensel_fpxs_aux i) * snd (hensel_fpxs_aux j))"
      define g'' h'' where "g'' = U * g'" and "h'' = U * h'"

      have "fps_nth (G * H) n =
              (\<Sum>i=0..n. fst (hensel_fpxs_aux i) * snd (hensel_fpxs_aux (n - i)))"
        using assms by (auto simp: hensel_fpxs1_def hensel_fpxs2_def fps_mult_nth)
      also have "\<dots> = (\<Sum>(i,j) | i + j = n. fst (hensel_fpxs_aux i) * snd (hensel_fpxs_aux j))"
        by (rule sum.reindex_bij_witness[of _ fst "\<lambda>i. (i, n - i)"]) auto
      also have "{(i,j). i + j = n} = {(i,j). i < n \<and> j < n \<and> i + j = n} \<union> {(n,0), (0,n)}"
        by auto
      also have "(\<Sum>(i,j)\<in>\<dots>. fst (hensel_fpxs_aux i) * snd (hensel_fpxs_aux j)) =
                 fps_nth F n - U + (fst (hensel_fpxs_aux n) * h + g * snd (hensel_fpxs_aux n))"
        using False fin by (subst sum.union_disjoint) (auto simp: case_prod_unfold U_def)
      also have eq: "fst (hensel_fpxs_aux n) * h + g * snd (hensel_fpxs_aux n) = U"
      proof -
        have "fst (hensel_fpxs_aux n) * h + g * snd (hensel_fpxs_aux n) =
              (g'' + g * (h'' div h)) * h + g * (h'' mod h)"
          using False by (simp add: hensel_fpxs_aux.simps[of n] U_def g''_def h''_def)
        also have "h'' mod h = h'' - (h'' div h) * h"
          by (simp add: minus_div_mult_eq_mod)
        also have "(g'' + g * (h'' div h)) * h + g * (h'' - h'' div h * h) = g * h'' + g'' * h"
          by (simp add: algebra_simps)
        also have "\<dots> = U * (h' * g + g' * h)"
          by (simp add: algebra_simps g''_def h''_def)
        also have "h' * g + g' * h = gcd g h"
          unfolding g'_def h'_def by (rule bezout_coefficients_fst_snd)
        also have "gcd g h = 1"
          using coprime by simp
        finally show ?thesis by simp
      qed
      finally have "fps_nth F n = fps_nth (G * H) n" by simp

      have "degree (G $ n) < degree g"
      proof (cases "G $ n = 0")
        case False
        have "degree (G $ n) + degree h = degree (G $ n * h)"
          using False assms by (intro degree_mult_eq [symmetric]) auto
        also from eq have "fps_nth G n * h = U - g * snd (hensel_fpxs_aux n)"
          by (simp add: algebra_simps G_def hensel_fpxs1_def)
        hence "degree (fps_nth G n * h) = degree (U - g * snd (hensel_fpxs_aux n))"
          by (simp only: )
        also have "\<dots> < degree f"
        proof (intro degree_diff_less)
          have "degree (g * snd (local.hensel_fpxs_aux n)) \<le>
                degree g + degree (snd (local.hensel_fpxs_aux n))"
            by (intro degree_mult_le)
          also have "degree (snd (local.hensel_fpxs_aux n)) < degree h"
            using deg_H[of n] \<open>n \<noteq> 0\<close> by (auto simp: H_def hensel_fpxs2_def)
          also have "degree g + degree h = degree f"
            by (subst deg_f) auto
          finally show "degree (g * snd (local.hensel_fpxs_aux n)) < degree f"
            by simp
        next
          show "degree U < degree f"
            unfolding U_def
          proof (intro degree_diff_less degree_sum_less)
            show "degree (F $ n) < degree f"
              using \<open>n \<noteq> 0\<close> assms by auto
          next
            show "degree f > 0"
              unfolding deg_f using deg_g by simp
          next
            fix z assume z: "z \<in> {(i, j). i < n \<and> j < n \<and> i + j = n}"
            have "degree (case z of (i, j) \<Rightarrow> fst (hensel_fpxs_aux i) * snd (hensel_fpxs_aux j)) =
                    degree (fps_nth G (fst z) * fps_nth H (snd z))" (is "?lhs = _")
              by (simp add: case_prod_unfold G_def H_def hensel_fpxs1_def hensel_fpxs2_def)
            also have "\<dots> \<le> degree (fps_nth G (fst z)) + degree (fps_nth H (snd z))"
              by (intro degree_mult_le)
            also have "\<dots> < degree g + degree h"
              using z less.IH[of "fst z"]
              by (intro add_strict_mono deg_H) (simp_all add: case_prod_unfold)
            finally show "?lhs < degree f"
              by (simp add: deg_f)
          qed
        qed
        finally show ?thesis
          by (simp add: deg_f) 
      qed (use deg_g in auto)

      with \<open>fps_nth F n = fps_nth (G * H) n\<close> show ?thesis
        by blast
    qed
  qed

  from * show "F = G * H" and "\<forall>n>0. degree (fps_nth G n) < degree g"
    by (auto simp: fps_eq_iff)
qed

end

end


locale fps_hensel =
  fixes F :: "'a :: field_gcd fps poly" and f g h :: "'a poly"
  assumes monic: "lead_coeff F = 1"
  defines "f \<equiv> reduce_fps_poly F"
  assumes f_splits: "f = g * h"
  assumes coprime: "coprime g h" and deg_g: "degree g > 0" and deg_h: "degree h > 0"
begin

definition F' where "F' = fps_poly_swap1 F" 

sublocale fps_hensel_aux F' g h
  by unfold_locales (fact deg_g deg_h coprime)+


definition G where
  "G = fps_poly_swap2 hensel_fpxs1"

definition H where
  "H = fps_poly_swap2 hensel_fpxs2"

lemma deg_f: "degree f = degree F"
proof (intro antisym)
  have "coeff f (degree F) \<noteq> 0"
    using monic by (simp add: f_def reduce_fps_poly_def)
  thus "degree f \<ge> (degree F)"
    by (rule le_degree)
next
  have "coeff f n = 0" if "n > degree F" for n
    using that by (simp add: f_def reduce_fps_poly_def coeff_eq_0)
  thus "degree f \<le> degree F"
    using degree_le by blast
qed

lemma
  F_splits:     "F = G * H" and
  reduce_G:     "reduce_fps_poly G = g" and
  reduce_H:     "reduce_fps_poly H = h" and
  deg_G:        "degree G = degree g" and
  deg_H:        "degree H = degree h" and
  lead_coeff_G: "lead_coeff G = fps_const (lead_coeff g)" and
  lead_coeff_H: "lead_coeff H = fps_const (lead_coeff h)"
proof -
  from deg_g deg_h have [simp]: "g \<noteq> 0" "h \<noteq> 0"
    by auto
  define N where "N = degree F"

  have deg_f: "degree f = N"
  proof (intro antisym)
    have "coeff f N \<noteq> 0"
      using monic by (simp add: f_def reduce_fps_poly_def N_def)
    thus "degree f \<ge> N"
      by (rule le_degree)
  next
    have "coeff f n = 0" if "n > N" for n
      using that by (simp add: f_def reduce_fps_poly_def N_def coeff_eq_0)
    thus "degree f \<le> N"
      using degree_le by blast
  qed

  have "F' $ 0 = f"
    unfolding F'_def f_def reduce_fps_poly_def ..
  have F'0: "F' $ 0 = g * h"
    using f_splits by (simp add: F'_def f_def reduce_fps_poly_def)

  have "\<forall>n>0. degree (F' $ n) < N"
  proof (subst F'_def, intro allI impI degree_lessI)
    fix n :: nat
    assume n: "n > 0"
    show "fps_poly_swap1 F $ n \<noteq> 0 \<or> 0 < N"
      using n deg_g deg_h f_splits deg_f by (auto simp: F'0 degree_mult_eq)
    fix k
    assume k: "k \<ge> N"
    have "coeff (F' $ n) k = coeff F k $ n"
      unfolding F'_def by simp
    also have "\<dots>= 0"
      using monic \<open>n > 0\<close> k by (cases "k > N") (auto simp: N_def coeff_eq_0)
    finally show "coeff (fps_poly_swap1 F $ n) k = 0"
      by (simp add: F'_def)
  qed
  hence degs_less: "\<forall>n>0. degree (F' $ n) < degree (F' $ 0)"
    by (simp add: \<open>F' $ 0 = f\<close> deg_f)
  note hensel = fps_hensel_aux[OF F'0 degs_less]

  have deg_less1: "degree (hensel_fpxs1 $ n) < degree g" if "n > 0" for n
    using hensel(4) that by (simp add: F'_def)
  have deg_le1: "degree (hensel_fpxs1 $ n) \<le> degree g" for n
  proof (cases "n = 0")
    case True
    hence "hensel_fpxs1 $ n = g"
      by (simp add: hensel_fpxs1_def)
    thus ?thesis by simp
  qed (auto intro: less_imp_le deg_less1 simp: f_def)

  have deg_less2: "degree (hensel_fpxs2 $ n) < degree h" if "n > 0" for n
    using hensel(5) that by (simp add: F'_def)
  have deg_le2: "degree (hensel_fpxs2 $ n) \<le> degree h" for n
  proof (cases "n = 0")
    case True
    hence "hensel_fpxs2 $ n = h"
      by (simp add: hensel_fpxs2_def)
    thus ?thesis by simp
  qed (auto intro: less_imp_le deg_less2 simp: f_def)

  show "F = G * H"
    unfolding poly_eq_iff fps_eq_iff
  proof safe
    fix n k
    have "poly.coeff F n $ k = poly.coeff (F' $ k) n"
      unfolding F'_def by simp
    also have "F' = hensel_fpxs1 * hensel_fpxs2"
      by (rule hensel)
    also have "\<dots> $ k = (\<Sum>i=0..k. hensel_fpxs1 $ i * hensel_fpxs2 $ (k - i))"
      unfolding fps_mult_nth ..
    also have "poly.coeff \<dots> n =
                 (\<Sum>i=0..k. \<Sum>j\<le>n. coeff (hensel_fpxs1 $ i) j * coeff (hensel_fpxs2 $ (k - i)) (n - j))"
      by (simp add: coeff_sum coeff_mult)
    also have "(\<lambda>i j. coeff (hensel_fpxs1 $ i) j) = (\<lambda>i j. coeff G j $ i)"
      unfolding G_def
      by (subst fps_nth_coeff_fps_poly_swap2[OF deg_le1]) (auto simp: F'_def)
    also have "(\<lambda>i j. coeff (hensel_fpxs2 $ i) j) = (\<lambda>i j. coeff H j $ i)"
      unfolding H_def
      by (subst fps_nth_coeff_fps_poly_swap2[OF deg_le2]) (auto simp: F'_def)
    also have "(\<Sum>i=0..k. \<Sum>j\<le>n. poly.coeff G j $ i * poly.coeff H (n - j) $ (k - i)) =
               (\<Sum>j\<le>n. \<Sum>i=0..k. poly.coeff G j $ i * poly.coeff H (n - j) $ (k - i))"
      by (rule sum.swap)
    also have "\<dots> = poly.coeff (G * H) n $ k"
      by (simp add: coeff_mult fps_mult_nth fps_sum_nth)
    finally show "poly.coeff F n $ k = poly.coeff (G * H) n $ k" .
  qed

  show "reduce_fps_poly G = g" unfolding G_def reduce_fps_poly_def poly_eq_iff
    by (auto simp: fps_nth_coeff_fps_poly_swap2[OF deg_le1])
  show "reduce_fps_poly H = h" unfolding H_def reduce_fps_poly_def poly_eq_iff
    by (auto simp: fps_nth_coeff_fps_poly_swap2[OF deg_le2])
  show "degree G = degree g" unfolding G_def
    by (rule degree_fps_poly_swap2_eq[where n = 0] deg_le1 disjI1 deg_g deg_le2)+ simp_all
  show "degree H = degree h" unfolding H_def
    by (rule degree_fps_poly_swap2_eq[where n = 0] deg_le1 disjI1 deg_h deg_le2)+ simp_all

  show "lead_coeff G = fps_const (lead_coeff g)"
  proof (rule fps_ext)
    fix n ::nat
    have "lead_coeff G $ n = coeff (hensel_fpxs1 $ n) (degree G)"
      by (subst G_def, subst fps_nth_coeff_fps_poly_swap2[OF deg_le1]) auto
    also have "\<dots> = (if n = 0 then lead_coeff g else 0)"
      by (auto simp: \<open>degree G = degree g\<close> intro: coeff_eq_0 deg_less1)
    finally show "lead_coeff G $ n = fps_const (lead_coeff g) $ n"
      by simp
  qed

  show "lead_coeff H = fps_const (lead_coeff h)"
  proof (rule fps_ext)
    fix n ::nat
    have "lead_coeff H $ n = coeff (hensel_fpxs2 $ n) (degree H)"
      by (subst H_def, subst fps_nth_coeff_fps_poly_swap2[OF deg_le2]) auto
    also have "\<dots> = (if n = 0 then lead_coeff h else 0)"
      by (auto simp: \<open>degree H = degree h\<close> intro: coeff_eq_0 deg_less2)
    finally show "lead_coeff H $ n = fps_const (lead_coeff h) $ n"
      by simp
  qed
qed

end

end