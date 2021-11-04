section \<open>Algorithms to compute all complex and real roots of a cubic polynomial\<close>

theory Cubic_Polynomials
  imports 
    Cardanos_Formula
    Complex_Roots
begin

hide_const (open) MPoly_Type.degree
hide_const (open) MPoly_Type.coeffs

(* TODO: this should be integrated into distribution *)
lemma complex_of_real_code[code_unfold]: "complex_of_real = (\<lambda> x. Complex x 0)" 
  by (intro ext, auto simp: complex_eq_iff)

text \<open>The real case where a result is only delivered if the discriminant is negative\<close>

definition solve_depressed_cubic_Cardano_real :: "real \<Rightarrow> real \<Rightarrow> real option" where
  "solve_depressed_cubic_Cardano_real e f = (
    if e = 0 then Some (root 3 (-f)) else
     let v = - (e ^ 3 / 27) in
     case rroots2 [:v,f,1:] of 
       [u,_] \<Rightarrow> let rt = root 3 u in Some (rt - e / (3 * rt))
     | _ \<Rightarrow> None)" 

lemma solve_depressed_cubic_Cardano_real: 
  assumes "solve_depressed_cubic_Cardano_real e f = Some y" 
  shows "{y. y^3 + e * y + f = 0} = {y}"
proof (cases "e = 0")
  case True
  have "{y. y^3 + e * y + f = 0} = {y. y^3 = -f}" unfolding True 
    by (auto simp add: field_simps)
  also have "\<dots> = {root 3 (-f)}" 
    using odd_real_root_unique[of 3 _ "-f"] odd_real_root_pow[of 3] by auto
  also have "root 3 (-f) = y" using assms unfolding True solve_depressed_cubic_Cardano_real_def
    by auto
  finally show ?thesis .
next
  case False
  define v where "v = - (e ^ 3 / 27)" 
  note * = assms[unfolded solve_depressed_cubic_Cardano_real_def Let_def, folded v_def]
  let ?rr = "rroots2 [:v,f,1:]" 
  from * False obtain u u' where rr: "?rr = [u,u']" 
    by (cases ?rr; cases "tl ?rr"; cases "tl (tl ?rr)"; auto split: if_splits)
  from *[unfolded rr list.simps] False 
  have y: "y = root 3 u - e / (3 * root 3 u)" by auto
  have "u \<in> set (rroots2 [:v,f,1:])" unfolding rr by auto
  also have "set (rroots2 [:v,f,1:]) = {u. poly [:v,f,1:] u = 0}" 
    by (subst rroots2, auto)
  finally have u: "u^2 + f * u + v = 0" by (simp add: field_simps power2_eq_square)
  note Cardano = solve_cubic_depressed_Cardano_real[OF False v_def u]
  have 2: "2 = Suc (Suc 0)" by simp
  from rr have 0: "f\<^sup>2 - 4 * v \<noteq> 0" unfolding rroots2_def Let_def
    by (auto split: if_splits simp: 2)
  hence 0: "discriminant_cubic_depressed e f \<noteq> 0" 
    unfolding discriminant_cubic_depressed_def v_def by auto
  show ?thesis using Cardano(1) Cardano(2)[OF 0] unfolding y[symmetric] by blast
qed

text \<open>The complex case\<close>

definition solve_depressed_cubic_complex :: "complex \<Rightarrow> complex \<Rightarrow> complex list" where
  "solve_depressed_cubic_complex e f = (let
          ys = (if e = 0 then all_croots 3 (- f) else (let
       u = hd (croots2 [: - (e ^ 3 / 27) ,f,1:]); 
       zs = all_croots 3 u 
       in map (\<lambda> z. z - e / (3 * z)) zs))
      in remdups ys)" 

lemma solve_depressed_cubic_complex_code[code]: 
  "solve_depressed_cubic_complex e f = (let
          ys = (if e = 0 then all_croots 3 (- f) else (let
            f2 = f / 2;
            u = - f2 + csqrt (f2^2 + e ^ 3 / 27);
            zs = all_croots 3 u 
            in map (\<lambda> z. z - e / (3 * z)) zs))
      in remdups ys)" 
  unfolding solve_depressed_cubic_complex_def Let_def croots2_def 
  by (simp add: numeral_2_eq_2)


lemma solve_depressed_cubic_complex: "y \<in> set (solve_depressed_cubic_complex e f) 
  \<longleftrightarrow> (y^3 + e * y + f = 0)"
proof (cases "e = 0")
  case True
  thus ?thesis by (simp add: solve_depressed_cubic_complex_def Let_def all_croots eq_neg_iff_add_eq_0)
next
  case e0: False
  hence id: "(if e = 0 then x else y) = y" for x y :: "complex list" by simp
  define v where "v = - (e ^ 3 / 27)" 
  define p where "p = [:v, f, 1:]" 
  have p2: "degree p = 2" unfolding p_def by auto
  let ?u = "hd (croots2 p)" 
  define u where "u = ?u" 
  have "u \<in> set (croots2 p)" unfolding croots2_def Let_def u_def by auto
  with croots2[OF p2] have "poly p u = 0" by auto
  hence u: "u^2 + f * u + v = 0" unfolding p_def
    by (simp add: field_simps power2_eq_square)
  note cube_roots = all_croots[of 3, simplified]
  show ?thesis unfolding solve_depressed_cubic_complex_def Let_def set_remdups set_map id cube_roots
    unfolding v_def[symmetric] p_def[symmetric] set_concat set_map
      u_def[symmetric]
  proof - 
    have p: "{x. poly p x = 0} = {u. u^2 + f * u + v = 0}" unfolding p_def by (auto simp: field_simps power2_eq_square)
    have cube: "\<Union> (set ` all_croots 3 ` {x. poly p x = 0}) = {z. \<exists> u. u\<^sup>2 + f * u + v = 0 \<and> z ^ 3 = u}" 
      unfolding p by (auto simp: cube_roots)
    show "(y \<in> (\<lambda>z. z - e / (3 * z)) ` {y. y ^ 3 = u}) = (y ^ 3 + e * y + f = 0)"
      using solve_cubic_depressed_Cardano_complex[OF e0 v_def u] cube by blast
  qed
qed

text \<open>For the general real case, we first try Cardano with negative discrimiant and only if it is not applicable,
   then we go for the calculation using complex numbers. Note that for for non-negative delta 
   no filter is required to identify the real roots from the list of complex roots, since in that case we 
   already know that all roots are real.\<close>
definition solve_depressed_cubic_real :: "real \<Rightarrow> real \<Rightarrow> real list" where
  "solve_depressed_cubic_real e f = (case solve_depressed_cubic_Cardano_real e f 
      of Some y \<Rightarrow> [y] 
       | None \<Rightarrow> map Re (solve_depressed_cubic_complex (of_real e) (of_real f)))"

lemma solve_depressed_cubic_real_code[code]: "solve_depressed_cubic_real e f =
  (if e = 0 then [root 3 (-f)] else 
   let v = e ^ 3 / 27; 
       f2 = f / 2;
       f2v = f2^2 + v in
   if f2v > 0 then 
     let u = -f2 + sqrt f2v;
         rt = root 3 u
      in [rt - e / (3 * rt)]
  else 
  let ce3 = of_real e / 3; 
      u = - of_real f2 + csqrt (of_real f2v) in
   map Re (remdups (map (\<lambda>rt. rt - ce3 / rt) (all_croots 3 u))))" 
proof -
  have id: "rroots2 [:v, f, 1:] = (let 
     f2 = f / 2;
     bac = f2\<^sup>2 - v in 
     if bac = 0 then [- f2] else 
     if bac < 0 then [] else let e = sqrt bac in [- f2 + e, - f2 - e])" for v
    unfolding rroots2_def Let_def numeral_2_eq_2 by auto
  define foo :: "real \<Rightarrow> real \<Rightarrow> real option" where 
    "foo f2v f2 = (case (if f2v = 0 then [- f2] else []) of [] \<Rightarrow> None | _ \<Rightarrow> None)" 
    for f2v f2
  have "solve_depressed_cubic_real e f = (if e = 0 then [root 3 (-f)] else 
   let v = e ^ 3 / 27; 
       f2 = f / 2;
       f2v = f2\<^sup>2 + v in
   if f2v > 0 then 
     let u = -f2 + sqrt f2v;
         rt = root 3 u
      in [rt - e / (3 * rt)]
  else 
  (case foo f2v f2 of
     None \<Rightarrow> let u = - cor f2 + csqrt (cor f2v) in
   map Re
    (remdups (map (\<lambda>z. z - cor e / (3 * z)) (all_croots 3 u)))
   | Some y \<Rightarrow> []))" 
    unfolding solve_depressed_cubic_real_def solve_depressed_cubic_Cardano_real_def 
      solve_depressed_cubic_complex_code
      Let_def id foo_def
    by (auto split: if_splits)
  also have id: "foo f2v f2 = None" 
    for f2v f2 unfolding foo_def by auto
  ultimately show ?thesis by (auto simp: Let_def)
qed

lemma solve_depressed_cubic_real: "y \<in> set (solve_depressed_cubic_real e f) 
  \<longleftrightarrow> (y^3 + e * y + f = 0)" 
proof (cases "solve_depressed_cubic_Cardano_real e f")
  case (Some x)
  show ?thesis unfolding solve_depressed_cubic_real_def Some option.simps
    using solve_depressed_cubic_Cardano_real[OF Some] by auto
next
  case None
  from this[unfolded solve_depressed_cubic_Cardano_real_def Let_def rroots2_def]
  have disc: "0 \<le> discriminant_cubic_depressed e f" unfolding discriminant_cubic_depressed_def
    by (auto split: if_splits simp: numeral_2_eq_2)
  let ?c = "complex_of_real" 
  let ?y = "?c y" 
  let ?e = "?c e" 
  let ?f = "?c f" 
  have sub: "set (solve_depressed_cubic_complex ?e ?f) \<subseteq> \<real>" 
  proof 
    fix y
    assume y: "y \<in> set (solve_depressed_cubic_complex ?e ?f)" 
    show "y \<in> \<real>" 
      by (rule solve_cubic_depressed_Cardano_all_real_roots[OF disc y[unfolded solve_depressed_cubic_complex]])
  qed
  have "y^3 + e * y + f = 0 \<longleftrightarrow> (?c (y^3 + e * y + f) = ?c 0)" unfolding of_real_eq_iff by simp
  also have "\<dots> \<longleftrightarrow> ?y^3 + ?e * ?y + ?f = 0" by simp
  also have "\<dots> \<longleftrightarrow> ?y \<in> set (solve_depressed_cubic_complex ?e ?f)" 
    unfolding solve_depressed_cubic_complex ..
  also have "\<dots> \<longleftrightarrow> y \<in> Re ` set (solve_depressed_cubic_complex ?e ?f)" using sub by force
  finally show ?thesis unfolding solve_depressed_cubic_real_def None by auto
qed

text \<open>Combining the various algorithms\<close>

lemma degree3_coeffs: "degree p = 3 \<Longrightarrow>
  \<exists> a b c d. p = [: d, c, b, a :] \<and> a \<noteq> 0"
  by (metis One_nat_def Suc_1 degree2_coeffs degree_pCons_eq_if nat.inject numeral_3_eq_3 pCons_cases zero_neq_numeral)

definition roots3_generic :: "('a :: field_char_0 \<Rightarrow> 'a \<Rightarrow> 'a list) \<Rightarrow> 'a poly \<Rightarrow> 'a list" where
  "roots3_generic depressed_solver p = (let 
     cs = coeffs p; 
     a = cs ! 3; b = cs ! 2; c = cs ! 1; d = cs ! 0;
     a3 = 3 * a;
     ba3 = b / a3;
     b2 = b * b;
     b3 = b2 * b;
     e = (c - b2 / a3) / a;
     f = (d + 2 * b3 / (27 * a^2) - b * c / a3) / a;
     roots = depressed_solver e f
     in map (\<lambda> y. y - ba3) roots)" 

lemma roots3_generic: assumes deg: "degree p = 3" 
  and solver: "\<And> e f y. y \<in> set (depressed_solver e f) \<longleftrightarrow> y^3 + e * y + f = 0" 
  shows "set (roots3_generic depressed_solver p) = {x. poly p x = 0}" 
proof -
  note powers = field_simps power3_eq_cube power2_eq_square
  from degree3_coeffs[OF deg] obtain a b c d where
    p: "p = [:d,c,b,a:]" and a: "a \<noteq> 0" by auto
  have coeffs: "coeffs p ! 3 = a" "coeffs p ! 2 = b" "coeffs p ! 1 = c" "coeffs p ! 0 = d" 
    unfolding p using a by auto
  define e where "e = (c - b^2 / (3 * a)) / a" 
  define f where "f = (d + 2 * b^3 / (27 * a^2) - b * c / (3 * a)) / a" 
  note def = roots3_generic_def[of depressed_solver p, unfolded Let_def coeffs,
      folded power3_eq_cube, folded power2_eq_square,  folded e_def f_def]
  {
    fix x :: 'a
    define y where "y = x + b / (3 * a)" 
    have xy: "x = y - b / (3 * a)" unfolding y_def by auto
    have "poly p x = 0 \<longleftrightarrow> a * x^3 + b * x^2 + c * x + d = 0" unfolding p
      by (simp add: powers)
    also have "\<dots> \<longleftrightarrow> (y ^ 3 + e * y + f = 0)" 
      unfolding to_depressed_cubic[OF a xy e_def f_def] ..
    also have "\<dots> \<longleftrightarrow> y \<in> set (depressed_solver e f)" 
      unfolding solver ..
    also have "\<dots> \<longleftrightarrow> x \<in> set (roots3_generic depressed_solver p)" unfolding xy def by auto
    finally have "poly p x = 0 \<longleftrightarrow> x \<in> set (roots3_generic depressed_solver p)" by auto
  }
  thus ?thesis by auto
qed

definition croots3 :: "complex poly \<Rightarrow> complex list" where
  "croots3 = roots3_generic solve_depressed_cubic_complex"

lemma croots3: assumes deg: "degree p = 3" 
  shows "set (croots3 p) = { x. poly p x = 0}" 
  unfolding croots3_def by (rule roots3_generic[OF deg solve_depressed_cubic_complex])

definition rroots3 :: "real poly \<Rightarrow> real list" where
  "rroots3 = roots3_generic solve_depressed_cubic_real"

lemma rroots3: assumes deg: "degree p = 3" 
  shows "set (rroots3 p) = { x. poly p x = 0}" 
  unfolding rroots3_def by (rule roots3_generic[OF deg solve_depressed_cubic_real])

end