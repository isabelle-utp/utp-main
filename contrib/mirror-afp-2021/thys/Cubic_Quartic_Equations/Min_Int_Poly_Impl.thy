section \<open>Implementation of the minimal polynomial of a real or complex algebraic number\<close>

text \<open>This theory provides implementation of the minimal-representing-polynomial of an algebraic
  number, for both the real-numbers and the complex-numbers.\<close>

theory Min_Int_Poly_Impl
  imports     
    Hermite_Lindemann.Min_Int_Poly
    Algebraic_Numbers.Real_Algebraic_Numbers
    Algebraic_Numbers.Complex_Algebraic_Numbers
begin
 
definition min_int_poly_real_alg :: "real_alg \<Rightarrow> int poly" where
  "min_int_poly_real_alg x = (case info_real_alg x of Inl r \<Rightarrow> poly_rat r | Inr (p,_) \<Rightarrow> p)" 

lemma min_int_poly_of_rat: "min_int_poly (of_rat r :: 'a :: {field_char_0, field_gcd}) = poly_rat r"
  by (intro min_int_poly_unique, auto)
  
lemma min_int_poly_real_alg: "min_int_poly_real_alg x = min_int_poly (real_of x)" 
proof (cases "info_real_alg x")
  case (Inl r)
  show ?thesis unfolding info_real_alg(2)[OF Inl] min_int_poly_real_alg_def Inl
    by (simp add: min_int_poly_of_rat)
next
  case (Inr pair)
  then obtain p n where Inr: "info_real_alg x = Inr (p,n)" by (cases pair, auto)
  hence "poly_cond p" by (transfer, transfer, auto simp: info_2_card)  
  hence "min_int_poly (real_of x) = p" using info_real_alg(1)[OF Inr]
    by (intro min_int_poly_unique, auto)
  thus ?thesis unfolding min_int_poly_real_alg_def Inr by simp
qed

definition min_int_poly_real :: "real \<Rightarrow> int poly" where
  [simp]: "min_int_poly_real = min_int_poly" 

lemma min_int_poly_real_code_unfold [code_unfold]: "min_int_poly = min_int_poly_real" 
  by simp

lemma min_int_poly_real_code[code]: "min_int_poly_real (real_of x) = min_int_poly_real_alg x" 
  by (simp add: min_int_poly_real_alg)

text \<open>Now let us head for the complex numbers\<close>
  
definition complex_poly :: "int poly \<Rightarrow> int poly \<Rightarrow> int poly list" where
  "complex_poly re im = (let i = [:1,0,1:] 
     in factors_of_int_poly (poly_add re (poly_mult im i)))" 

lemma complex_poly: assumes re: "re represents (Re x)" 
   and im: "im represents (Im x)" 
  shows "\<exists> f \<in> set (complex_poly re im). f represents x" "\<And> f. f \<in> set (complex_poly re im) \<Longrightarrow> poly_cond f" 
proof -
  let ?p = "poly_add re (poly_mult im [:1, 0, 1:])" 
  from re have re: "re represents complex_of_real (Re x)" by simp
  from im have im: "im represents complex_of_real (Im x)" by simp
  have "[:1,0,1:] represents \<i>" by auto
  from represents_add[OF re represents_mult[OF im this]]
  have "?p represents of_real (Re x) + complex_of_real (Im x) * \<i>" by simp
  also have "of_real (Re x) + complex_of_real (Im x) * \<i> = x"
    by (metis complex_eq mult.commute)
  finally have p: "?p represents x" by auto
  have "factors_of_int_poly ?p = complex_poly re im" 
    unfolding complex_poly_def Let_def by simp
  from factors_of_int_poly(1)[OF this] factors_of_int_poly(2)[OF this, of x] p
  show "\<exists> f \<in> set (complex_poly re im). f represents x" "\<And> f. f \<in> set (complex_poly re im) \<Longrightarrow> poly_cond f" 
    unfolding represents_def by auto
qed
 

definition algebraic_real :: "real \<Rightarrow> bool" where 
  [simp]: "algebraic_real = algebraic" 

lemma algebraic_real_iff[code_unfold]: "algebraic = algebraic_real" by simp

lemma algebraic_real_code[code]: "algebraic_real (real_of x) = True" 
proof (cases "info_real_alg x")
  case (Inl r)
  show ?thesis using info_real_alg(2)[OF Inl] by (auto simp: algebraic_of_rat)
next
  case (Inr pair)
  then obtain p n where Inr: "info_real_alg x = Inr (p,n)" by (cases pair, auto)
  from info_real_alg(1)[OF Inr] have "p represents (real_of x)" by auto
  thus ?thesis by (auto simp: algebraic_altdef_ipoly)
qed

lemma algebraic_complex_iff[code_unfold]: "algebraic x \<longleftrightarrow> algebraic (Re x) \<and> algebraic (Im x)" 
proof
  assume "algebraic x" 
  from this[unfolded algebraic_altdef_ipoly] obtain p where "ipoly p x = 0" "p \<noteq> 0" by auto
  from represents_root_poly[OF this] show "algebraic (Re x) \<and> algebraic (Im x)" 
    unfolding represents_def algebraic_altdef_ipoly by auto
next
  assume "algebraic (Re x) \<and> algebraic (Im x)" 
  from this[unfolded algebraic_altdef_ipoly] obtain re im where 
    "re represents (Re x)" "im represents (Im x)" by blast
  from complex_poly[OF this] show "algebraic x" 
    unfolding represents_def algebraic_altdef_ipoly by auto
qed

lemma algebraic_0[simp]: "algebraic 0"
  unfolding algebraic_altdef_ipoly
  by (intro exI[of _ "[:0,1:]"], auto)

lemma min_int_poly_complex_of_real[simp]: "min_int_poly (complex_of_real x) = min_int_poly x" 
proof (cases "algebraic x")
  case False
  hence "\<not> algebraic (complex_of_real x)" unfolding algebraic_complex_iff by auto
  with False show ?thesis unfolding min_int_poly_def by auto
next
  case True
  from min_int_poly_represents[OF True]
  have "min_int_poly x represents x" by auto
  thus ?thesis
    by (intro min_int_poly_unique, auto simp: lead_coeff_min_int_poly_pos)
qed
  


text \<open>TODO: the implemention might be tuned, since the search process should be faster when
  using interval arithmetic to figure out the correct factor.
  (One might also implement the search via checking @{term "ipoly f x = 0"}, but because of complex-algebraic-number
   arithmetic, I think that search would be slower than the current one via "@{term "x \<in> set (complex_roots_of_int_poly f)"}\<close>
definition min_int_poly_complex :: "complex \<Rightarrow> int poly" where
  "min_int_poly_complex x = (if algebraic x then if Im x = 0 then min_int_poly_real (Re x)
     else the (find (\<lambda> f. x \<in> set (complex_roots_of_int_poly f)) (complex_poly (min_int_poly (Re x)) (min_int_poly (Im x))))
     else [:0,1:])" 
 
lemma min_int_poly_complex[code_unfold]: "min_int_poly = min_int_poly_complex" 
proof (standard)
  fix x
  define fs where "fs = complex_poly (min_int_poly (Re x)) (min_int_poly (Im x))" 
  let ?f = "min_int_poly_complex x" 
  show "min_int_poly x = ?f" 
  proof (cases "algebraic x")
    case False
    thus ?thesis unfolding min_int_poly_def min_int_poly_complex_def by auto
  next
    case True
    show ?thesis
    proof (cases "Im x = 0")
      case *: True
      have id: "?f = min_int_poly_real (Re x)" unfolding min_int_poly_complex_def * using True by auto
      show ?thesis unfolding id min_int_poly_real_code_unfold[symmetric] min_int_poly_complex_of_real[symmetric]
        using * by (intro arg_cong[of _ _ min_int_poly] complex_eqI, auto)
    next
      case False  
      from True[unfolded algebraic_complex_iff] have "algebraic (Re x)" "algebraic (Im x)" by auto
      from complex_poly[OF min_int_poly_represents[OF this(1)] min_int_poly_represents[OF this(2)]]
      have fs: "\<exists> f \<in> set fs. ipoly f x = 0" "\<And> f. f \<in> set fs \<Longrightarrow> poly_cond f" unfolding fs_def by auto
      let ?fs = "find (\<lambda> f. ipoly f x = 0) fs" 
      let ?fs' = "find (\<lambda> f. x \<in> set (complex_roots_of_int_poly f)) fs" 
      have "?f = the ?fs'" unfolding min_int_poly_complex_def fs_def
        using True False by auto
      also have "?fs' = ?fs" 
        by (rule find_cong[OF refl], subst complex_roots_of_int_poly, insert fs, auto)
      finally have id: "?f = the ?fs" .
      from fs(1) have "?fs \<noteq> None" unfolding find_None_iff by auto
      then obtain f where Some: "?fs = Some f" by auto
      from find_Some_D[OF this] fs(2)[of f]
      show ?thesis unfolding id Some
        by (intro min_int_poly_unique, auto)
    qed
  qed
qed

(* outcommented tests, since time-consuming:

value (code) "min_int_poly (sqrt 2 + 3)" 
value (code) "min_int_poly (sqrt 2 + \<i>)" 

*)
end
