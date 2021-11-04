subsection "Negative Infinity"
theory NegInfinity
  imports "HOL-Analysis.Poly_Roots" VSAlgos
begin



lemma freeIn_allzero : "freeIn var (allZero p var)"
  by (simp add: not_in_isovarspar freeIn_list_conj)

lemma allzero_eval :
  assumes lLength : "var < length L"
  shows"(\<exists>x. \<forall>y<x. aEval (Eq p) (list_update L var y) ) = (\<forall>x. eval (allZero p var) (list_update L var x))"
proof-
  define n where "n = MPoly_Type.degree p var"
  define k where "k i x =((insertion (nth_default 0(list_update L var x)) (isolate_variable_sparse p var i)))" for i x
  {fix x
    have "(eval (allZero p var) (list_update L var x)) =
        (\<forall>i\<in>{0..<(MPoly_Type.degree p var)+1}. aEval (Eq(isolate_variable_sparse p var i)) (list_update L var x))"
      by (simp add: eval_list_conj atLeast0_lessThan_Suc)
    also have "... = (\<forall>i\<in>{0..<(MPoly_Type.degree p var)+1}. (insertion (nth_default 0(list_update L var x)) (isolate_variable_sparse p var i))=0)"
      by simp
    also have "... = (\<forall>i\<le>(MPoly_Type.degree p var). (insertion (nth_default 0(list_update L var x)) (isolate_variable_sparse p var i))=0)"
      by fastforce
    also have "... = (\<forall>y. (\<Sum>i\<le>(MPoly_Type.degree p var). ((insertion (nth_default 0(list_update L var x)) (isolate_variable_sparse p var i)) * y ^ i))=0)"
      using polyfun_eq_const[where n="MPoly_Type.degree p var", where k="0", where c="\<lambda>i. (insertion (nth_default 0(list_update L var x)) (isolate_variable_sparse p var i))"]
      by (metis (no_types, lifting) le_add2 le_add_same_cancel2)
    also have "... = (\<forall>y. (\<Sum>i\<le>n. (k i x) * y ^ i)=0)"
      using k_def n_def by simp
    finally have  "(eval (allZero p var) (list_update L var x)) = (\<forall>y. (\<Sum>i\<le>n. (k i x) * y ^ i)=0)"
      by simp
  }
  then have h1 : "(\<forall>x. (eval (allZero p var) (list_update L var x))) = (\<forall>x.(\<forall>y. (\<Sum>i\<le>n. (k i x) * y ^ i)=0))"
    by simp

  have "(\<exists>y. \<forall>x<y. (\<Sum>i\<le>n. (k i x)* x^i)= 0) = (\<exists>y. \<forall>x<y. (\<Sum>i\<le>(MPoly_Type.degree p var). (insertion (nth_default 0 (list_update L var x))(isolate_variable_sparse p var i))* x^i)= 0)"
    using k_def n_def by simp
  also have "... = (\<exists>y. \<forall>x<y. insertion (nth_default 0 (list_update L var x)) (\<Sum>i\<le>(MPoly_Type.degree p var). (isolate_variable_sparse p var i)* Var var^i)= 0)"
    by(simp add: insertion_sum' insertion_mult insertion_pow insertion_var lLength)
  also have "... = (\<exists>y. \<forall>x<y. insertion (nth_default 0 (list_update L var x)) p = 0)"
    using sum_over_zero  by simp
  also have "... = (\<exists>y. \<forall>x<y. aEval (Eq p) (list_update L var x))"
    by simp
  finally have h2 : "(\<exists>y. \<forall>x<y. aEval (Eq p) (list_update L var x)) = (\<exists>y. \<forall>x<y. (\<Sum>i\<le>n. (k i x)* x^i)= 0)"
    by simp

  have k_all : "\<forall>x y i. k i x = k i y"
    unfolding k_def
    by (simp add: insertion_isovarspars_free)
  have h3a : "(\<exists>y. \<forall>x<y. (\<Sum>i\<le>n. (k i x)* x^i)= 0) \<Longrightarrow> (\<forall>x.(\<forall>y. (\<Sum>i\<le>n. (k i x) * y ^ i)=0))"
  proof-
    assume h : "(\<exists>y. \<forall>x<y. (\<Sum>i\<le>n. (k i x)* x^i)= 0)"
    {fix z y
      assume h : "(\<forall>x<y. (\<Sum>i\<le>n. (k i x)* x^i)= 0)"
      have "\<forall>x<y.\<forall>i\<le>n. k i x = k i z"
        unfolding k_def
        using insertion_isovarspars_free by blast
      then have * : "\<forall>x<y.\<forall>i\<le>n. k i x * x ^ i = k i z * x^i"
        by auto
      then have "\<forall>x<y. (\<Sum>i\<le>n. k i x * x ^ i) = (\<Sum>i\<le>n. k i z * x ^ i)"
        by (metis (no_types, lifting) k_all sum.cong)
      then have "\<forall>x<y. (\<Sum>i\<le>n. (k i z)* x^i)= 0"
        using h  by simp
      then have "\<not>(finite {x. (\<Sum>i\<le>n. k i z * x ^ i) = 0})"
        using infinite_Iio[where a="y"]  Inf_many_def[where P="\<lambda>x. (\<Sum>i\<le>n. k i z * x ^ i) = 0"]
        by (smt INFM_iff_infinite frequently_mono lessThan_def)
      then have "\<forall>i\<le>n. k i z = 0"
        using  polyfun_rootbound[where n="n",  where c = "\<lambda>i. k i z" ]
        by blast
    }
    then have "\<forall>x.\<forall>i\<le>n. k i x = 0"
      using h
      by (meson gt_ex)
    then show ?thesis by simp
  qed
  have h3b : "(\<forall>x.(\<forall>y. (\<Sum>i\<le>n. (k i x) * y ^ i)=0)) \<Longrightarrow> (\<exists>y. \<forall>x<y. (\<Sum>i\<le>n. (k i x)* x^i)= 0)"
  proof-
    assume h : "(\<forall>x.(\<forall>y. (\<Sum>i\<le>n. (k i x) * y ^ i)=0))"
    {fix z y x
      have "(\<Sum>i\<le>n. (k i z)* x^i)= 0"
        using h k_all by blast
      then have "\<forall>i\<le>n. k i z = 0"
        using polyfun_eq_const[where k="0", where c = "\<lambda>i. k i z", where n="n"]
        by (metis h)
    }
    then have "\<forall>x.\<forall>i\<le>n. k i x = 0"
      by (meson gt_ex)
    then show ?thesis by simp
  qed
  have h3 : "(\<exists>y. \<forall>x<y. (\<Sum>i\<le>n. (k i x)* x^i)= 0) = (\<forall>x.(\<forall>y. (\<Sum>i\<le>n. (k i x) * y ^ i)=0))"
    using h3a h3b by auto
  show ?thesis using h1 h2 h3 by simp
qed




lemma freeIn_altNegInf : "freeIn var (alternateNegInfinity p var)"
proof-
  have h1 : "\<forall>i. var \<notin> (vars (if (i::nat) mod 2 = 0 then (Const(1)::real mpoly) else (Const(-1)::real mpoly)))"
    using var_not_in_Const[where var = "var", where x="1"] var_not_in_Const[where var = "var", where x="-1"]
    by simp
  define g where "g = (\<lambda>F.\<lambda>i.
    let a_n = isolate_variable_sparse p var i in
    let exp = (if i mod 2 = 0 then Const(1) else Const(-1)) in
      or (Atom(Less (exp * a_n)))
        (and (Atom (Eq a_n)) F)
    )"
  have h3 : "\<forall>i. \<forall>F. (freeIn var F \<longrightarrow> freeIn var (g F i))"
    using g_def h1
    by (smt PolyAtoms.and_def not_in_isovarspar PolyAtoms.or_def freeIn.simps(1) freeIn.simps(2) freeIn.simps(7) freeIn.simps(8) not_in_mult) 
  define L where "L = ([0..<((MPoly_Type.degree p var)+1)])"
  have "\<forall>F. freeIn var F \<longrightarrow> freeIn var (foldl (g::atom fm \<Rightarrow> nat \<Rightarrow> atom fm) F (L::nat list))"
  proof(induction L)
    case Nil
    then show ?case by simp
  next
    case (Cons a L)
    then show ?case using h3 by simp
  qed
  then have "freeIn var (foldl g FalseF L)"
    using freeIn.simps(6) by blast 
  then show ?thesis using g_def L_def by simp
qed



theorem freeIn_substNegInfinity : "freeIn var (substNegInfinity var A)"
  apply(cases A) using freeIn_altNegInf freeIn_allzero by simp_all


end
