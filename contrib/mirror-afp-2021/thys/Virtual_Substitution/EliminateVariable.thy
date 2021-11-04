subsection "Lemmas of the elimVar function"

theory EliminateVariable
  imports LinearCase QuadraticCase  "HOL-Library.Quadratic_Discriminant"
begin




lemma elimVar_eq :
  assumes hlength : "length xs = var"
  assumes in_list : "Eq p \<in> set(L)"
  assumes low_pow : "MPoly_Type.degree p var = 1 \<or> MPoly_Type.degree p var = 2"
  shows "((\<exists>x. eval (list_conj (map fm.Atom L @ F)) (xs @ x # \<Gamma>)) =
    ((\<exists>x. eval (elimVar var L F (Eq p)) (xs @ x # \<Gamma>)))\<or> (\<forall>x. aEval (Eq p) (xs @ x # \<Gamma>)))"
proof-

  { fix x
    define A where "A = (isolate_variable_sparse p var 2)"
    define B where "B = (isolate_variable_sparse p var 1)"
    define C where "C = (isolate_variable_sparse p var 0)"
    have freeA : "var \<notin> vars A"
      unfolding A_def
      by (simp add: not_in_isovarspar)
    have freeB : "var \<notin> vars B"
      unfolding B_def
      by (simp add: not_in_isovarspar)
    have freeC : "var \<notin> vars C"
      unfolding C_def
      by (simp add: not_in_isovarspar)
    assume "eval (list_conj (map fm.Atom L @ F)) (xs @ x # \<Gamma>)"
    then have h : "(\<forall>a\<in>set L. aEval a (xs @ x # \<Gamma>)) \<and> (\<forall>f\<in>set F. eval f (xs @ x # \<Gamma>))"
      apply(simp add:eval_list_conj)
      by (meson Un_iff eval.simps(1) image_eqI)
    define X where "X=xs@x#\<Gamma>"
    have Xlength : "length X > var"
      using X_def hlength by auto
    define Aval where "Aval = insertion (nth_default 0 (list_update X var x)) A"
    define Bval where "Bval = insertion (nth_default 0 (list_update X var x)) B"
    define Cval where "Cval = insertion (nth_default 0 (list_update X var x)) C"
    have hinsert : "(xs @ x # \<Gamma>)[var := x] = (xs @ x #\<Gamma>)"
      using hlength by auto
    have allAval : "\<forall>x. insertion (nth_default 0 (xs @ x # \<Gamma>)) A = Aval"
      using Aval_def
      using not_contains_insertion[where var="var", where p = "A", OF freeA, where L = "xs @ x #\<Gamma>", where x="x", where val="Aval"]
      unfolding X_def hinsert using hlength by auto
    have allBval : "\<forall>x. insertion (nth_default 0 (xs @ x # \<Gamma>)) B = Bval"
      using Bval_def
      using not_contains_insertion[where var="var", where p = "B", OF freeB, where L = "xs @ x #\<Gamma>", where x="x", where val="Bval"]
      unfolding X_def hinsert using hlength by auto
    have allCval : "\<forall>x. insertion (nth_default 0 (xs @ x # \<Gamma>)) C = Cval"
      using Cval_def
      using not_contains_insertion[where var="var", where p = "C", OF freeC, where L = "xs @ x #\<Gamma>", where x="x", where val="Cval"]
      unfolding X_def hinsert using hlength by auto
    have insertion_p : "insertion (nth_default 0 X) p = 0"
      using in_list h aEval.simps(1) X_def by fastforce
    have express_p : "p = A * Var var ^ 2 + B * Var var + C"
      using express_poly[OF low_pow] unfolding A_def B_def C_def
      by fastforce
    have insertion_p' : "Aval *x^2+Bval *x+Cval = 0"
      using express_p insertion_p unfolding Aval_def Bval_def Cval_def X_def hinsert
      apply(simp add: insertion_add insertion_mult insertion_pow)
      using  insertion_var by (metis X_def Xlength hinsert) 
    have biglemma : "
       ((Aval = 0 \<and>
        Bval \<noteq> 0 \<and>
        (\<forall>f\<in>set L. aEval (linear_substitution var (-C) B f) (xs @ x # \<Gamma>)) \<and> 
        (\<forall>f\<in>set F. eval (linear_substitution_fm var (-C) B f) (xs @ x # \<Gamma>)) \<or>
        Aval \<noteq> 0 \<and>
        insertion (nth_default 0 (xs @ x # \<Gamma>)) 4 * 
        Aval *
        Cval
        \<le> (Bval)\<^sup>2 \<and>
        ((\<forall>f\<in>set L. eval (quadratic_sub var (- B) 1 (B\<^sup>2 - 4 * A * C) (2 * A) f) (xs @ x # \<Gamma>))\<and>
         (\<forall>f\<in>set F. eval (quadratic_sub_fm var (- B) 1 (B\<^sup>2 - 4 * A * C) (2 * A) f) (xs @ x # \<Gamma>)) \<or>
         (\<forall>f\<in>set L. eval (quadratic_sub var (- B) (-1) (B\<^sup>2 - 4 * A * C) (2 * A) f) (xs @ x # \<Gamma>)) \<and>
         (\<forall>f\<in>set F. eval (quadratic_sub_fm var (- B) (-1) (B\<^sup>2 - 4 * A * C) (2 * A) f) (xs @ x # \<Gamma>))) \<or>
        Aval = 0 \<and>
        Bval = 0 \<and>
        Cval = 0))"
    proof(cases "Aval=0")
      case True
      then have aval0 : "Aval=0" by simp
      show ?thesis proof(cases "Bval=0")
        case True
        then have bval0 :  "Bval=0" by simp
        have h : "eval (list_conj (map fm.Atom L @ F)) (xs @ x # \<Gamma>)"
          using hlength h unfolding X_def
          using \<open>eval (list_conj (map fm.Atom L @ F)) (xs @ x # \<Gamma>)\<close> by blast
        show ?thesis proof(cases "Cval=0")
          case True
          show ?thesis                                  
            by(simp add:aval0 True bval0)
        next
          case False
          show ?thesis
            using insertion_p' aval0 bval0 False by(simp)
        qed
      next
        case False
        have bh : "insertion (nth_default 0 (X[var := - Cval / Bval])) B = Bval"
          using allBval unfolding X_def
          using Bval_def X_def freeB not_contains_insertion by blast
        have ch : "insertion (nth_default 0 (X[var := - Cval / Bval])) C = Cval"
          using allCval unfolding X_def
          using Cval_def X_def freeC not_contains_insertion by blast
        have xh : "x=-Cval/Bval"
        proof-
          have "Bval*x+Cval = 0"
            using insertion_p' aval0
            by simp
          then show ?thesis using False
            by (smt nonzero_mult_div_cancel_left)
        qed
        have freecneg : "var \<notin> vars (-C)" using freeC not_in_neg by auto
        have h1:  "(\<forall>a\<in>set L. aEval (linear_substitution var (-C) (B) a) (X[var := x]))"
          using h xh Bval_def Cval_def False LinearCase.linear[OF Xlength False freecneg freeB, of "-Cval"] freeB freeC freecneg
          by (metis X_def hinsert insertion_neg)
        have h2 : "\<forall>f\<in>set F. eval (linear_substitution_fm var (-C) B f) (X[var := x])"
          using h xh Bval_def Cval_def False LinearCase.linear_fm[OF Xlength False freecneg freeB, of "-Cval"] freeB freeC
          by (metis X_def hinsert insertion_neg)
        show ?thesis using h1 h2 apply(simp add:aval0 False)
          using X_def hlength
          using hinsert by auto
      qed
    next
      case False
      then have aval0 : "Aval \<noteq>0" by simp
      have h4 : "insertion (nth_default 0 (X[var := x])) 4 = 4"
        using insertion_const[where f = "(nth_default 0 (X[var := x]))", where c="4"]
        by (metis MPoly_Type.insertion_one insertion_add numeral_Bit0 one_add_one)
      show ?thesis proof(cases "4 * Aval * Cval \<le> Bval\<^sup>2")
        case True
        have h1a : "var\<notin>vars(-B)"
          by(simp add: freeB not_in_neg)
        have h1b : "var\<notin>vars(1::real mpoly)"
          using isolate_var_one not_in_isovarspar by blast
        have h1c : "var\<notin>vars(-1::real mpoly)"
          by(simp add: h1b not_in_neg)
        have h1d : "var\<notin>vars(4::real mpoly)"
          by (metis h1b not_in_add numeral_Bit0 one_add_one)
        have h1e : "var\<notin>vars(B^2-4*A*C)" 
          by(simp add: freeB h1d freeA freeC not_in_mult not_in_pow not_in_sub)
        have h1f : "var\<notin>vars(2::real mpoly)"
          using h1b not_in_add by fastforce
        have h1g : "var\<notin>vars(2*A)"
          by(simp add: freeA h1f not_in_mult)
        have h1h : "freeIn var (quadratic_sub var (-B) (1) (B^2-4*A*C) (2*A) a)"
          using free_in_quad h1a h1b h1e h1g by blast
        have h1i : "freeIn var (quadratic_sub var (-B) (-1) (B^2-4*A*C) (2*A) a)"
          using free_in_quad h1a h1c h1e h1g by blast 
        have h2 : "2*Aval \<noteq> 0" using aval0 by auto
        have h3 : "0 \<le> (Bval^2-4*Aval*Cval)" using True by auto
        have h4a : "var \<notin> vars 4"
          by (metis monom_numeral notInKeys_notInVars not_in_add not_in_isovarspar not_in_pow one_add_one power.simps(1) rel_simps(76) vars_monom_keys) 
        have h4 : "var \<notin> vars (B^2-4*A*C)" by(simp add: h4a freeA freeB freeC not_in_pow not_in_mult not_in_sub)  
        have h5 : "\<forall>x. insertion (nth_default 0 (list_update X var x)) (-B) = -Bval " 
          using allBval apply(simp add: insertion_neg)
          by (simp add: B_def Bval_def insertion_isovarspars_free)
        have h6 : "\<forall>x. insertion (nth_default 0 (list_update X var x)) 1 = 1" by simp
        have h6a : "\<forall>x. insertion (nth_default 0 (list_update X var x)) (-1) = (-1)" using h6 by (simp add: insertion_neg) 
        have h7a : "\<forall>x. insertion (nth_default 0 (list_update X var x)) 4 = 4" by (metis h6 insertion_add numeral_Bit0 one_add_one)
        have h7b : "var \<notin> vars(4*A*C)" using freeA freeC by (simp add: h4a not_in_mult) 
        have h7c : "var \<notin> vars(B^2)" using freeB not_in_pow by auto
        have h7 : "\<forall>x. insertion (nth_default 0 (list_update X var x)) (B^2-4*A*C) = (Bval^2-4*Aval*Cval)"
          using h7a allAval allBval allCval unfolding X_def  using hlength 
          apply (simp add: insertion_mult insertion_sub power2_eq_square)
          by (metis A_def Aval_def Bval_def C_def Cval_def X_def freeB insertion_isovarspars_free not_contains_insertion)
        have h8a : "\<forall>x. insertion (nth_default 0 (list_update X var x)) 2 = 2" by (metis h6 insertion_add one_add_one)
        have h8 : "\<forall>x. insertion (nth_default 0 (list_update X var x)) (2*A) = (2*Aval)"
          apply(simp add: allAval h8a insertion_mult)
          by (simp add: A_def Aval_def insertion_isovarspars_free)

        have h1 : "- Bval\<^sup>2 + 4 * Aval * Cval \<le> 0"
          using True by simp
        have xh : "x = (- Bval + sqrt (Bval\<^sup>2 - 4 * Aval * Cval)) / (2 * Aval)\<or>x=(- Bval - sqrt (Bval\<^sup>2 - 4 * Aval * Cval)) / (2 * Aval)"
          using insertion_p' aval0 h1
            discriminant_iff unfolding discrim_def by blast
        have p1 : "x = (- Bval + sqrt (Bval\<^sup>2 - 4 * Aval * Cval)) / (2 * Aval) \<Longrightarrow> 
                                                            ((\<forall>a\<in> set L. eval (quadratic_sub var (-B) 1 (B^2-4*A*C) (2*A) a) (X[var := x]))
                                                      \<and>(\<forall>a\<in> set F. eval (quadratic_sub_fm var (-B) 1 (B^2-4*A*C) (2*A) a) (X[var := x])))"
        proof-
          assume x_def : "x = (- Bval + sqrt (Bval\<^sup>2 - 4 * Aval * Cval)) / (2 * Aval)"
          then have h : "(\<forall>a\<in>set L. aEval a (X[var := (- Bval + sqrt (Bval\<^sup>2 - 4 * Aval * Cval)) / (2 * Aval)])) \<and> (\<forall>f\<in>set F. eval f (X[var := (- Bval + sqrt (Bval\<^sup>2 - 4 * Aval * Cval)) / (2 * Aval)]))"
            using h
            using X_def hinsert by auto
          { fix a
            assume in_list : "a\<in> set L"
            have "eval (quadratic_sub var (- B) 1 (B\<^sup>2 - 4 * A * C) (2 * A) a) (X[var := x])"
              using free_in_quad[where a="-B",where b="1", where c="(B^2-4*A*C)", where d="2*A",where var="var",OF h1a h1b h1e h1g]
              using quadratic_sub[where a="-B",where b="1", where c="(B^2-4*A*C)", where d="2*A",where var="var", where L="X", OF Xlength,
                  where Dv="2*Aval", OF h2, where Cv="(Bval^2-4*Aval*Cval)", OF h3, where Av="-Bval", OF h4 h5, where Bv="1", OF h6 h7 h8]
                  h in_list
              using var_not_in_eval by fastforce 

          }
          then have left : "(\<forall>a\<in>set L. eval (quadratic_sub var (- B) 1 (B\<^sup>2 - 4 * A * C) (2 * A) a) (X[var := x]))"
            by simp


          { fix a
            assume in_list : "a\<in> set F"
            have "eval (quadratic_sub_fm var (- B) 1 (B\<^sup>2 - 4 * A * C) (2 * A) a) (X[var := x])"
              using free_in_quad_fm[where a="-B",where b="1", where c="(B^2-4*A*C)", where d="2*A",where var="var",OF h1a h1b h1e h1g]
              using quadratic_sub_fm[where a="-B",where b="1", where c="(B^2-4*A*C)", where d="2*A",where var="var", where L="X", OF Xlength,
                  where Dv="2*Aval", OF h2, where Cv="(Bval^2-4*Aval*Cval)", OF h3, where Av="-Bval", OF h4 h5, where Bv="1", OF h6 h7 h8]
                  h in_list
              using var_not_in_eval by fastforce 

          }
          then have right : "(\<forall>a\<in>set F. eval (quadratic_sub_fm var (- B) 1 (B\<^sup>2 - 4 * A * C) (2 * A) a) (X[var := x]))"
            by simp
          show ?thesis
            using right left by simp
        qed

        have p2 : "x = (- Bval - sqrt (Bval\<^sup>2 - 4 * Aval * Cval)) / (2 * Aval) \<Longrightarrow> 
                                                            ((\<forall>a\<in> set L. eval (quadratic_sub var (-B) (-1) (B^2-4*A*C) (2*A) a) (X[var := x]))
                                                      \<and>(\<forall>a\<in> set F. eval (quadratic_sub_fm var (-B) (-1) (B^2-4*A*C) (2*A) a) (X[var := x])))"
        proof -
          assume x_def : "x = (- Bval - sqrt (Bval\<^sup>2 - 4 * Aval * Cval)) / (2 * Aval)"
          then have h : "(\<forall>a\<in>set L. aEval a (X[var := (- Bval - sqrt (Bval\<^sup>2 - 4 * Aval * Cval)) / (2 * Aval)])) \<and> (\<forall>f\<in>set F. eval f (X[var := (- Bval - sqrt (Bval\<^sup>2 - 4 * Aval * Cval)) / (2 * Aval)]))"
            using h
            using X_def hinsert by auto
          then have "(\<forall>a\<in>set L. aEval a (X[var := (- Bval - sqrt (Bval\<^sup>2 - 4 * Aval * Cval)) / (2 * Aval)])) \<and> (\<forall>f\<in>set F. eval f (X[var := (- Bval - sqrt (Bval\<^sup>2 - 4 * Aval * Cval)) / (2 * Aval)]))"
            using h  by simp
          { fix a
            assume in_list : "a\<in> set L"
            have "eval (quadratic_sub var (- B) (-1) (B\<^sup>2 - 4 * A * C) (2 * A) a) (X[var := x])"
              using free_in_quad[where a="-B",where b="-1", where c="(B^2-4*A*C)", where d="2*A",where var="var",OF h1a h1c h1e h1g]
              using quadratic_sub[where a="-B",where b="-1", where c="(B^2-4*A*C)", where d="2*A",where var="var", where L="X", OF Xlength,
                  where Dv="2*Aval", OF h2, where Cv="(Bval^2-4*Aval*Cval)", OF h3, where Av="-Bval", OF h4 h5, where Bv="-1", OF h6a h7 h8]
                  h in_list
              using var_not_in_eval by fastforce 

          }
          then have left : "(\<forall>a\<in>set L. eval (quadratic_sub var (- B) (-1) (B\<^sup>2 - 4 * A * C) (2 * A) a) (X[var := x]))"
            by simp


          { fix a
            assume in_list : "a\<in> set F"
            have "eval (quadratic_sub_fm var (- B) (-1) (B\<^sup>2 - 4 * A * C) (2 * A) a) (X[var := x])"
              using free_in_quad_fm[where a="-B",where b="-1", where c="(B^2-4*A*C)", where d="2*A",where var="var",OF h1a h1c h1e h1g]
              using quadratic_sub_fm[where a="-B",where b="-1", where c="(B^2-4*A*C)", where d="2*A",where var="var", where L="X", OF Xlength,
                  where Dv="2*Aval", OF h2, where Cv="(Bval^2-4*Aval*Cval)", OF h3, where Av="-Bval", OF h4 h5, where Bv="-1", OF h6a h7 h8]
                  h in_list
              using var_not_in_eval by fastforce 

          }
          then have right : "(\<forall>a\<in>set F. eval (quadratic_sub_fm var (- B) (-1) (B\<^sup>2 - 4 * A * C) (2 * A) a) (X[var := x]))"
            by simp
          show ?thesis
            using right left by simp
        qed
        have subst4 : "insertion (nth_default 0 (xs @ x # \<Gamma>)) 4 = 4" using h7a hlength X_def by auto 
        have disj: "(\<forall>a\<in>set L. eval (quadratic_sub var (- B) 1 (B\<^sup>2 - 4 * A * C) (2 * A) a) (xs @ x # \<Gamma>)) \<and>
                                                            (\<forall>a\<in>set F. eval (quadratic_sub_fm var (- B) 1 (B\<^sup>2 - 4 * A * C) (2 * A) a) (xs @ x # \<Gamma>)) \<or> 
                                                            (\<forall>a\<in>set L. eval (quadratic_sub var (- B) (-1) (B\<^sup>2 - 4 * A * C) (2 * A) a) (xs @ x # \<Gamma>)) \<and>
                                                            (\<forall>a\<in>set F. eval (quadratic_sub_fm var (- B) (-1) (B\<^sup>2 - 4 * A * C) (2 * A) a) (xs @ x # \<Gamma>))"
          using xh p1 p2
          unfolding X_def hinsert  by blast
        show ?thesis apply(simp add: aval0 True h7a subst4) using disj
          unfolding X_def hinsert by auto
      next
        case False
        then have det : "0 < - Bval\<^sup>2 + 4 * Aval * Cval"
          by simp
        show ?thesis apply(simp add: aval0 False h4) using discriminant_negative unfolding discrim_def
          using insertion_p'
          using aval0 det by auto 
      qed
    qed
    have "(\<exists>x.
       (insertion (nth_default 0 (xs @ x # \<Gamma>)) A = 0 \<and>
        insertion (nth_default 0 (xs @ x # \<Gamma>)) B \<noteq> 0 \<and>
        (\<forall>f\<in>set L. aEval (linear_substitution var (-C) (B) f) (xs @ x # \<Gamma>)) \<and> 
        (\<forall>f\<in>set F. eval (linear_substitution_fm var (-C) B f) (xs @ x # \<Gamma>)) \<or>
        insertion (nth_default 0 (xs @ x # \<Gamma>)) A \<noteq> 0 \<and>
        insertion (nth_default 0 (xs @ x # \<Gamma>)) 4 * 
        insertion (nth_default 0 (xs @ x # \<Gamma>)) A *
        insertion (nth_default 0 (xs @ x # \<Gamma>)) C
        \<le> (insertion (nth_default 0 (xs @ x # \<Gamma>)) B)\<^sup>2 \<and>
        ((\<forall>f\<in>set L. eval (quadratic_sub var (- B) 1 (B\<^sup>2 - 4 * A * C) (2 * A) f) (xs @ x # \<Gamma>))\<and>
         (\<forall>f\<in>set F. eval (quadratic_sub_fm var (- B) 1 (B\<^sup>2 - 4 * A * C) (2 * A) f) (xs @ x # \<Gamma>)) \<or>
         (\<forall>f\<in>set L. eval (quadratic_sub var (- B) (-1) (B\<^sup>2 - 4 * A * C) (2 * A) f) (xs @ x # \<Gamma>)) \<and>
         (\<forall>f\<in>set F. eval (quadratic_sub_fm var (- B) (-1) (B\<^sup>2 - 4 * A * C) (2 * A) f) (xs @ x # \<Gamma>)))) \<or>
        (Aval = 0 \<and>
        Bval = 0 \<and>
        Cval = 0))"
      apply(rule exI[where x=x])
      using biglemma
      using allAval allBval allCval unfolding A_def B_def C_def Aval_def Bval_def Cval_def X_def hinsert
      by auto
    then obtain x where x : "(insertion (nth_default 0 (xs @ x # \<Gamma>)) A = 0 \<and>
        insertion (nth_default 0 (xs @ x # \<Gamma>)) B \<noteq> 0 \<and>
        (\<forall>f\<in>set L. aEval (linear_substitution var (-C) (B) f) (xs @ x # \<Gamma>)) \<and> 
        (\<forall>f\<in>set F. eval (linear_substitution_fm var (-C) B f) (xs @ x # \<Gamma>)) \<or>
        insertion (nth_default 0 (xs @ x # \<Gamma>)) A \<noteq> 0 \<and>
        insertion (nth_default 0 (xs @ x # \<Gamma>)) 4 * 
        insertion (nth_default 0 (xs @ x # \<Gamma>)) A *
        insertion (nth_default 0 (xs @ x # \<Gamma>)) C
        \<le> (insertion (nth_default 0 (xs @ x # \<Gamma>)) B)\<^sup>2 \<and>
        ((\<forall>f\<in>set L. eval (quadratic_sub var (- B) 1 (B\<^sup>2 - 4 * A * C) (2 * A) f) (xs @ x # \<Gamma>))\<and>
         (\<forall>f\<in>set F. eval (quadratic_sub_fm var (- B) 1 (B\<^sup>2 - 4 * A * C) (2 * A) f) (xs @ x # \<Gamma>)) \<or>
         (\<forall>f\<in>set L. eval (quadratic_sub var (- B) (-1) (B\<^sup>2 - 4 * A * C) (2 * A) f) (xs @ x # \<Gamma>)) \<and>
         (\<forall>f\<in>set F. eval (quadratic_sub_fm var (- B) (-1) (B\<^sup>2 - 4 * A * C) (2 * A) f) (xs @ x # \<Gamma>)))) \<or>
        (Aval = 0 \<and>
        Bval = 0 \<and>
        Cval = 0)" by auto
    have h : "(\<exists>x. eval (elimVar var L F (Eq p)) (xs @ x # \<Gamma>))\<or>(Aval = 0 \<and> Bval = 0 \<and> Cval = 0)"
    proof(cases "(Aval = 0 \<and> Bval = 0 \<and> Cval = 0)")
      case True
      then show ?thesis by simp
    next
      case False
      have "(\<exists>x. eval (elimVar var L F (Eq p)) (xs @ x # \<Gamma>))"
        apply(rule exI[where x=x])
        apply(simp add: eval_list_conj insertion_mult insertion_sub insertion_pow insertion_add 
            del:  quadratic_sub.simps linear_substitution.simps quadratic_sub_fm.simps linear_substitution_fm.simps)
        unfolding A_def[symmetric] B_def[symmetric] C_def[symmetric] One_nat_def[symmetric] X_def[symmetric]
        using hlength x
        by (auto simp add:False)
      then show ?thesis by auto
    qed
    have "(\<exists>x. eval (elimVar var L F (Eq p)) (xs @ x # \<Gamma>))\<or>(\<forall>x. aEval (Eq p) (xs@ x# \<Gamma>))"
    proof(cases "(\<exists>x. eval (elimVar var L F (Eq p)) (xs @ x # \<Gamma>))")
      case True
      then show ?thesis by auto
    next
      case False
      then have "(Aval = 0 \<and> Bval = 0 \<and> Cval = 0)"
        using h by auto
      then have "(\<forall>x. aEval (Eq p) (xs @ x # \<Gamma>))"
        unfolding express_p
        apply(simp add:insertion_add insertion_mult insertion_pow)
        using allAval allBval allCval by auto 
      then show ?thesis by auto
    qed
  }
  then have left : "(\<exists>x. eval (list_conj (map fm.Atom L @ F)) (xs @ x # \<Gamma>)) \<Longrightarrow>
                        ((\<exists>x. eval (elimVar var L F (Eq p)) (xs @ x # \<Gamma>))\<or>(\<forall>x. aEval (Eq p) (xs@ x# \<Gamma>)))"
    by blast


  {
    assume hlength : "length (xs::real list) = var"
    define A where "A = (isolate_variable_sparse p var 2)"
    define B where "B = (isolate_variable_sparse p var 1)"
    define C where "C = (isolate_variable_sparse p var 0)"
    have freeA : "var \<notin> vars A"
      unfolding A_def
      by (simp add: not_in_isovarspar)
    have freeB : "var \<notin> vars B"
      unfolding B_def
      by (simp add: not_in_isovarspar)
    have freeC : "var \<notin> vars C"
      unfolding C_def
      by (simp add: not_in_isovarspar)
    have express_p : "p = A*(Var var)^2+B*(Var var)+C"
      using express_poly[OF low_pow] unfolding A_def B_def C_def
      by fastforce
    assume h : "(\<exists>x. (eval (elimVar var L F (Eq p)) (list_update (xs@x#\<Gamma>) var x)))"
    fix x
    define X where "X=xs@x#\<Gamma>"
    have Xlength : "length X > var"
      using X_def hlength by auto
    define Aval where "Aval = insertion (nth_default 0 (list_update X var x)) A"
    define Bval where "Bval = insertion (nth_default 0 (list_update X var x)) B"
    define Cval where "Cval = insertion (nth_default 0 (list_update X var x)) C"
    have allAval : "\<forall>x. insertion (nth_default 0 (list_update X var x)) A = Aval"
      using freeA Aval_def
      using not_contains_insertion by blast
    have allBval : "\<forall>x. insertion (nth_default 0 (list_update X var x)) B = Bval"
      using freeB Bval_def
      using not_contains_insertion by blast
    have allCval : "\<forall>x. insertion (nth_default 0 (list_update X var x)) C = Cval"
      using freeC Cval_def
      using not_contains_insertion by blast
    assume "(eval (elimVar var L F (Eq p)) (list_update (xs@x#\<Gamma>) var x))"
    then have h : "(eval (elimVar var L F (Eq p)) (list_update X var x))"
      unfolding X_def .

    have "(Aval = 0 \<and> Bval \<noteq> 0 \<and>
          (\<forall>f\<in>(\<lambda>a. Atom(linear_substitution var (-C) B a)) ` set L \<union>
             linear_substitution_fm var (-C) B `
             set F.
            eval f (X[var := x])) \<or>
          Aval \<noteq> 0 \<and>
          insertion (nth_default 0 (X[var := x])) 4 * Aval * Cval  \<le> Bval\<^sup>2 \<and>
          ((\<forall>f\<in>(quadratic_sub var (-B) 1 (B^2-4*A*C) (2*A)) `
             set L \<union>
             (quadratic_sub_fm var (-B) 1 (B^2-4*A*C) (2*A)) `
             set F.
            eval f (X[var := x]))
          \<or>(\<forall>f\<in>(quadratic_sub var (-B) (-1) (B^2-4*A*C) (2*A)) `
             set L \<union>
             (quadratic_sub_fm var (-B) (-1) (B^2-4*A*C) (2*A)) `
             set F.
            eval f (X[var := x]))
          ))"
      unfolding Aval_def Bval_def Cval_def A_def B_def C_def
      using h by(simp add: eval_list_conj insertion_mult insertion_sub insertion_pow insertion_add insertion_var Xlength)
    then have h : "(Aval = 0 \<and> Bval \<noteq> 0 \<and>
                            ((\<forall>a\<in> set L. aEval (linear_substitution var (-C) B a) (X[var := x])) \<and>
                            (\<forall>a\<in> set F. eval (linear_substitution_fm var (-C) B a) (X[var := x]))) \<or>
                            Aval \<noteq> 0 \<and> insertion (nth_default 0 (X[var := x])) 4 * Aval * Cval \<le> Bval\<^sup>2 \<and>
                            (((\<forall>a\<in> set L. eval (quadratic_sub var (-B) 1 (B^2-4*A*C) (2*A) a) (X[var := x]))
                            \<and>(\<forall>a\<in> set F. eval (quadratic_sub_fm var (-B) 1 (B^2-4*A*C) (2*A) a) (X[var := x])))
                            \<or>((\<forall>a\<in> set L. eval (quadratic_sub var (-B) (-1) (B^2-4*A*C) (2*A) a) (X[var := x]))
                            \<and>(\<forall>a\<in> set F. eval (quadratic_sub_fm var (-B) (-1) (B^2-4*A*C) (2*A) a) (X[var := x])))))
                          "
      apply(cases "Aval = 0 ")
      apply auto
      by (meson Un_iff eval.simps(1) imageI)
    have h : "(\<exists>x. ((\<forall>a\<in>set L . aEval a ((xs@x#\<Gamma>)[var := x])) \<and> (\<forall>f\<in>set F. eval f ((xs@x#\<Gamma>)[var := x]))))\<or>(Aval=0\<and>Bval=0\<and>Cval=0)"
    proof(cases "Aval=0")
      case True
      then have aval0 : "Aval=0"
        by simp
      show ?thesis proof(cases "Bval = 0")
        case True
        then have bval0 : "Bval = 0" by simp
        show ?thesis proof(cases "Cval=0")
          case True
          then show ?thesis using aval0 bval0 True by auto
        next
          case False
          then show ?thesis using h by(simp add:aval0 bval0 False)
        qed 
      next
        case False
        have hb :  "insertion (nth_default 0 (X[var := - Cval / Bval])) B = Bval"
          using allBval by simp
        have hc : "insertion (nth_default 0 (X[var := - Cval / Bval])) (-C) = -Cval"
          using allCval
          by (simp add: insertion_neg) 
        have freecneg : "var\<notin>vars(-C)" using freeC not_in_neg by auto
        have p1 : "(\<forall>a\<in>set L. aEval a ((xs @ x # \<Gamma>)[var := - Cval / Bval]))"
          using h apply(simp add: False aval0)
          using linear[OF Xlength False freecneg freeB hc hb]
            list_update_length var_not_in_linear[OF freecneg freeB]
          unfolding X_def using hlength
          by (metis divide_minus_left)

        have p2 : "(\<forall>a\<in>set F. eval a ((xs @ x # \<Gamma>)[var := - Cval / Bval]))"
          using h apply(simp add: False aval0)
          using linear_fm[OF Xlength False freecneg freeB hc hb]
            list_update_length var_not_in_linear_fm[OF freecneg freeB]
          unfolding X_def using hlength var_not_in_eval
          by (metis divide_minus_left linear_substitution_fm.elims linear_substitution_fm_helper.elims)
        show ?thesis 
          using p1 p2 hlength by fastforce
      qed
    next
      case False
      then have aval0 : "Aval \<noteq> 0"
        by simp
      have h4 : "insertion (nth_default 0 (X[var := x])) 4 = 4"
        using insertion_const[where f = "(nth_default 0 (X[var := x]))", where c="4"]
        by (metis MPoly_Type.insertion_one insertion_add numeral_Bit0 one_add_one)
      show ?thesis proof(cases "4 * Aval * Cval \<le> Bval\<^sup>2")
        case True
        then have h1 :  "- Bval\<^sup>2 + 4 * Aval * Cval \<le> 0"
          by simp
        have h : "(((\<forall>a\<in> set L. eval (quadratic_sub var (-B) 1 (B^2-4*A*C) (2*A) a) (X[var := x]))
                        \<and>(\<forall>a\<in> set F. eval (quadratic_sub_fm var (-B) 1 (B^2-4*A*C) (2*A) a) (X[var := x])))
                        \<or>((\<forall>a\<in> set L. eval (quadratic_sub var (-B) (-1) (B^2-4*A*C) (2*A) a) (X[var := x]))
                        \<and>(\<forall>a\<in> set F. eval (quadratic_sub_fm var (-B) (-1) (B^2-4*A*C) (2*A) a) (X[var := x]))))"
          using h by(simp add: h1 aval0)
        have h1a : "var\<notin>vars(-B)"
          by(simp add: freeB not_in_neg)
        have h1b : "var\<notin>vars(1::real mpoly)"
          using isolate_var_one not_in_isovarspar by blast
        have h1c : "var\<notin>vars(-1::real mpoly)"
          by(simp add: h1b not_in_neg)
        have h1d : "var\<notin>vars(4::real mpoly)"
          by (metis h1b not_in_add numeral_Bit0 one_add_one)
        have h1e : "var\<notin>vars(B^2-4*A*C)" 
          by(simp add: freeB h1d freeA freeC not_in_mult not_in_pow not_in_sub)
        have h1f : "var\<notin>vars(2::real mpoly)"
          using h1b not_in_add by fastforce
        have h1g : "var\<notin>vars(2*A)"
          by(simp add: freeA h1f not_in_mult)
        have h1h : "freeIn var (quadratic_sub var (-B) (1) (B^2-4*A*C) (2*A) a)"
          using free_in_quad h1a h1b h1e h1g by blast
        have h1i : "freeIn var (quadratic_sub var (-B) (-1) (B^2-4*A*C) (2*A) a)"
          using free_in_quad h1a h1c h1e h1g by blast 
        have h2 : "2*Aval \<noteq> 0" using aval0 by auto
        have h3 : "0 \<le> (Bval^2-4*Aval*Cval)" using True by auto
        have h4a : "var \<notin> vars 4"
          by (metis monom_numeral notInKeys_notInVars not_in_add not_in_isovarspar not_in_pow one_add_one power.simps(1) rel_simps(76) vars_monom_keys) 
        have h4 : "var \<notin> vars (B^2-4*A*C)" by(simp add: h4a freeA freeB freeC not_in_pow not_in_mult not_in_sub)  
        have h5 : "\<forall>x. insertion (nth_default 0 (list_update X var x)) (-B) = -Bval " using allBval by(simp add: insertion_neg)
        have h6 : "\<forall>x. insertion (nth_default 0 (list_update X var x)) 1 = 1" by simp
        have h6a : "\<forall>x. insertion (nth_default 0 (list_update X var x)) (-1) = (-1)" using h6 by (simp add: insertion_neg) 
        have h7a : "\<forall>x. insertion (nth_default 0 (list_update X var x)) 4 = 4" by (metis h6 insertion_add numeral_Bit0 one_add_one)
        have h7b : "var \<notin> vars(4*A*C)" using freeA freeC by (simp add: h4a not_in_mult) 
        have h7c : "var \<notin> vars(B^2)" using freeB not_in_pow by auto
        have h7 : "\<forall>x. insertion (nth_default 0 (list_update X var x)) (B^2-4*A*C) = (Bval^2-4*Aval*Cval)"
          by (simp add: h7a allAval allBval allCval insertion_mult insertion_sub power2_eq_square)
        have h8a : "\<forall>x. insertion (nth_default 0 (list_update X var x)) 2 = 2" by (metis h6 insertion_add one_add_one)
        have h8 : "\<forall>x. insertion (nth_default 0 (list_update X var x)) (2*A) = (2*Aval)" by(simp add: allAval h8a insertion_mult)

        have p1 : "(\<forall>a\<in> set L. eval (quadratic_sub var (-B) 1 (B^2-4*A*C) (2*A) a) (X[var := x]))
                        \<Longrightarrow>(\<forall>a\<in> set F. eval (quadratic_sub_fm var (-B) 1 (B^2-4*A*C) (2*A) a) (X[var := x]))
                          \<Longrightarrow> \<exists>x. length xs = var \<and> ((\<forall>a\<in>set L . aEval a ((xs@x#\<Gamma>)[var := x])) \<and> (\<forall>f\<in>set F. eval f ((xs@x#\<Gamma>)[var := x])))"
        proof-
          assume p1 : "(\<forall>a\<in> set L. eval (quadratic_sub var (-B) 1 (B^2-4*A*C) (2*A) a) (X[var := x]))"
          assume p2 : "(\<forall>a\<in> set F. eval (quadratic_sub_fm var (-B) 1 (B^2-4*A*C) (2*A) a) (X[var := x]))"
          show ?thesis
            using free_in_quad[where a="-B",where b="1", where c="(B^2-4*A*C)", where d="2*A",where var="var",OF h1a h1b h1e h1g]
            using quadratic_sub[where a="-B",where b="1", where c="(B^2-4*A*C)", where d="2*A",where var="var", where L="X", OF Xlength,
                where Dv="2*Aval", OF h2, where Cv="(Bval^2-4*Aval*Cval)", OF h3, where Av="-Bval", OF h4 h5, where Bv="1", OF h6 h7 h8]
            using free_in_quad_fm[where a="-B",where b="1", where c="(B^2-4*A*C)", where d="2*A",where var="var",OF h1a h1b h1e h1g]
            using quadratic_sub_fm[where a="-B",where b="1", where c="(B^2-4*A*C)", where d="2*A",where var="var", where L="X", OF Xlength,
                where Dv="2*Aval", OF h2, where Cv="(Bval^2-4*Aval*Cval)", OF h3, where Av="-Bval", OF h4 h5, where Bv="1", OF h6 h7 h8]
                p1 p2
            using var_not_in_eval
            by (metis X_def hlength list_update_length)
        qed
        have p2 : "(\<forall>a\<in> set L. eval (quadratic_sub var (-B) (-1) (B^2-4*A*C) (2*A) a) (X[var := x]))
                        \<Longrightarrow>(\<forall>a\<in> set F. eval (quadratic_sub_fm var (-B) (-1) (B^2-4*A*C) (2*A) a) (X[var := x]))
                          \<Longrightarrow>\<exists>x. length xs = var \<and> ((\<forall>a\<in>set L . aEval a ((xs@x#\<Gamma>)[var := x])) \<and> (\<forall>f\<in>set F. eval f ((xs@x#\<Gamma>)[var := x])))"
          using free_in_quad[where a="-B",where b="-1", where c="(B^2-4*A*C)", where d="2*A",where var="var",OF h1a h1c h1e h1g]
          using quadratic_sub[where a="-B",where b="-1", where c="(B^2-4*A*C)", where d="2*A",where var="var", where L="X", OF Xlength,
              where Dv="2*Aval", OF h2, where Cv="(Bval^2-4*Aval*Cval)", OF h3, where Av="-Bval", OF h4 h5, where Bv="-1", OF h6a h7 h8]

          using free_in_quad_fm[where a="-B",where b="-1", where c="(B^2-4*A*C)", where d="2*A",where var="var",OF h1a h1c h1e h1g]
          using quadratic_sub_fm[where a="-B",where b="-1", where c="(B^2-4*A*C)", where d="2*A",where var="var", where L="X", OF Xlength,
              where Dv="2*Aval", OF h2, where Cv="(Bval^2-4*Aval*Cval)", OF h3, where Av="-Bval", OF h4 h5, where Bv="-1", OF h6a h7 h8]

          using var_not_in_eval by (metis X_def hlength list_update_length)
        then show ?thesis
          using h p1 p2 by blast
      next
        case False
        then show ?thesis using h by(simp add: aval0 False h4)
      qed
    qed
    have "(\<exists>x.((\<forall>a\<in>set L . aEval a ((xs@x#\<Gamma>)[var := x])) \<and> (\<forall>f\<in>set F. eval f ((xs@x#\<Gamma>)[var := x]))))\<or>(\<forall>x. aEval (Eq p) (xs @ x#\<Gamma>))"
    proof(cases "(\<exists>x.((\<forall>a\<in>set L . aEval a ((xs@x#\<Gamma>)[var := x])) \<and> (\<forall>f\<in>set F. eval f ((xs@x#\<Gamma>)[var := x]))))")
      case True
      then show ?thesis by auto
    next
      case False
      then have "Aval=0\<and>Bval=0\<and>Cval=0" using h by auto
      then have "(\<forall>x. aEval (Eq p) (xs @ x # \<Gamma>))"
        unfolding express_p apply(simp add:insertion_add insertion_mult insertion_pow)
        using allAval allBval allCval hlength unfolding X_def by auto
      then show ?thesis by auto
    qed
  }


  then have right : "(\<exists>x. eval (elimVar var L F (Eq p)) (xs @ x # \<Gamma>)) \<Longrightarrow>
               ((\<exists>x. eval (list_conj (map fm.Atom L @ F)) (xs @ x # \<Gamma>))\<or>(\<forall>x. aEval (Eq p) (xs @ x # \<Gamma>)))"
    by (smt UnE eval.simps(1) eval_list_conj hlength imageE list_update_length set_append set_map)


  show ?thesis using right left by blast
qed

text "simply states that the variable is free in the equality case of the elimVar function"
lemma freeIn_elimVar_eq : "freeIn var (elimVar var L F (Eq p))"
proof-
  have h4 : "var \<notin> vars(4:: real mpoly)" using var_not_in_Const
    by (metis (full_types) isolate_var_one monom_numeral not_in_isovarspar numeral_One vars_monom_keys zero_neq_numeral)
  have hlinear: "\<forall>f\<in>set(map (\<lambda>a. Atom(linear_substitution var (-isolate_variable_sparse p var 0) (isolate_variable_sparse p var (Suc 0)) a)) L @
        map (linear_substitution_fm var (-isolate_variable_sparse p var 0) (isolate_variable_sparse p var (Suc 0)))
         F). freeIn var f" 
    using
      var_not_in_linear[where c="(isolate_variable_sparse p var (Suc 0))", where b="(- isolate_variable_sparse p var 0)", where var="var"]
      var_not_in_linear_fm[where c="(isolate_variable_sparse p var (Suc 0))", where b="(-isolate_variable_sparse p var 0)", where var="var"]
      not_in_isovarspar not_in_neg by auto
  have freeA : "var \<notin> vars (- isolate_variable_sparse p var (Suc 0))"
    using not_in_isovarspar not_in_neg by auto
  have freeB1 : "var \<notin> vars (1::real mpoly)"
    by (metis h4 monom_numeral monom_one notInKeys_notInVars vars_monom_keys zero_neq_numeral)
  have freeC : "var \<notin> vars (((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
                    4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0))"
    using not_in_isovarspar not_in_pow not_in_sub not_in_mult h4 by auto
  have freeD : "var \<notin> vars ((2 * isolate_variable_sparse p var 2))"
    using not_in_isovarspar not_in_mult
    by (metis mult_2 not_in_add) 
  have freeB2 : "var\<notin>vars (-1::real mpoly)"
    using freeB1 not_in_neg by auto
  have quadratic1 : "\<forall>f\<in>set(map (quadratic_sub var (- isolate_variable_sparse p var (Suc 0)) 1
              ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
               4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)
              (2 * isolate_variable_sparse p var 2))
         L @
        map (quadratic_sub_fm var (- isolate_variable_sparse p var (Suc 0)) 1
              ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
               4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)
              (2 * isolate_variable_sparse p var 2))
         F). freeIn var f" 
    using free_in_quad[OF freeA freeB1 freeC freeD]
      free_in_quad_fm[OF freeA freeB1 freeC freeD] by auto
  have quadratic2 : "\<forall>f\<in>set(map (quadratic_sub var (- isolate_variable_sparse p var (Suc 0)) (-1)
              ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
               4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)
              (2 * isolate_variable_sparse p var 2))
         L @
        map (quadratic_sub_fm var (- isolate_variable_sparse p var (Suc 0)) (-1)
              ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
               4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)
              (2 * isolate_variable_sparse p var 2))
         F). freeIn var f"
    using free_in_quad[OF freeA freeB2 freeC freeD]
      free_in_quad_fm[OF freeA freeB2 freeC freeD] by auto
  show ?thesis
    using not_in_mult not_in_add h4 not_in_pow not_in_sub freeIn_list_conj not_in_isovarspar hlinear quadratic1 quadratic2
    by(simp add: )
qed


text "Theorem 20.2 in the textbook"
lemma elimVar_eq_2 :
  assumes hlength : "length xs = var"
  assumes in_list : "Eq p \<in> set(L)"
  assumes low_pow : "MPoly_Type.degree p var = 1 \<or> MPoly_Type.degree p var = 2"
  assumes nonzero : "\<forall>x. 
              insertion (nth_default 0 (xs @ x # \<Gamma>)) (isolate_variable_sparse p var 2) \<noteq> 0
            \<or> insertion (nth_default 0 (xs @ x # \<Gamma>)) (isolate_variable_sparse p var 1) \<noteq> 0
            \<or> insertion (nth_default 0 (xs @ x # \<Gamma>)) (isolate_variable_sparse p var 0) \<noteq> 0" (is ?non0)
  shows "(\<exists>x. eval (list_conj (map fm.Atom L @ F)) (xs @ x # \<Gamma>)) =
         (\<exists>x. eval (elimVar var L F (Eq p)) (xs @ x # \<Gamma>))"
proof-
  define A where "A = (isolate_variable_sparse p var 2)"
  define B where "B = (isolate_variable_sparse p var 1)"
  define C where "C = (isolate_variable_sparse p var 0)"
  have freeA : "var \<notin> vars A"
    unfolding A_def
    by (simp add: not_in_isovarspar)
  have freeB : "var \<notin> vars B"
    unfolding B_def
    by (simp add: not_in_isovarspar)
  have freeC : "var \<notin> vars C"
    unfolding C_def
    by (simp add: not_in_isovarspar)
  have express_p : "p = A*(Var var)^2+B*(Var var)+C"
    using express_poly[OF low_pow] unfolding A_def B_def C_def
    by fastforce
  have af : "isolate_variable_sparse p var 2 = A"
    using A_def by auto
  have bf : "isolate_variable_sparse p var (Suc 0) = B"
    using B_def by auto
  have cf : "isolate_variable_sparse p var 0 = C"
    using C_def by auto
  have xlength : "\<forall>x. (insertion (nth_default 0 (xs @ x # \<Gamma>)) (Var var))= x" 
    using hlength insertion_var
    by (metis add.commute add_strict_increasing length_append length_greater_0_conv list.distinct(1) list_update_id nth_append_length order_refl)
  fix x
  define c where "c i = (insertion (nth_default 0 (xs @ x # \<Gamma>)) (isolate_variable_sparse p var i))" for i
  have c2 : "\<forall>x. insertion (nth_default 0 (xs @ x # \<Gamma>)) A = c 2" 
    using freeA apply(simp add: A_def c_def)
    by (simp add: hlength insertion_lowerPoly1)
  have c1 : "\<forall>x. insertion (nth_default 0 (xs @ x # \<Gamma>)) B = c 1"
    using freeB apply(simp add: B_def c_def)
    by (simp add: hlength insertion_lowerPoly1)
  have c0 : "\<forall>x. insertion (nth_default 0 (xs @ x # \<Gamma>)) C = c 0"
    using freeC apply(simp add: C_def c_def)
    by (simp add: hlength insertion_lowerPoly1)
  have sum : "\<forall>x. c 2 * x\<^sup>2 + c (Suc 0) * x + c 0 = (\<Sum>i\<le>2. c i * x ^ i)"
    by (simp add: numerals(2))
  have "(\<forall>x. aEval (Eq p) (xs @ x # \<Gamma>)) = (\<not>?non0)"
    apply(simp add : af bf cf)
    unfolding express_p apply(simp add:insertion_add insertion_mult insertion_pow xlength)
    apply(simp add:c2 c1 c0)
    apply(simp add: sum)
    using polyfun_eq_0[where c="c", where n="2"]
    using sum by auto
  then have "\<not>(\<forall>x. aEval (Eq p) (xs @ x \<Gamma>))"
    using nonzero by auto
  then show ?thesis
    using disjE[OF elimVar_eq[OF hlength in_list, where F="F", where \<Gamma>="\<Gamma>"], where R="?thesis"]
    using \<open>(\<forall>x. aEval (Eq p) (xs @ x # \<Gamma>)) = (\<not> (\<forall>x. insertion (nth_default 0 (xs @ x # \<Gamma>)) (isolate_variable_sparse p var 2) \<noteq> 0 \<or> insertion (nth_default 0 (xs @ x # \<Gamma>)) (isolate_variable_sparse p var 1) \<noteq> 0 \<or> insertion (nth_default 0 (xs @ x # \<Gamma>)) (isolate_variable_sparse p var 0) \<noteq> 0))\<close> low_pow nonzero by blast
qed



end