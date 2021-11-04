subsection "Overall Equality VS Proofs"
theory EqualityVS
  imports EliminateVariable LuckyFind
begin


lemma degree_find_eq :
  assumes "find_eq var L = (A,L')"
  shows "\<forall>p\<in>set(A). MPoly_Type.degree p var = 1 \<or> MPoly_Type.degree p var = 2" using assms(1)
proof(induction L arbitrary: A L')
  case Nil
  then show ?case by auto
next
  case (Cons a L)
  then show ?case proof(cases a)
    case (Less p)
    {fix A' L' 
      assume h : "find_eq var L = (A', L')"
      have "A=A'"
        using Less Cons h by(simp)
      then have "\<forall>p\<in>set A. MPoly_Type.degree p var = 1 \<or> MPoly_Type.degree p var = 2"
        using Cons h by auto
    }
    then show ?thesis by (meson surj_pair)
  next
    case (Eq p)
    then show ?thesis proof(cases "MPoly_Type.degree p var = 1 \<or> MPoly_Type.degree p var = 2")
      case True
      {fix A' L' 
        assume h : "find_eq var L = (A', L')"
        have "A= (p#A')"
          using Eq Cons h True by auto
        then have "\<forall>p\<in>set A. MPoly_Type.degree p var = 1 \<or> MPoly_Type.degree p var = 2"
          using Cons h True by auto
      }
      then show ?thesis by (meson surj_pair)
    next
      case False
      {fix A' L' 
        assume h : "find_eq var L = (A', L')"
        have "A=A'"
          using Eq Cons h False
          by (smt One_nat_def case_prod_conv find_eq.simps(3) less_2_cases less_SucE numeral_2_eq_2 numeral_3_eq_3 prod.sel(1))
        then have "\<forall>p\<in>set A. MPoly_Type.degree p var = 1 \<or> MPoly_Type.degree p var = 2"
          using Cons h by auto
      }
      then show ?thesis by (meson surj_pair)
    qed
  next
    case (Leq p)
    {fix A' L' 
      assume h : "find_eq var L = (A', L')"
      have "A=A'"
        using Leq Cons h by(simp)
      then have "\<forall>p\<in>set A. MPoly_Type.degree p var = 1 \<or> MPoly_Type.degree p var = 2"
        using Cons h by auto
    }
    then show ?thesis by (meson surj_pair)
  next
    case (Neq p)
    {fix A' L' 
      assume h : "find_eq var L = (A', L')"
      have "A=A'"
        using Neq Cons h by(simp)
      then have "\<forall>p\<in>set A. MPoly_Type.degree p var = 1 \<or> MPoly_Type.degree p var = 2"
        using Cons h by auto
    }
    then show ?thesis by (meson surj_pair)
  qed
qed

lemma list_in_find_eq :
  assumes "find_eq var L = (A,L')"
  shows "set(map Eq A @ L') = set L"using assms(1)
proof(induction L arbitrary: A L')
  case Nil
  then show ?case by auto
next
  case (Cons a L)
  then show ?case proof(cases a)
    case (Less p)
    {fix A' L'' 
      assume h : "find_eq var L = (A', L'')"
      have A : "A=A'"
        using Less Cons h by(simp)
      have L : "L'=Less p # L''"
        using Less Cons h by simp
      have "set (map Eq A @ L') = set (a # L)"
        apply(simp add: A L Less) using Cons(1)[OF h] by auto
    }
    then show ?thesis by (meson surj_pair)
  next
    case (Eq p)
    then show ?thesis proof(cases "MPoly_Type.degree p var = 1 \<or> MPoly_Type.degree p var = 2")
      case True
      {fix A' L'' 
        assume h : "find_eq var L = (A', L'')"
        have A : "A=(p#A')"
          using Eq Cons h True by auto
        have L : "L'= L''"
          using Eq Cons h True by auto 
        have "set (map Eq A @ L') = set (a # L)"
          apply(simp add: A L Eq) using Cons(1)[OF h] by auto
      }
      then show ?thesis by (meson surj_pair)
    next
      case False
      {fix A' L'' 
        assume h : "find_eq var L = (A', L'')"
        have A : "A=A'"
          using Eq Cons h False
          by (smt case_prod_conv degree_find_eq find_eq.simps(3) list.set_intros(1) prod.sel(1))
        have L : "L'=Eq p # L''"
          using Eq Cons h
          by (smt A case_prod_conv find_eq.simps(3) not_Cons_self2 prod.sel(1) prod.sel(2)) 
        have "set (map Eq A @ L') = set (a # L)"
          apply(simp add: A L Eq) using Cons(1)[OF h] by auto
      }
      then show ?thesis by (meson surj_pair)
    qed
  next
    case (Leq p)
    {fix A' L'' 
      assume h : "find_eq var L = (A', L'')"
      have A : "A=A'"
        using Leq Cons h by(simp)
      have L : "L'=Leq p # L''"
        using Leq Cons h by simp
      have "set (map Eq A @ L') = set (a # L)"
        apply(simp add: A L Leq) using Cons(1)[OF h] by auto
    }
    then show ?thesis by (meson surj_pair)
  next
    case (Neq p)
    {fix A' L'' 
      assume h : "find_eq var L = (A', L'')"
      have A : "A=A'"
        using Neq Cons h by(simp)
      have L : "L'=Neq p # L''"
        using Neq Cons h by simp
      have "set (map Eq A @ L') = set (a # L)"
        apply(simp add: A L Neq) using Cons(1)[OF h] by auto
    }
    then show ?thesis by (meson surj_pair)
  qed
qed


lemma qe_eq_one_eval :
  assumes hlength : "length xs = var"
  shows "(\<exists>x. (eval (list_conj ((map Atom L) @ F)) (xs @ (x#\<Gamma>)))) = (\<exists>x.(eval (qe_eq_one var L F) (xs @ (x#\<Gamma>))))"
proof(cases "find_eq var L")
  case (Pair A L')
  then show ?thesis proof(cases A)
    case Nil
    show ?thesis proof safe
      fix x
      assume h : "eval (list_conj (map fm.Atom L @ F)) (xs @ x # \<Gamma>)"
      show "\<exists>x. eval (qe_eq_one var L F) (xs @ x # \<Gamma>)" apply(simp) using Nil Pair h by auto 
    next
      fix x
      assume h : "eval (qe_eq_one var L F) (xs @ x # \<Gamma>)"
      show "\<exists>x. eval (list_conj (map fm.Atom L @ F)) (xs @ x # \<Gamma>)"
        apply(rule exI[where x="x"]) using Nil Pair h by auto
    qed
  next
    case (Cons p A')
    have "set(map Eq (p # A') @ L') = set L"
      using list_in_find_eq[OF Pair] Cons by auto
    then have in_p: "Eq p \<in> set (L)"
      by auto
    have "p\<in>(set A)" using Cons by auto
    then have low_pow : "MPoly_Type.degree p var = 1 \<or> MPoly_Type.degree p var = 2" 
      using degree_find_eq[OF Pair] by auto
    have "(\<exists>x.(eval (qe_eq_one var L F) (xs @ (x#\<Gamma>)))) = 
          (\<exists>x.(eval (Or (And (Neg (split_p var p))
                      ((elimVar var L F) (Eq p))
                    )
                    (And (split_p var p) 
                      (list_conj (map Atom ((map Eq A')  @ L') @ F))
                    )) (xs @ (x#\<Gamma>))))"
      apply(rule ex_cong1) apply(simp only: qe_eq_one.simps) using Pair Cons  by auto
    also have "... = (\<exists>x. ((\<not>eval (split_p var p) (xs @ x # \<Gamma>)) \<and> eval (elimVar var L F (Eq p)) (xs @ x # \<Gamma>)) \<or>
         eval (split_p var p) (xs @ x # \<Gamma>) \<and>
         (\<forall>f\<in>set (map fm.Atom (map Eq A' @ L') @ F). eval f (xs @ x # \<Gamma>)))"
      by(simp add: eval_list_conj)
    also have "... = (\<exists>x. eval (list_conj (map fm.Atom L @ F)) (xs @ x # \<Gamma>))"
    proof(cases "\<forall>x. insertion (nth_default 0 (xs @ x # \<Gamma>)) (isolate_variable_sparse p var 2) \<noteq> 0 \<or>
      insertion (nth_default 0 (xs @ x # \<Gamma>)) (isolate_variable_sparse p var 1) \<noteq> 0 \<or>
      insertion (nth_default 0 (xs @ x # \<Gamma>)) (isolate_variable_sparse p var 0) \<noteq> 0")
      case True
      have "(\<exists>x. ((\<not>eval (split_p var p) (xs @ x # \<Gamma>)) \<and> eval (elimVar var L F (Eq p)) (xs @ x # \<Gamma>)) \<or>
         eval (split_p var p) (xs @ x # \<Gamma>) \<and>
         (\<forall>f\<in>set (map fm.Atom (map Eq A' @ L') @ F). eval f (xs @ x # \<Gamma>))) =
        (\<exists>x. eval (elimVar var L F (Eq p)) (xs @ x # \<Gamma>))"
      proof safe
        fix x
        assume "eval (elimVar var L F (Eq p)) (xs @ x # \<Gamma>)"
        then show "\<exists>x. eval (elimVar var L F (Eq p)) (xs @ x # \<Gamma>)" by auto
      next
        fix x
        assume h : "eval (split_p var p) (xs @ x # \<Gamma>)"
        have "\<not> eval (split_p var p) (xs @ x # \<Gamma>)"
          using True by simp 
        then show "\<exists>x. eval (elimVar var L F (Eq p)) (xs @ x # \<Gamma>)" using h by simp
      next
        fix x
        assume "eval (elimVar var L F (Eq p)) (xs @ x # \<Gamma>)"
        then show "\<exists>x. \<not> eval (split_p var p) (xs @ x # \<Gamma>) \<and> eval (elimVar var L F (Eq p)) (xs @ x # \<Gamma>) \<or>
             eval (split_p var p) (xs @ x # \<Gamma>) \<and>
             (\<forall>f\<in>set (map fm.Atom (map Eq A' @ L') @ F). eval f (xs @ x # \<Gamma>))"
          by auto
      qed
      then show ?thesis using elimVar_eq_2[OF hlength in_p low_pow True] by simp
    next
      case False
      have h1: "\<forall>x. eval (split_p var p) (xs @ x # \<Gamma>)"
        using False apply(simp) using not_in_isovarspar
        by (metis hlength insertion_lowerPoly1)
      have "set(map Eq (p # A') @ L') = set L"
        using list_in_find_eq[OF Pair] Cons by auto
      then have h5 : "set(map fm.Atom (map Eq (p # A') @ L') @ F) = set(map fm.Atom L @ F)"
        by auto
      have h4 : "(\<exists>x. (aEval (Eq p) (xs @ x # \<Gamma>)) \<and>
         (\<forall>f\<in>set (map fm.Atom (map Eq A' @ L') @ F). eval f (xs @ x # \<Gamma>))) = 
          (\<exists>x.(\<forall>f\<in>set (map fm.Atom (map Eq (p#A') @ L') @ F). eval f (xs @ x # \<Gamma>)))"
        by(simp)
      have h2 : "(\<exists>x. eval (list_conj (map fm.Atom L @ F)) (xs @ x # \<Gamma>)) = (\<exists>x. (aEval (Eq p) (xs @ x # \<Gamma>)) \<and>
         (\<forall>f\<in>set (map fm.Atom (map Eq A' @ L') @ F). eval f (xs @ x # \<Gamma>)))"
        by(simp only: h4 h5 eval_list_conj) 
      have h3 : "\<forall>x. (aEval (Eq p) (xs @ x # \<Gamma>))"
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
        show ?thesis unfolding express_p apply(simp add:insertion_add insertion_mult insertion_pow xlength)
          apply(simp add:c2 c1 c0 sum polyfun_eq_0[where c="c", where n="2"])
          using False apply(simp)
          by (metis A_def B_def C_def One_nat_def c0 c1 c2 le_SucE le_zero_eq numeral_2_eq_2)
      qed
      show ?thesis apply(simp only: h1 h2) using h3 by(simp)
    qed
    finally show ?thesis by auto
  qed
qed    




lemma qe_eq_repeat_helper_eval_case1 :
  assumes hlength : "length xs = var"
  assumes degreeGood : "\<forall>p\<in>set(A). MPoly_Type.degree p var = 1 \<or> MPoly_Type.degree p var = 2"
  shows "((eval (list_conj ((map (Atom o Eq)  A) @ (map Atom L) @ F)) (xs @ (x#\<Gamma>)))) 
        \<Longrightarrow> (eval (qe_eq_repeat_helper var A L F) (xs @ x # \<Gamma>))"
proof(induction A rule : in_list_induct)
  case Nil
  then show ?case by auto
next
  case (Cons p A')
  assume assm : "((eval (list_conj ((map (Atom o Eq) (p#A')) @ (map Atom L) @ F)) (xs @ (x#\<Gamma>)))) "
  then have h :  "insertion (nth_default 0 (xs @ x # \<Gamma>)) p = 0 \<and> (eval (qe_eq_repeat_helper var A' L F) (xs @ x # \<Gamma>))"
    using Cons by(simp add: eval_list_conj)
  have "\<not> eval (split_p var p) (xs @ x # \<Gamma>) \<and> eval (elimVar var ((map Eq (p# A')) @ L) F (Eq p)) (xs @ x # \<Gamma>) \<or>
    eval (split_p var p) (xs @ x # \<Gamma>) \<and> eval (qe_eq_repeat_helper var A' L F) (xs @ x # \<Gamma>)"
  proof(cases "eval (split_p var p) (xs @ x # \<Gamma>)")
    case True
    then show ?thesis using h by blast
  next
    case False
    have all0 :  " \<forall>x. insertion (nth_default 0 (xs @ x # \<Gamma>)) (isolate_variable_sparse p var 2) \<noteq> 0 \<or>
      insertion (nth_default 0 (xs @ x # \<Gamma>)) (isolate_variable_sparse p var 1) \<noteq> 0 \<or>
      insertion (nth_default 0 (xs @ x # \<Gamma>)) (isolate_variable_sparse p var 0) \<noteq> 0"
      using False  apply(simp) using not_in_isovarspar
      by (metis hlength insertion_lowerPoly1)
    have in_p : "Eq p\<in>set((map Eq (p # A') @ L))"
      by auto
    have "p\<in>(set A)" using Cons by auto
    then have low_pow : "MPoly_Type.degree p var = 1 \<or> MPoly_Type.degree p var = 2" 
      using degreeGood by auto
    have list_manipulate : "map fm.Atom (map Eq (p # A') @ L) = map (fm.Atom \<circ> Eq) (p # A') @ map fm.Atom L"
      by(simp)
    have "eval (elimVar var ((map Eq (p# A')) @ L) F (Eq p)) (xs @ x # \<Gamma>)"
      using elimVar_eq_2[OF hlength in_p low_pow all0, where F="F"] apply(simp only: list_manipulate) 
      using assm freeIn_elimVar_eq[where var="var", where L="(map Eq (p # A') @ L)", where F="F", where p="p"]
      by (metis append.assoc hlength list_update_length var_not_in_eval)
    then show ?thesis apply(simp only: False) by blast
  qed
  then show ?case by(simp only: qe_eq_repeat_helper.simps eval.simps)
qed

lemma qe_eq_repeat_helper_eval_case2 :
  assumes hlength : "length xs = var"
  assumes degreeGood : "\<forall>p\<in>set(A). MPoly_Type.degree p var = 1 \<or> MPoly_Type.degree p var = 2"
  shows "(eval (qe_eq_repeat_helper var A L F) (xs @ x # \<Gamma>))
        \<Longrightarrow> \<exists>x. ((eval (list_conj ((map (Atom o Eq)  A) @ (map Atom L) @ F)) (xs @ (x#\<Gamma>))))"
proof(induction A rule : in_list_induct)
  case Nil
  then show ?case apply(simp) apply(rule exI[where x=x]) by simp
next
  case (Cons p A')
  have h : "\<not> eval (split_p var p) (xs @ x # \<Gamma>) \<and> eval (elimVar var ((map Eq (p# A')) @ L) F (Eq p)) (xs @ x # \<Gamma>) \<or>
    eval (split_p var p) (xs @ x # \<Gamma>) \<and> eval (qe_eq_repeat_helper var A' L F) (xs @ x # \<Gamma>)"
    using Cons by(simp only:qe_eq_repeat_helper.simps eval.simps)
  have "p\<in>set(A)" using Cons(1) .
  then have degp : "MPoly_Type.degree p var = 1 \<or> MPoly_Type.degree p var = 2" 
    using degreeGood by auto
  show ?case proof(cases "eval (split_p var p) (xs @ x # \<Gamma>)")
    case True
    have "\<exists>x. eval (list_conj (map (fm.Atom \<circ> Eq) A' @ map fm.Atom L @ F)) (xs @ x # \<Gamma>)"
      using h True Cons by blast
    then obtain x where x_def : "eval (list_conj (map (fm.Atom \<circ> Eq) A' @ map fm.Atom L @ F)) (xs @ x # \<Gamma>)" by metis
    define A where "A = (isolate_variable_sparse p var 2)"
    define B where "B = (isolate_variable_sparse p var 1)"
    define C where "C = (isolate_variable_sparse p var 0)"
    have express_p : "p = A * Var var ^2+B * Var var+C"
    proof(cases "MPoly_Type.degree p var = 1")
      case True
      have a0 : "A = 0" apply(simp add: A_def) using True
        by (simp add: isovar_greater_degree) 
      show ?thesis using sum_over_zero[where mp="p", where x="var"] apply(subst (asm) True) by(simp add:a0 B_def C_def add.commute)
    next
      case False
      then have deg : "MPoly_Type.degree p var = 2" using degp by blast
      have flip : "A * (Var var)\<^sup>2 + B * Var var + C = C + B * Var var + A * (Var var)^2" using add.commute by auto
      show ?thesis using sum_over_zero[where mp="p", where x="var"] apply(subst (asm) deg) apply(simp add: flip) apply(simp add: A_def B_def C_def)
        by (simp add: numeral_2_eq_2)
    qed
    have insert_x : "insertion (nth_default 0 (xs @ x # \<Gamma>)) (Var var) = x" using hlength
      by (metis add.commute add_strict_increasing insertion_var length_append length_greater_0_conv list.distinct(1) list_update_id nth_append_length order_refl)

    have h : "(aEval (Eq p) (xs @ x # \<Gamma>))"
    proof-
      have freeA : "var \<notin> vars A"
        unfolding A_def
        by (simp add: not_in_isovarspar)
      have freeB : "var \<notin> vars B"
        unfolding B_def
        by (simp add: not_in_isovarspar)
      have freeC : "var \<notin> vars C"
        unfolding C_def
        by (simp add: not_in_isovarspar)
      have xlength : "(insertion (nth_default 0 (xs @ x # \<Gamma>)) (Var var))= x" 
        using hlength insertion_var
        using insert_x by blast
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
      have sum : "c 2 * x\<^sup>2 + c (Suc 0) * x + c 0 = (\<Sum>i\<le>2. c i * x ^ i)"
        by (simp add: numerals(2))  
      show ?thesis apply(subst express_p) apply(simp add:insertion_add insertion_mult insertion_pow xlength)
        apply(simp add:c2 c1 c0 sum polyfun_eq_0[where c="c", where n="2"])
        using True apply(simp) using le_SucE numeral_2_eq_2
        by (metis (no_types) A_def B_def C_def One_nat_def add.left_neutral c0 c1 c2 mult_zero_class.mult_zero_left sum)
    qed
    show ?thesis apply(rule exI[where x=x]) using x_def h apply(simp only:eval_list_conj) by(simp)
  next
    case False
    have all0 :  " \<forall>x. insertion (nth_default 0 (xs @ x # \<Gamma>)) (isolate_variable_sparse p var 2) \<noteq> 0 \<or>
      insertion (nth_default 0 (xs @ x # \<Gamma>)) (isolate_variable_sparse p var 1) \<noteq> 0 \<or>
      insertion (nth_default 0 (xs @ x # \<Gamma>)) (isolate_variable_sparse p var 0) \<noteq> 0"
      using False  apply(simp) using not_in_isovarspar
      by (metis hlength insertion_lowerPoly1)
    have h : "eval (elimVar var ((map Eq (p# A')) @ L) F (Eq p)) (xs @ x # \<Gamma>)"
      using False h by blast
    have in_list : "Eq p \<in> set (((map Eq (p# A')) @ L))"
      by(simp)
    show ?thesis using elimVar_eq_2[OF hlength in_list, where F="F", OF degp all0] h
      by (metis append_assoc map_append map_map)
  qed
qed



lemma qe_eq_repeat_eval :
  assumes hlength : "length xs = var"
  shows "(\<exists>x. (eval (list_conj ((map Atom L) @ F)) (xs @ (x#\<Gamma>)))) = (\<exists>x.(eval (qe_eq_repeat var L F) (xs @ (x#\<Gamma>))))"
proof(cases "luckyFind var L F")
  case None
  then show ?thesis proof(cases "find_eq var L")
    case (Pair A L')
    have degGood : "\<forall>p\<in>set A. MPoly_Type.degree p var = 1 \<or> MPoly_Type.degree p var = 2"
      using degree_find_eq[OF Pair] .
    have "(\<exists>x. eval (qe_eq_repeat var L F) (xs @ x # \<Gamma>)) =(\<exists>x. eval
        (qe_eq_repeat_helper var A L' F)
        (xs @ x # \<Gamma>))"
      using Pair None by auto
    also have "...
      = (\<exists>x. ((eval (list_conj ((map (Atom o Eq)  A) @ (map Atom L') @ F)) (xs @ (x#\<Gamma>)))))"
      using qe_eq_repeat_helper_eval_case1[OF hlength degGood, where L="L'", where F="F", where \<Gamma>="\<Gamma>"]
        qe_eq_repeat_helper_eval_case2[OF hlength degGood, where L="L'", where F="F", where \<Gamma>="\<Gamma>"]
      by blast
    also have "... = (\<exists>x. (eval (list_conj ((map Atom L) @ F)) (xs @ (x#\<Gamma>))))"
    proof-
      have list_manipulate : "map (fm.Atom \<circ> Eq) A @ map fm.Atom L' = map fm.Atom (map Eq A @ L')"
        by simp
      have changeA :  "map (fm.Atom \<circ> Eq) A = map Atom (map Eq A)" by auto
      have split : "(\<exists>x. \<forall>f\<in>set ((map (fm.Atom \<circ> Eq) A) @
                (map fm.Atom L') @ F).
          eval f (xs @ x # \<Gamma>)) = (\<exists>x. \<forall>f\<in> (Atom ` set ((map (Eq) A) @ L')) \<union> set(F).
          eval f (xs @ x # \<Gamma>))"
        apply (rule ex_cong1)
        apply(subst changeA)
        by auto
      show ?thesis apply(simp only: eval_list_conj split list_in_find_eq[OF Pair]) by auto
    qed
    finally have ?thesis by simp
    then show ?thesis by auto
  qed
next
  case (Some a)
  then show ?thesis using luckyFind_eval[OF Some assms(1)] by auto
qed


end
