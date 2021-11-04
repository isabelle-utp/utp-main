subsection "Overall LuckyFind Proofs"
theory LuckyFind
  imports EliminateVariable
begin



theorem luckyFind_eval:
  assumes "luckyFind x L F = Some F'"
  assumes "length xs = x"
  shows "(\<exists>x. (eval (list_conj ((map Atom L) @ F)) (xs @ (x#\<Gamma>)))) = (\<exists>x.(eval F' (xs @ (x#\<Gamma>))))"
proof(cases "find_lucky_eq x L")
  case None
  then show ?thesis using assms by auto
next
  case (Some p)
  have inset : "Eq p \<in> set L"
    using Some proof(induction L)
    case Nil
    then show ?case by auto
  next
    case (Cons a L)
    then show ?case proof(cases a)
      case (Less x1)
      then show ?thesis using Cons by auto
    next
      case (Eq p')
      show ?thesis using Cons
        unfolding Eq apply simp apply(cases "(MPoly_Type.degree p' x = Suc 0 \<or> MPoly_Type.degree p' x = 2)") apply simp_all
        apply(cases "check_nonzero_const (isolate_variable_sparse p' x 2)") apply(simp_all)
        apply(cases "check_nonzero_const (isolate_variable_sparse p' x 1)") apply(simp_all)
        apply(cases "check_nonzero_const (isolate_variable_sparse p' x 0)") by(simp_all)
    next
      case (Leq x3)
      then show ?thesis using Cons by auto
    next
      case (Neq x4)
      then show ?thesis using Cons by auto
    qed
  qed
  have degree : "MPoly_Type.degree p x = 1 \<or> MPoly_Type.degree p x = 2"
    using Some proof(induction L)
    case Nil
    then show ?case by auto
  next
    case (Cons a L)
    then show ?case proof(cases a)
      case (Less x1)
      then show ?thesis using Cons by auto
    next
      case (Eq p')
      show ?thesis using Cons
        unfolding Eq apply simp apply(cases "(MPoly_Type.degree p' x = Suc 0 \<or> MPoly_Type.degree p' x = 2)") apply simp_all
        apply(cases "check_nonzero_const (isolate_variable_sparse p' x 2)") apply(simp_all)
        apply(cases "check_nonzero_const (isolate_variable_sparse p' x 1)") apply(simp_all)
        apply(cases "check_nonzero_const (isolate_variable_sparse p' x 0)") by(simp_all)
    next
      case (Leq x3)
      then show ?thesis using Cons by auto
    next
      case (Neq x4)
      then show ?thesis using Cons by auto
    qed
  qed
  have nonzero : "\<forall>xa. insertion (nth_default 0 (xs @ xa # \<Gamma>)) (isolate_variable_sparse p x 2) \<noteq> 0 \<or>
       insertion (nth_default 0 (xs @ xa # \<Gamma>)) (isolate_variable_sparse p x 1) \<noteq> 0 \<or>
       insertion (nth_default 0 (xs @ xa # \<Gamma>)) (isolate_variable_sparse p x 0) \<noteq> 0"
    using Some proof(induction L)
    case Nil
    then show ?case by auto
  next
    case (Cons a L)
    then show ?case proof(cases a)
      case (Less x1)
      then show ?thesis using Cons by auto
    next
      case (Eq p')
      have h : "\<And>p xa. check_nonzero_const p \<Longrightarrow> insertion (nth_default 0 (xs @ xa # \<Gamma>)) p \<noteq> 0"
      proof-
        fix p xa
        assume h : "check_nonzero_const p"
        show "insertion (nth_default 0 (xs @ xa # \<Gamma>)) p \<noteq> 0"
          apply(cases "get_if_const p")
          using h get_if_const_insertion by simp_all
      qed
      show ?thesis using Cons(2)
        unfolding Eq apply (simp del:get_if_const.simps) apply(cases "(MPoly_Type.degree p' x = Suc 0 \<or> MPoly_Type.degree p' x = 2)") defer using Cons apply simp
        apply (simp del:get_if_const.simps)
        apply(cases "check_nonzero_const (isolate_variable_sparse p' x 2)")
        apply(simp del:get_if_const.simps) using h
        apply simp
        apply(cases "check_nonzero_const (isolate_variable_sparse p' x 1)")
        apply(simp del:get_if_const.simps) using h
        apply simp
        apply(cases "check_nonzero_const (isolate_variable_sparse p' x 0)")
        apply(simp del:get_if_const.simps) using h
        apply simp
        using Cons by auto
    next
      case (Leq x3)
      then show ?thesis using Cons by auto
    next
      case (Neq x4)
      then show ?thesis using Cons by auto
    qed
  qed
  show ?thesis
    using elimVar_eq_2[OF assms(2) inset degree nonzero] Some assms by auto
qed  


lemma luckyFind'_eval : 
  assumes "length xs = var"
  shows "(\<exists>x. eval (list_conj (map fm.Atom L @ F)) (xs @ x # \<Gamma>)) = (\<exists>x. eval (luckyFind' var L F) (xs @ x # \<Gamma>))"
proof(cases "find_lucky_eq var L")
  case None
  show ?thesis apply(simp add:eval_list_conj None)
    apply(rule ex_cong1)
    apply auto
    by (meson UnCI eval.simps(1) image_eqI)
next
  case (Some p)
  have "\<exists>F'. luckyFind var L F = Some F'" by (simp add:Some)
  then obtain F' where F'_def: "luckyFind var L F = Some F'" by metis
  show ?thesis
    unfolding luckyFind_eval[OF F'_def assms] 
    using F'_def Some by auto
qed 



lemma luckiestFind_eval : 
  assumes "length xs = var"
  shows "(\<exists>x. eval (list_conj (map fm.Atom L @ F)) (xs @ x # \<Gamma>)) = (\<exists>x. eval (luckiestFind var L F) (xs @ x # \<Gamma>))"
proof(cases "find_luckiest_eq var L")
  case None
  show ?thesis apply(simp add:eval_list_conj None)
    apply(rule ex_cong1)
    apply auto
    by (meson UnCI eval.simps(1) image_eqI)
next
  case (Some p)
  have h1: "Eq p \<in> set L"
    using Some apply(induction L arbitrary:p)
    apply simp
    subgoal for a L p
      apply(rule find_luckiest_eq.elims[of var "a#L" "Some p"])
      apply simp_all
      subgoal for v p'
        apply(cases "MPoly_Type.degree p' v = Suc 0 \<or> MPoly_Type.degree p' v = 2") apply simp_all 
        apply(cases "Set.is_empty (vars (isolate_variable_sparse p' v 2))") apply simp_all
        apply(cases "Set.is_empty (vars (isolate_variable_sparse p' v (Suc 0)))") apply simp_all
        apply(cases "Set.is_empty (vars (isolate_variable_sparse p' v 0))") apply simp_all
        apply(cases "MPoly_Type.coeff (isolate_variable_sparse p' v (Suc 0)) 0 = 0 \<longrightarrow>
        MPoly_Type.coeff (isolate_variable_sparse p' v 2) 0 = 0 \<longrightarrow> MPoly_Type.coeff (isolate_variable_sparse p' v 0) 0 \<noteq> 0") by simp_all
      done
    done
  have h2 : "MPoly_Type.degree p var = 1 \<or> MPoly_Type.degree p var = 2"
    using Some apply(induction L arbitrary:p)
    apply simp
    subgoal for a L p
      apply(rule find_luckiest_eq.elims[of var "a#L" "Some p"])
      apply simp_all
      subgoal for v p'
        apply(cases "MPoly_Type.degree p' v = Suc 0 \<or> MPoly_Type.degree p' v = 2") apply simp_all 
        apply(cases "Set.is_empty (vars (isolate_variable_sparse p' v 2))") apply simp_all
        apply(cases "Set.is_empty (vars (isolate_variable_sparse p' v (Suc 0)))") apply simp_all
        apply(cases "Set.is_empty (vars (isolate_variable_sparse p' v 0))") apply simp_all
        apply(cases "MPoly_Type.coeff (isolate_variable_sparse p' v (Suc 0)) 0 = 0 \<longrightarrow>
        MPoly_Type.coeff (isolate_variable_sparse p' v 2) 0 = 0 \<longrightarrow> MPoly_Type.coeff (isolate_variable_sparse p' v 0) 0 \<noteq> 0") by simp_all
      done
    done
  have h : "\<And>p xa. check_nonzero_const p \<Longrightarrow> insertion (nth_default 0 (xs @ xa # \<Gamma>)) p \<noteq> 0"
  proof-
    fix p xa
    assume h : "check_nonzero_const p"
    show "insertion (nth_default 0 (xs @ xa # \<Gamma>)) p \<noteq> 0"
      apply(cases "get_if_const p")
      using h get_if_const_insertion by simp_all
  qed

  have h3 : "\<forall>x. insertion (nth_default 0 (xs @ x # \<Gamma>)) (isolate_variable_sparse p var 2) \<noteq> 0 \<or>
        insertion (nth_default 0 (xs @ x # \<Gamma>)) (isolate_variable_sparse p var 1) \<noteq> 0 \<or>
        insertion (nth_default 0 (xs @ x # \<Gamma>)) (isolate_variable_sparse p var 0) \<noteq> 0"
    using Some apply(induction L arbitrary:p)
    apply simp
    subgoal for a L p
      apply(rule find_luckiest_eq.elims[of var "a#L" "Some p"])
      apply simp_all
      subgoal for v p'
        apply(cases "MPoly_Type.degree p' v = Suc 0 \<or> MPoly_Type.degree p' v = 2") apply simp_all 
        apply(cases "Set.is_empty (vars (isolate_variable_sparse p' v 2))") apply simp_all
        apply(cases "Set.is_empty (vars (isolate_variable_sparse p' v (Suc 0)))") apply simp_all
        apply(cases "Set.is_empty (vars (isolate_variable_sparse p' v 0))") apply simp_all
        apply(cases "MPoly_Type.coeff (isolate_variable_sparse p' v (Suc 0)) 0 = 0 \<longrightarrow>
        MPoly_Type.coeff (isolate_variable_sparse p' v 2) 0 = 0 \<longrightarrow> MPoly_Type.coeff (isolate_variable_sparse p' v 0) 0 \<noteq> 0") apply simp_all
        using h[of "isolate_variable_sparse p' v 0"] h[of "isolate_variable_sparse p' v (Suc 0)"] h[of "isolate_variable_sparse p' v 2"] apply simp
        by blast
      done
    done
  show ?thesis  apply(simp_all add:Some del:elimVar.simps)
    apply(rule elimVar_eq_2) using assms apply simp using h1 h2 h3 by auto

qed 

end