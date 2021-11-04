subsection "Optimization Proofs"
theory OptimizationProofs
  imports Optimizations
begin

lemma neg_nnf : "\<forall>\<Gamma>. (\<not> eval (nnf (Neg \<phi>)) \<Gamma>) = eval (nnf \<phi>) \<Gamma>"
  apply(induction \<phi>)
           apply(simp_all)
  using aNeg_aEval apply blast
  using aNeg_aEval by blast

theorem eval_nnf : "\<forall>\<Gamma>. eval \<phi> \<Gamma> = eval (nnf \<phi>) \<Gamma>"
  apply(induction \<phi>)apply(simp_all) using neg_nnf by blast


theorem negation_free_nnf : "negation_free (nnf \<phi>)"
proof(induction "depth \<phi>" arbitrary : \<phi> rule: nat_less_induct )
  case 1
  then show ?case
  proof(induction \<phi>)
    case (And \<phi>1 \<phi>2)
    then show ?case apply simp
      by (metis less_Suc_eq_le max.cobounded1 max.cobounded2)
  next
    case (Or \<phi>1 \<phi>2)
    then show ?case apply simp
      by (metis less_Suc_eq_le max.cobounded1 max.cobounded2)
  next
    case (Neg \<phi>)
    then show ?case proof (induction \<phi>)
      case (And \<phi>1 \<phi>2)
      then show ?case apply simp
        by (metis less_Suc_eq max_less_iff_conj not_less_eq)
    next
      case (Or \<phi>1 \<phi>2)
      then show ?case apply simp
        by (metis less_Suc_eq max_less_iff_conj not_less_eq)
    next
      case (Neg \<phi>)
      then show ?case
        by (metis Suc_eq_plus1 add_lessD1 depth.simps(6) lessI nnf.simps(12))
    qed auto
  qed auto
qed


lemma groupQuantifiers_eval : "eval F L = eval (groupQuantifiers F) L"
  apply(induction F arbitrary: L  rule:groupQuantifiers.induct) 
  unfolding doubleExist unwrapExist unwrapExist' unwrapExist'' doubleForall unwrapForall unwrapForall' unwrapForall''
  apply (auto)
  using doubleExist doubleExist unwrapExist unwrapExist' unwrapExist'' doubleForall unwrapForall unwrapForall' unwrapForall''  apply auto
  by metis+


theorem simp_atom_eval : "aEval a xs = eval (simp_atom a) xs"
proof(cases a)
  case (Less p)
  then show ?thesis by(cases "get_if_const p")(simp_all add:get_if_const_insertion)
next
  case (Eq p)
  then show ?thesis by(cases "get_if_const p")(simp_all add:get_if_const_insertion)
next
  case (Leq p)
  then show ?thesis by(cases "get_if_const p")(simp_all add:get_if_const_insertion)
next
  case (Neq p)
  then show ?thesis by(cases "get_if_const p")(simp_all add:get_if_const_insertion)
qed

lemma simpfm_eval : "\<forall>L. eval \<phi> L = eval (simpfm \<phi>) L"
  apply(induction \<phi>)
  apply(simp_all add: simp_atom_eval eval_and eval_or)
  using eval_neg by blast

lemma exQ_clearQuantifiers:
  assumes ExQ : "\<And>xs. eval (clearQuantifiers \<phi>) xs = eval \<phi> xs"
  shows "eval (clearQuantifiers (ExQ \<phi>)) xs = eval (ExQ \<phi>) xs"
proof-
  define \<phi>' where "\<phi>' = clearQuantifiers \<phi>"
  have h : "freeIn 0 \<phi>' \<Longrightarrow> (eval (lowerFm 0 1 \<phi>') xs = eval (ExQ \<phi>') xs)"
    using eval_lowerFm by simp
  have "eval (clearQuantifiers (ExQ \<phi>)) xs = 
      eval (if freeIn 0 \<phi>' then lowerFm 0 1 \<phi>' else ExQ \<phi>') xs"
    using \<phi>'_def by simp
  also have "... = eval (ExQ \<phi>) xs"
    apply(cases "freeIn 0 \<phi>'")
    using h ExQ \<phi>'_def by(simp_all)
  finally show ?thesis
    by simp
qed

lemma allQ_clearQuantifiers :
  assumes AllQ : "\<And>xs. eval (clearQuantifiers \<phi>) xs = eval \<phi> xs"
  shows "eval (clearQuantifiers (AllQ \<phi>)) xs = eval (AllQ \<phi>) xs"
proof-
  define \<phi>' where "\<phi>' = clearQuantifiers \<phi>"
  have "freeIn 0 \<phi>' \<Longrightarrow> (eval (ExQ \<phi>') xs) = eval (AllQ \<phi>') xs"
    by (simp add: var_not_in_eval2)
  then have h : "freeIn 0 \<phi>' \<Longrightarrow> (eval (lowerFm 0 1 \<phi>') xs = eval (AllQ \<phi>') xs)"
    using eval_lowerFm by simp
  have "eval (clearQuantifiers (AllQ \<phi>)) xs = 
      eval (if freeIn 0 \<phi>' then lowerFm 0 1 \<phi>' else AllQ \<phi>') xs"
    using \<phi>'_def by simp
  also have "... = eval (AllQ \<phi>) xs"
    apply(cases "freeIn 0 \<phi>'")
    using h AllQ \<phi>'_def by(simp_all)
  finally show ?thesis 
    by simp
qed

lemma clearQuantifiers_eval : "eval (clearQuantifiers \<phi>) xs = eval \<phi> xs"
proof(induction \<phi> arbitrary : xs)
  case (Atom x)
  then show ?case using simp_atom_eval by simp
next
  case (And \<phi>1 \<phi>2)
  then show ?case using eval_and by simp
next
  case (Or \<phi>1 \<phi>2)
  then show ?case using eval_or by simp
next
  case (Neg \<phi>)
  then show ?case using eval_neg by auto
next
  case (ExQ \<phi>)
  then show ?case using exQ_clearQuantifiers by simp
next
  case (AllQ \<phi>)
  then show ?case using allQ_clearQuantifiers by simp
next
  case (ExN x1 \<phi>)
  then show ?case proof(induction x1 arbitrary:\<phi>)
    case 0
    then show ?case by auto
  next
    case (Suc x1)
    show ?case
      using Suc(1)[of "ExQ \<phi>", OF exQ_clearQuantifiers[OF Suc(2)]]
      apply simp
      using Suc_eq_plus1 \<open>eval (clearQuantifiers (ExN x1 (ExQ \<phi>))) xs = eval (ExN x1 (ExQ \<phi>)) xs\<close> eval.simps(10) unwrapExist' by presburger
  qed
next
  case (AllN x1 \<phi>)
  then show ?case proof(induction x1 arbitrary:\<phi>)
    case 0
    then show ?case by auto
  next
    case (Suc x1)
    show ?case
      using Suc(1)[of "AllQ \<phi>", OF allQ_clearQuantifiers[OF Suc(2)]]
      apply simp
      using unwrapForall' by force
  qed
qed auto

lemma  push_forall_eval_AllQ : "\<forall>xs. eval (AllQ \<phi>) xs = eval (push_forall (AllQ \<phi>)) xs"
proof(induction \<phi>)
  case TrueF
  then show ?case by simp
next
  case FalseF
  then show ?case by simp
next
  case (Atom x)
  then show ?case
    using aEval_lowerAtom eval.simps(1) eval.simps(8) push_forall.simps(11) by presburger
next
  case (And \<phi>1 \<phi>2)
  {fix xs
    have "eval (AllQ (And \<phi>1 \<phi>2)) xs = (\<forall>x. eval \<phi>1 (x#xs) \<and> eval \<phi>2 (x#xs))"
      by simp
    also have "... = ((\<forall>x. eval \<phi>1 (x#xs)) \<and> (\<forall>x. eval \<phi>2 (x#xs)))"
      by blast
    also have "... = eval (push_forall (AllQ (And \<phi>1 \<phi>2))) xs"
      using And eval_and by(simp)
    finally have "eval (AllQ (And \<phi>1 \<phi>2)) xs = eval (push_forall (AllQ (And \<phi>1 \<phi>2))) xs"
      by simp
  }
  then show ?case by simp 
next
  case (Or \<phi>1 \<phi>2)
  then show ?case proof(cases "freeIn 0 \<phi>1")
    case True
    then have h : "freeIn 0 \<phi>1"
      by simp
    then show ?thesis proof(cases "freeIn 0 \<phi>2")
      case True
      {fix xs
        have "\<exists>x. eval \<phi>1 (x # xs) = eval (lowerFm 0 1 \<phi>1) xs"
          using eval_lowerFm h eval.simps(7) by blast 
        then have h1 : "\<forall>x. eval \<phi>1 (x # xs) = eval (lowerFm 0 1 \<phi>1) xs"
          using h var_not_in_eval2 by blast
        have "\<exists>x. eval \<phi>2 (x # xs) = eval (lowerFm 0 1 \<phi>2) xs"
          using eval_lowerFm True eval.simps(7) by blast 
        then have h2 : "\<forall>x. eval \<phi>2 (x # xs) = eval (lowerFm 0 1 \<phi>2) xs"
          using True var_not_in_eval2 by blast
        have "eval (AllQ (Or \<phi>1 \<phi>2)) xs = eval (push_forall (AllQ (Or \<phi>1 \<phi>2))) xs"
          by(simp add:h h1 h2 True eval_or)
      }
      then show ?thesis by simp
    next
      case False
      {fix xs
        have "\<exists>x. eval \<phi>1 (x # xs) = eval (lowerFm 0 1 \<phi>1) xs"
          using eval_lowerFm h eval.simps(7) by blast 
        then have "\<forall>x. eval \<phi>1 (x # xs) = eval (lowerFm 0 1 \<phi>1) xs"
          using True var_not_in_eval2 by blast
        then have "eval (AllQ (Or \<phi>1 \<phi>2)) xs = eval (push_forall (AllQ (Or \<phi>1 \<phi>2))) xs"
          by(simp add:h False eval_or)
      }
      then show ?thesis by simp
    qed
  next
    case False
    then have h : "\<not>freeIn 0 \<phi>1"
      by simp
    then show ?thesis proof(cases "freeIn 0 \<phi>2")
      case True
      {fix xs
        have "\<exists>x. eval \<phi>2 (x # xs) = eval (lowerFm 0 1 \<phi>2) xs"
          using eval_lowerFm True eval.simps(7) by blast 
        then have "\<forall>x. eval \<phi>2 (x # xs) = eval (lowerFm 0 1 \<phi>2) xs"
          using True var_not_in_eval2 by blast
        then have "eval (AllQ (Or \<phi>1 \<phi>2)) xs = eval (push_forall (AllQ (Or \<phi>1 \<phi>2))) xs"
          by(simp add:h True eval_or)
      }
      then show ?thesis by simp
    next
      case False
      then show ?thesis by(simp add:h False eval_or)
    qed
  qed
next
  case (Neg \<phi>)
  {fix xs
    have "freeIn 0 (Neg \<phi>) \<Longrightarrow> (eval (ExQ (Neg \<phi>)) xs) = eval (AllQ (Neg \<phi>)) xs"
      using var_not_in_eval2 eval.simps(7) eval.simps(8) by blast
    then have h : "freeIn 0 (Neg \<phi>) \<Longrightarrow> (eval (lowerFm 0 1 (Neg \<phi>)) xs = eval (AllQ (Neg \<phi>)) xs)"
      using eval_lowerFm by blast
    have "eval (push_forall (AllQ (Neg \<phi>))) xs = 
      eval (if freeIn 0 (Neg \<phi>) then lowerFm 0 1 (Neg \<phi>) else AllQ (Neg \<phi>)) xs"
      by simp
    also have "... = eval (AllQ (Neg \<phi>)) xs"
      apply(cases "freeIn 0 (Neg \<phi>)")
      using h  by(simp_all)
    finally have "eval (push_forall (AllQ (Neg \<phi>))) xs = eval (AllQ (Neg \<phi>)) xs"
      by simp
  }
  then show ?case by simp
next
  case (ExQ \<phi>)
  {fix xs
    have "freeIn 0 (ExQ \<phi>) \<Longrightarrow> (eval (ExQ (ExQ \<phi>)) xs) = eval (AllQ (ExQ \<phi>)) xs"
      using var_not_in_eval2 eval.simps(7) eval.simps(8) by blast
    then have h : "freeIn 0 (ExQ \<phi>) \<Longrightarrow> (eval (lowerFm 0 1 (ExQ \<phi>)) xs = eval (AllQ (ExQ \<phi>)) xs)"
      using eval_lowerFm by blast
    have "eval (push_forall (AllQ (ExQ \<phi>))) xs = 
      eval (if freeIn 0 (ExQ \<phi>) then lowerFm 0 1 (ExQ \<phi>) else AllQ (ExQ \<phi>)) xs"
      by simp
    also have "... = eval (AllQ (ExQ \<phi>)) xs"
      apply(cases "freeIn 0 (ExQ \<phi>)")
      using h  by(simp_all)
    finally have "eval (push_forall (AllQ (ExQ \<phi>))) xs = eval (AllQ (ExQ \<phi>)) xs"
      by simp
  }
  then show ?case by simp
next
  case (AllQ \<phi>)
  {fix xs
    have "freeIn 0 (AllQ \<phi>) \<Longrightarrow> (eval (ExQ (AllQ \<phi>)) xs) = eval (AllQ (AllQ \<phi>)) xs"
      using var_not_in_eval2 eval.simps(7) eval.simps(8) by blast
    then have h : "freeIn 0 (AllQ \<phi>) \<Longrightarrow> (eval (lowerFm 0 1 (AllQ \<phi>)) xs = eval (AllQ (AllQ \<phi>)) xs)"
      using eval_lowerFm by blast
    have "eval (push_forall (AllQ (AllQ \<phi>))) xs = 
      eval (if freeIn 0 (AllQ \<phi>) then lowerFm 0 1 (AllQ \<phi>) else AllQ (AllQ \<phi>)) xs"
      by simp
    also have "... = eval (AllQ (AllQ \<phi>)) xs"
      apply(cases "freeIn 0 (AllQ \<phi>)")
      using h AllQ  by(simp_all)
    finally have "eval (push_forall (AllQ (AllQ \<phi>))) xs = eval (AllQ (AllQ \<phi>)) xs"
      by simp
  }
  then show ?case by simp
next
  case (ExN x1 \<phi>)
  then show ?case
    using eval.simps(7) eval.simps(8) eval_lowerFm push_forall.simps(17) var_not_in_eval2 by presburger
next
  case (AllN x1 \<phi>)
  then show ?case
    using eval.simps(7) eval.simps(8) eval_lowerFm push_forall.simps(18) var_not_in_eval2 by presburger
qed

lemma push_forall_eval : "\<forall>xs. eval \<phi> xs = eval (push_forall \<phi>) xs"
proof(induction \<phi>)
  case (Atom x)
  then show ?case using simp_atom_eval by simp
next
  case (And \<phi>1 \<phi>2)
  then show ?case using eval_and by auto
next
  case (Or \<phi>1 \<phi>2)
  then show ?case using eval_or by auto
next
  case (Neg \<phi>)
  then show ?case using eval_neg by auto
next
  case (AllQ \<phi>)
  then show ?case using push_forall_eval_AllQ by blast 
next
  case (ExN x1 \<phi>)
  then show ?case
    using eval.simps(10) push_forall.simps(7) by presburger
qed auto

lemma map_fm_binders_negation_free : 
  assumes "negation_free \<phi>"
  shows "negation_free (map_fm_binders f \<phi> n)"
  using assms apply(induction \<phi> arbitrary : n) by auto

lemma negation_free_and : 
  assumes "negation_free \<phi>"
  assumes "negation_free \<psi>"
  shows "negation_free (and \<phi> \<psi>)"
  using assms unfolding and_def by simp 

lemma negation_free_or : 
  assumes "negation_free \<phi>"
  assumes "negation_free \<psi>"
  shows "negation_free (or \<phi> \<psi>)"
  using assms unfolding or_def by simp 

lemma push_forall_negation_free_all :
  assumes "negation_free \<phi>"
  shows "negation_free (push_forall (AllQ \<phi>))"
  using assms proof(induction \<phi>)
  case (And \<phi>1 \<phi>2)
  show ?case apply auto
    apply(rule negation_free_and)
    using And by auto
next
  case (Or \<phi>1 \<phi>2)
  show ?case
    apply auto
    apply(rule negation_free_or)   
    using Or map_fm_binders_negation_free negation_free_or by auto
next
  case (ExQ \<phi>)
  then show ?case using map_fm_binders_negation_free by auto
next
  case (AllQ \<phi>)
  then show ?case using map_fm_binders_negation_free by auto
next
  case (ExN x1 \<phi>)
  then show ?case using map_fm_binders_negation_free by auto
next
  case (AllN x1 \<phi>)
  then show ?case using map_fm_binders_negation_free by auto
qed auto

lemma push_forall_negation_free : 
  assumes "negation_free \<phi>"  
  shows "negation_free(push_forall \<phi>)"
  using assms proof(induction \<phi>)
  case (Atom A)
  then show ?case apply(cases A) by auto
next
  case (And \<phi>1 \<phi>2)
  then show ?case by (auto simp add: and_def)
next
  case (Or \<phi>1 \<phi>2)
  then show ?case by (auto simp add: or_def)
next
  case (AllQ \<phi>)
  then show ?case using push_forall_negation_free_all by auto
qed auto


lemma to_list_insertion: "insertion f p = sum_list [insertion f term * (f v) ^ i. (term,i)\<leftarrow>(to_list v p)]"
proof-
  have h1 :  "insertion f p = insertion f (\<Sum>i\<le>MPoly_Type.degree p v. isolate_variable_sparse p v i * Var v ^ i)"
    using sum_over_zero by auto
  have h2 : "insertion f (Var v) = f v" by (auto simp: monomials_Var coeff_Var insertion_code)
  define d where "d = MPoly_Type.degree p v"
  define g where "g = (\<lambda>x. insertion f (isolate_variable_sparse p v x) * f v ^ x)"
  have h3 : "insertion f (isolate_variable_sparse p v d) * f v ^ d = g d" using g_def by auto
  show ?thesis unfolding h1
      insertion_sum' insertion_mult insertion_pow h2 apply auto unfolding d_def[symmetric] g_def[symmetric]
      h3  proof(induction d)
    case 0
    then show ?case by auto
  next
    case (Suc d)
    show ?case
      apply (auto simp add: Suc ) unfolding g_def by auto
  qed
qed

lemma to_list_p: "p = sum_list [term * (Var v) ^ i. (term,i)\<leftarrow>(to_list v p)]"
proof-
  define d where "d = MPoly_Type.degree p v"
  have "(\<Sum>i\<le>MPoly_Type.degree p v. isolate_variable_sparse p v i * Var v ^ i) = (\<Sum>(term, i)\<leftarrow>to_list v p. term * Var v ^ i)"
    unfolding to_list.simps d_def[symmetric] apply(induction d) by auto
  then show ?thesis 
    using sum_over_zero[of p v]
    by auto
qed


fun chophelper :: "(real mpoly * nat) list \<Rightarrow> (real mpoly * nat) list \<Rightarrow> (real mpoly * nat) list * (real mpoly * nat) list" where
  "chophelper [] L = (L,[])"|
  "chophelper ((p,i)#L) R = (if p=0 then chophelper L (R @ [(p,i)]) else (R,(p,i)#L))"

lemma preserve :
  assumes "(a,b)=chophelper L L'"
  shows "a@b=L'@L"
  using assms
proof(induction L arbitrary : a b L')
  case Nil
  then show ?case using assms by auto
next
  case (Cons A L)
  then show ?case proof(cases A)
    case (Pair p i)
    show ?thesis using Cons unfolding Pair apply(cases "p=0") by auto
  qed
qed
lemma compare : 
  assumes "(a,b)=chophelper L L'"
  shows "chop L = b"
  using assms
proof(induction L arbitrary : a b L')
  case Nil
  then show ?case by auto
next
  case (Cons A L)
  then show ?case proof(cases A)
    case (Pair p i)
    show ?thesis using Cons unfolding Pair apply(cases "p=0") by auto
  qed
qed
lemma allzero:
  assumes "\<forall>(p,i)\<in>set(L'). p=0"
  assumes "(a,b)=chophelper L L'"
  shows "\<forall>(p,i)\<in>set(a). p=0"
  using assms proof(induction L arbitrary : a b L')
  case Nil
  then show ?case by auto
next
  case (Cons t L)
  then show ?case
  proof(cases t)
    case (Pair p i)
    show ?thesis proof(cases "p=0")
      case True
      have h1: "\<forall>x\<in>set (L' @ [(0, i)]). case x of (p, i) \<Rightarrow> p = 0"
        using Cons(2) by auto
      show ?thesis using Cons(1)[OF h1] Cons(3) True unfolding Pair by auto
    next
      case False
      then show ?thesis using Cons unfolding Pair by auto
    qed
  qed
qed 

lemma separate:
  assumes "(a,b)=chophelper (to_list v p) []"
  shows "insertion f p = sum_list [insertion f term * (f v) ^ i. (term,i)\<leftarrow>a] + sum_list [insertion f term * (f v) ^ i. (term,i)\<leftarrow>b]"
  using to_list_insertion[of f p v]  preserve[OF assms, symmetric] unfolding List.append.left_neutral
  by (simp del: to_list.simps)

lemma chopped : 
  assumes "(a,b)=chophelper (to_list v p) []"
  shows "insertion f p = sum_list [insertion f term * (f v) ^ i. (term,i)\<leftarrow>b]"
proof-
  have h1 : "\<forall>(p, i)\<in>set []. p = 0" by auto
  have "(\<Sum>(term, i)\<leftarrow>a. insertion f term * f v ^ i) = 0"
    using allzero[OF h1 assms] proof(induction a)
    case Nil
    then show ?case by auto
  next
    case (Cons a1 a2)
    then show ?case
      apply(cases a1) by simp
  qed 
  then show ?thesis using separate[OF assms, of f] by auto
qed

lemma insertion_chop : 
  shows "insertion f p = sum_list [insertion f term * (f v) ^ i. (term,i)\<leftarrow>(chop (to_list v p))]" 
proof(cases "chophelper (to_list v p) []")
  case (Pair a b)
  show ?thesis using chopped[OF Pair[symmetric], of f] unfolding compare[OF Pair[symmetric], symmetric] .
qed

lemma sorted : "sorted_wrt (\<lambda>(_,i).\<lambda>(_,i'). i<i') (to_list v p)"
proof -
  define d  where "d = MPoly_Type.degree p v"
  show ?thesis unfolding to_list.simps d_def[symmetric] 
  proof(induction d)
    case 0
    then show ?case by auto
  next
    case (Suc d)
    have h : "(map (\<lambda>x. (isolate_variable_sparse p v x, x)) [0..<Suc d + 1]) = 
        (map (\<lambda>x. (isolate_variable_sparse p v x, x)) [0..<Suc d]) @ [(isolate_variable_sparse p v (Suc d), (Suc d))]"
      by auto
    show ?case
      unfolding sorted_wrt_append h
      using Suc
      by auto
  qed
qed

lemma sublist : "sublist (chop L) L"
proof(induction L)
  case Nil
  then show ?case by auto
next
  case (Cons a L)
  then show ?case proof(cases a)
    case (Pair a b)
    show ?thesis using Cons unfolding Pair apply auto
      by (simp add: sublist_Cons_right)
  qed
qed



lemma move_exp :
  assumes "(p',i)#L = (chop (to_list v p))"
  shows "insertion f p = sum_list [insertion f term * (f v) ^ (d-i). (term,d)\<leftarrow>(chop (to_list v p))] * (f v)^i" 
proof-
  have h : "sorted_wrt (\<lambda>(_, i) (_, y). i < y) (chop (to_list v p))"
  proof-
    define L where "L = to_list v p"
    show ?thesis using sublist[of "to_list v p"] sorted[of v p] unfolding L_def[symmetric]
      by (metis sorted_wrt_append sublist_def)
  qed
  then have "\<forall>(term,d)\<in>set(chop (to_list v p)). d\<ge>i"
    unfolding assms[symmetric]  by fastforce
  then have simp : "\<forall>(term,d)\<in>set(chop(to_list v p)). f v ^ (d - i) * f v ^ i = f v ^ d"
    unfolding HOL.no_atp(118) by(auto simp del: to_list.simps)
  have "insertion f p = sum_list [insertion f term * (f v) ^ i. (term,i)\<leftarrow>(chop (to_list v p))]" using insertion_chop[of f p v] .
  also have "...= (\<Sum>(term, d)\<leftarrow>chop (to_list v p). insertion f term * f v ^ (d-i) * f v ^ i)" 
    using simp
    by (smt Pair_inject case_prodE map_eq_conv mult.assoc split_cong) 
  also have "... =  (\<Sum>(term, d)\<leftarrow>chop (to_list v p). insertion f term * f v ^ (d - i)) * f v ^ i"
  proof-
    define d where "d = chop(to_list v p)"
    define a where "a = f v ^ i"
    define b where "b = (\<lambda>(term, d). insertion f term * f v ^ (d - i))"
    have h : "(\<Sum>(term, d)\<leftarrow>d. insertion f term * f v ^ (d - i) * a) = (\<Sum>(term, d)\<leftarrow>d. b (term,d) * a)"
      using b_def by auto
    show ?thesis unfolding d_def[symmetric] a_def[symmetric]  b_def[symmetric] h  apply(induction d) apply simp apply auto
      by (simp add: ring_class.ring_distribs(2))
  qed
  finally show ?thesis by auto
qed

lemma insert_Var_Zero : "insertion f (Var v) = f v"
  unfolding insertion_code monomials_Var apply auto
  unfolding coeff_Var by simp


lemma decreasePower_insertion :
  assumes "decreasePower v p = (p',i)"
  shows "insertion f p = insertion f p'* (f v)^i"
proof(cases "chop (to_list v p)")
  case Nil
  then show ?thesis
    using assms by auto
next
  case (Cons a list)
  then show ?thesis
  proof(cases a)
    case (Pair coef i')
    have i'_def : "i'=i" using Cons assms Pair by auto
    have chop: "chop (to_list v p) = (coef, i) # list" using Cons assms unfolding i'_def Pair by auto
    have p'_def :  "p' = (\<Sum>(term, x)\<leftarrow>chop (to_list v p). term * Var v ^ (x - i))"
      using assms Cons Pair by auto 
    have p'_insertion : "insertion f p' = (\<Sum>(term, x)\<leftarrow>chop (to_list v p). insertion f term * f v ^ (x - i))"
    proof-
      define d where "d = chop (to_list v p)"
      have "insertion f p' = insertion f (\<Sum>(term, x)\<leftarrow>chop (to_list v p). term * Var v ^ (x - i))" using p'_def by auto
      also have "... = (\<Sum>(term, x)\<leftarrow>chop (to_list v p).  insertion f (term * Var v ^ (x - i)))" 
        unfolding d_def[symmetric] apply(induction d) apply simp apply(simp add:insertion_add) by auto
      also have "... = (\<Sum>(term, x)\<leftarrow>chop (to_list v p). insertion f term * f v ^ (x - i))" unfolding insertion_mult insertion_pow insert_Var_Zero by auto
      finally show ?thesis by auto
    qed
    have h : "(coef, i') # list = chop (to_list v p)"  using Cons unfolding Pair by auto
    show ?thesis unfolding p'_insertion
      using move_exp[OF h, of f] unfolding i'_def .
  qed
qed 


lemma unpower_eval: "eval (unpower v \<phi>) L = eval \<phi> L"
proof(induction \<phi> arbitrary: v L)
  case TrueF
  then show ?case by auto
next
  case FalseF
  then show ?case by auto
next
  case (Atom At)
  then show ?case proof(cases At)
    case (Less p)
    obtain q i where h: "decreasePower v p = (q, i)"
      using prod.exhaust_sel by blast
    have p : "\<And>f. insertion f p = insertion f q* (f v)^i"
      using decreasePower_insertion[OF h] by auto
    show ?thesis
    proof(cases "i=0")
      case True
      then show ?thesis unfolding Less unpower.simps h  by auto
    next
      case False
      obtain x where x_def : "Suc x = i" using False
        using not0_implies_Suc by auto 
      have h1 : "i mod 2 = 0 \<Longrightarrow>
    (insertion (nth_default 0 L) q < 0 \<and>
     insertion (nth_default 0 L) (Var v) \<noteq> 0) =
    (insertion (nth_default 0 L) q * nth_default 0 L v ^ i < 0)"
      proof -
        assume "i mod 2 = 0"
        then have "\<forall>r. \<not> (r::real) ^ i < 0"
          by presburger
        then show ?thesis
          by (metis \<open>\<And>thesis. (\<And>x. Suc x = i \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> insert_Var_Zero linorder_neqE_linordered_idom mult_less_0_iff power_0_Suc power_eq_0_iff)
      qed
      show ?thesis unfolding Less unpower.simps h x_def[symmetric] apply simp
        unfolding x_def p apply(cases "i mod 2 = 0") using h1 apply simp_all
        by (smt insert_Var_Zero insertion_neg mod_Suc mod_eq_0D mult_less_0_iff nat.inject odd_power_less_zero power_0 power_Suc0_right power_eq_0_iff x_def zero_less_Suc zero_less_power)
    qed 
  next
    case (Eq p)
    obtain q i where h: "decreasePower v p = (q, i)"
      using prod.exhaust_sel by blast
    have p : "\<And>f. insertion f p = insertion f q* (f v)^i"
      using decreasePower_insertion[OF h] by auto
    show ?thesis unfolding Eq unpower.simps h apply simp apply(cases i) apply simp
      apply simp unfolding p apply simp
      by (metis insert_Var_Zero)
  next
    case (Leq p)
    obtain q i where h: "decreasePower v p = (q, i)"
      using prod.exhaust_sel by blast
    have p : "\<And>f. insertion f p = insertion f q* (f v)^i"
      using decreasePower_insertion[OF h] by auto
    show ?thesis
    proof(cases "i=0")
      case True
      then show ?thesis unfolding Leq unpower.simps h  by auto
    next
      case False
      obtain x where x_def : "Suc x = i" using False
        using not0_implies_Suc by auto 
      define a where "a = insertion (nth_default 0 L) q"
      define x' where "x' = nth_default 0 L v"
      show ?thesis unfolding Leq unpower.simps h x_def[symmetric] apply simp
        unfolding x_def p apply(cases "i mod 2 = 0") unfolding insert_Var_Zero insertion_mult insertion_pow insertion_neg apply simp_all
        unfolding a_def[symmetric] x'_def[symmetric]
      proof-
        assume "i mod 2 = 0"
        then have "x' ^ i \<ge>0"
          by (simp add: \<open>i mod 2 = 0\<close> even_iff_mod_2_eq_zero zero_le_even_power) 
        then show "(a \<le> 0 \<or> x' = 0) = (a * x' ^ i \<le> 0)"
          using Rings.ordered_semiring_0_class.mult_nonpos_nonneg[of a "x'^i"]
          apply auto
          unfolding Rings.linordered_ring_strict_class.mult_le_0_iff
          apply auto
          by (simp add: False power_0_left)
      next
        assume h:  "i mod 2 = Suc 0"
        show "(a = 0 \<or> a < 0 \<and> 0 \<le> x' \<or> 0 < a \<and> x' \<le> 0) = (a * x' ^ i \<le> 0)"
          using h
          by (smt even_iff_mod_2_eq_zero mult_less_cancel_right mult_neg_neg mult_nonneg_nonpos mult_pos_pos not_mod2_eq_Suc_0_eq_0 power_0_Suc x_def zero_le_power_eq zero_less_mult_pos2 zero_less_power)
      qed
    qed 
  next
    case (Neq p)
    obtain q i where h: "decreasePower v p = (q, i)"
      using prod.exhaust_sel by blast
    have p : "\<And>f. insertion f p = insertion f q* (f v)^i"
      using decreasePower_insertion[OF h] by auto
    show ?thesis unfolding Neq unpower.simps h apply simp apply(cases i) apply simp
      apply simp unfolding p apply simp
      by (metis insert_Var_Zero)
  qed
qed auto

lemma to_list_filter: "p = sum_list [term * (Var v) ^ i. (term,i)\<leftarrow>((filter (\<lambda>(x,_). x\<noteq>0) (to_list v p)))]"
proof-
  define L where "L = to_list v p"
  have "(\<Sum>(term, i)\<leftarrow>to_list v p. term * Var v ^ i) = (\<Sum>(term, i)\<leftarrow>filter (\<lambda>(x, _). x \<noteq> 0) (to_list v p). term * Var v ^ i)"
    unfolding L_def[symmetric] apply(induction L) by auto
  then show ?thesis
    using to_list_p[of p v] by auto
qed

end