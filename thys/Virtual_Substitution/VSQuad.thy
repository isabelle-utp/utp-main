subsection "Recursive QE"
theory VSQuad
  imports EqualityVS GeneralVSProofs Reindex OptimizationProofs DNF
begin

lemma existN_eval : "\<forall>xs. eval (ExN n \<phi>) xs = (\<exists>L. (length L = n \<and> eval \<phi> (L@xs)))"
proof(induction n)
  case 0
  then show ?case  by simp
next
  case (Suc n)
  {fix xs
    have "eval (ExN (Suc n) \<phi>) xs = (\<exists>l. length l = Suc n \<and> eval \<phi> (l @ xs))"
      by simp
    also have "... = (\<exists>x.\<exists>L. (length L = n \<and> eval \<phi> (L@(x#xs))))"
    proof safe
      fix l
      assume h : "length l = Suc n" "eval \<phi> (l @ xs)"
      show "\<exists>x L. length L = n \<and> eval \<phi> (L @ x # xs)"
        apply(rule exI[where x="l ! n"])
        apply(rule exI[where x="take n l"])
        using h apply auto
        by (metis Cons_nth_drop_Suc append.assoc append_Cons append_take_drop_id lessI order_refl self_append_conv self_append_conv2 take_all)
    next
      fix x L
      assume h : "eval \<phi> (L @ x # xs)" "n = length L"
      show "\<exists>l. length l = Suc (length L) \<and> eval \<phi> (l @ xs)"
        apply(rule exI[where x="L@[x]"])
        using h by auto
    qed
    also have "... = (\<exists>x.\<exists>L. (length L = n \<and> eval \<phi> ((L@[x])@xs)))"
      by simp
    also have "... = (\<exists>x.\<exists>L. (length (L@[x]) = (Suc n) \<and> eval \<phi> ((L@[x])@xs)))"
      by simp
    also have "... = (\<exists>L. (length L = (Suc n) \<and> eval \<phi> (L@xs)))"
      by (metis append_butlast_last_id length_0_conv nat.simps(3))
    finally have "eval (ExN (Suc n) \<phi>) xs = (\<exists>L. (length L = (Suc n) \<and> eval \<phi> (L@xs)))"
      by simp
  }
  then show ?case by simp
qed




lemma boundedFlipNegQuantifier : "(\<not>(\<forall>x\<in>A. \<not> P x)) = (\<exists>x\<in>A. P x)"
  by blast


theorem QE_dnf'_eval: 
  assumes steph : "\<And>amount F \<Gamma>.
    (\<exists>xs. (length xs = amount \<and> eval (list_disj (map(\<lambda>(L,F,n). ExN n (list_conj (map fm.Atom L @ F))) F))  (xs @ \<Gamma>))) = (eval (step amount F)  \<Gamma>)"
  assumes opt : "\<And>xs F . eval (opt F) xs = eval F xs"
  shows "eval (QE_dnf' opt step \<phi>) xs = eval \<phi> xs"
proof(induction \<phi> arbitrary : xs)
  case (Atom x)
  then show ?case by (simp add: simp_atom_eval)
next
  case (And \<phi>1 \<phi>2)
  then show ?case by (simp add: eval_and) 
next
  case (Or \<phi>1 \<phi>2)
  then show ?case by (simp add: eval_or) 
next
  case (Neg \<phi>)
  then show ?case  apply simp
    by (metis  eval_neg )  
next
  case (ExQ \<phi>)
  have h1 : "\<And>F. (\<exists>xs. length xs = Suc 0 \<and>
          F xs) = (\<exists>x.
          F [x])"
    by (metis length_0_conv length_Suc_conv)
  show ?case
    apply simp 
    unfolding steph[symmetric] apply(simp add: eval_list_disj)
    unfolding h1 apply(rule ex_cong1)
    unfolding ExQ[symmetric]
    unfolding opt[symmetric, of "(QE_dnf' opt step \<phi>)"]
    unfolding dnf_modified_eval[symmetric, of "(opt (QE_dnf' opt step \<phi>))"]
    apply(rule bex_cong) apply simp
    subgoal for x f
      apply(cases f)
      apply (auto simp add:eval_list_conj)
      by (metis Un_iff eval.simps(1) imageI)
    done
next
  case (AllQ \<phi>)
  have h1 : "\<And>F. (\<forall>xs::real list. (length xs = Suc 0 \<longrightarrow>
          F xs)) = (\<forall>x.
          F [x])"
    by (metis length_0_conv length_Suc_conv)
  show ?case
    apply simp
    unfolding steph[symmetric] apply(simp add: eval_list_disj)
    unfolding h1 apply(rule all_cong1)
    unfolding AllQ[symmetric]
    unfolding eval_neg[symmetric, of "(QE_dnf' opt step \<phi>)"]
    unfolding opt[symmetric, of "neg(QE_dnf' opt step \<phi>)"]
    unfolding Set.bex_simps(8)[symmetric] HOL.Not_eq_iff
    unfolding dnf_modified_eval[symmetric, of "(opt (neg(QE_dnf' opt step \<phi>)))"]
    apply(rule bex_cong) apply simp
    subgoal for x f
      apply(cases f)
      apply (auto simp add:eval_list_conj)
      by (metis Un_iff eval.simps(1) imageI)
    done
next
  case (ExN amount \<phi>)
  show ?case
    apply(cases amount)
    apply (simp_all add: ExN)
    unfolding steph[symmetric] apply(simp add: eval_list_disj)
    unfolding ExN[symmetric]
    unfolding opt[of "(QE_dnf' opt step \<phi>)",symmetric]
    unfolding dnf_modified_eval[of "(opt (QE_dnf' opt step \<phi>))",symmetric]
    apply(rule ex_cong1)
    subgoal for nat xs
      apply(cases "length xs = Suc nat")
      apply simp_all
      apply(rule bex_cong)
      apply simp_all
      subgoal for f
        apply(cases f)
        apply simp
        apply(rule ex_cong1)
        unfolding eval_list_conj
        apply auto
        by (meson Un_iff eval.simps(1) imageI)
      done
    done
next
  case (AllN amount \<phi>)
  show ?case
    apply(cases amount)
    apply (simp_all add: AllN)
    unfolding steph[symmetric] apply(simp add: eval_list_disj)
    unfolding AllN[symmetric]
    unfolding eval_neg[symmetric, of "(QE_dnf' opt step \<phi>)"]
    unfolding opt[symmetric, of "neg(QE_dnf' opt step \<phi>)"]
    unfolding Set.bex_simps(8)[symmetric]
    unfolding HOL.imp_conv_disj
    unfolding HOL.de_Morgan_conj[symmetric]
    unfolding HOL.not_ex[symmetric]
    unfolding  HOL.Not_eq_iff
    unfolding dnf_modified_eval[symmetric, of "(opt (neg(QE_dnf' opt step \<phi>)))"]
    apply(rule ex_cong1)
    subgoal for nat xs
      apply(cases "length xs = Suc nat")
      apply simp_all
      apply(rule bex_cong)
      apply simp_all
      subgoal for f
        apply(cases f)
        apply simp
        apply(rule ex_cong1)
        unfolding eval_list_conj
        apply auto
        by (meson Un_iff eval.simps(1) imageI)
      done
    done
qed auto



theorem QE_dnf_eval: 
  assumes steph : "\<And>var amount new L F \<Gamma>.
  amount\<le>var+1 \<Longrightarrow>
    (\<exists>xs. (length xs = var+1 \<and> eval (list_conj (map fm.Atom L @ F)) (xs @ \<Gamma>))) = (\<exists>xs. (length xs = var+1 \<and>eval (step amount var L F) (xs @ \<Gamma>)))"
  assumes opt : "\<And>xs F . eval (opt F) xs = eval F xs"
  shows "eval (QE_dnf opt step \<phi>) xs = eval \<phi> xs"
proof(induction \<phi> arbitrary:xs)
  case (Atom x)
  then show ?case by (simp add: simp_atom_eval)
next
  case (And \<phi>1 \<phi>2)
  then show ?case by (simp add: eval_and) 
next
  case (Or \<phi>1 \<phi>2)
  then show ?case by (simp add: eval_or) 
next
  case (Neg \<phi>)
  then show ?case 
    by (metis eval.simps(6) eval_neg QE_dnf.simps(3))  
next
  case (ExQ \<phi>)
  have h : "(\<exists>x. \<exists>(al, fl, n)\<in>set (dnf_modified (opt (QE_dnf opt step \<phi>))).
            \<exists>L. length L = n \<and> (\<forall>a\<in>set al. aEval a (L @ x # xs)) \<and> (\<forall>f\<in>set fl. eval f (L @ x # xs))) = 
        (\<exists>(al, fl, n)\<in>set (dnf_modified (opt (QE_dnf opt step \<phi>))). \<exists>x. 
            \<exists>L. length L = n \<and> (\<forall>a\<in>set al. aEval a (L @ x # xs)) \<and> (\<forall>f\<in>set fl. eval f (L @ x # xs)))"
    apply safe
    by blast+
  have lessThan : "\<And>c. Suc 0 \<le> c + 1"
    by simp 
  show ?case apply (simp add:eval_list_disj)
    unfolding ExQ[symmetric]
    unfolding opt[symmetric, of "(QE_dnf opt step \<phi>)"]
    unfolding dnf_modified_eval[symmetric, of "opt(QE_dnf opt step \<phi>)"]
    unfolding h
    apply(rule bex_cong)
    apply simp
    subgoal for f
      apply(cases f)
      apply simp
      subgoal for a b c
        using steph[of "Suc 0" c a b xs, symmetric, OF lessThan] apply (simp add:eval_list_conj)
        apply safe
        subgoal for xs' l' l''
          apply(rule exI[where x="l'!c"])
          apply(rule exI[where x="take c l'"])
          apply auto
          apply (metis Un_iff append.assoc append_Cons append_Nil eval.simps(1) image_eqI lessI order_refl take_Suc_conv_app_nth take_all)
          by (metis Un_iff append.assoc append_Cons append_Nil lessI order_refl take_Suc_conv_app_nth take_all)
        subgoal for A B C D
          apply(rule exI[where x="D@[C]"]) by auto
        subgoal for A B
          apply(rule exI[where x="B@[A]"]) by auto
        done
      done
    done
next
  case (AllQ \<phi>)
  have h : "(\<exists>x. \<exists>(al, fl, n)\<in>set (dnf_modified (opt (neg(QE_dnf opt step \<phi>)))).
            \<exists>L. length L = n \<and> (\<forall>a\<in>set al. aEval a (L @ x # xs)) \<and> (\<forall>f\<in>set fl. eval f (L @ x # xs))) = 
        (\<exists>(al, fl, n)\<in>set (dnf_modified (opt (neg(QE_dnf opt step \<phi>)))). \<exists>x. 
            \<exists>L. length L = n \<and> (\<forall>a\<in>set al. aEval a (L @ x # xs)) \<and> (\<forall>f\<in>set fl. eval f (L @ x # xs)))"
    apply safe
    by blast+
  have lessThan : "\<And>c. Suc 0 \<le> c + 1"
    by simp 
  show ?case
    apply (simp add:eval_list_disj)
    unfolding AllQ[symmetric]
    unfolding eval_neg[symmetric, of "(QE_dnf opt step \<phi>)"]
    unfolding opt[symmetric, of "neg(QE_dnf opt step \<phi>)"]
    unfolding HOL.Not_eq_iff[symmetric, of "(\<forall>f\<in>set (dnf_modified (opt (neg (QE_dnf opt step \<phi>)))). \<not> eval (case f of (al, fl, n) \<Rightarrow> ExN (Suc n) (step (Suc 0) n al fl)) xs)"]
    unfolding SMT.verit_connective_def(3)[symmetric]
    unfolding boundedFlipNegQuantifier
    unfolding dnf_modified_eval[symmetric, of "opt(neg(QE_dnf opt step \<phi>))"]
    unfolding h
    apply(rule bex_cong)
    apply simp
    subgoal for f
      apply(cases f)
      apply simp
      subgoal for a b c
        using steph[of "Suc 0" c a b xs, symmetric,OF lessThan] apply (simp add:eval_list_conj)
        apply safe
        subgoal for xs' l' l''
          apply(rule exI[where x="l'!c"])
          apply(rule exI[where x="take c l'"])
          apply auto
          apply (metis Un_iff append.assoc append_Cons append_Nil eval.simps(1) image_eqI lessI order_refl take_Suc_conv_app_nth take_all)
          by (metis Un_iff append.assoc append_Cons append_Nil lessI order_refl take_Suc_conv_app_nth take_all)
        subgoal for A B C D
          apply(rule exI[where x="D@[C]"]) by auto
        subgoal for A B
          apply(rule exI[where x="B@[A]"]) by auto
        done
      done
    done
next
  case (ExN x1 \<phi>)
  show ?case
  proof(cases x1)
    case 0
    then show ?thesis using ExN by simp
  next
    case (Suc nat)
    have h : "(\<exists>l. length l = Suc nat \<and>
         (\<exists>(al, fl, n)\<in>set (dnf_modified (opt (QE_dnf opt step \<phi>))).
             \<exists>L. length L = n \<and> (\<forall>a\<in>set al. aEval a (L @ l @ xs)) \<and> (\<forall>f\<in>set fl. eval f (L @ l @ xs)))) = 
        (\<exists>(al, fl, n)\<in>set (dnf_modified (opt (QE_dnf opt step \<phi>))). (\<exists>l. length l = Suc nat \<and>
             (\<exists>L. length L = n \<and> (\<forall>a\<in>set al. aEval a (L @ l @ xs)) \<and> (\<forall>f\<in>set fl. eval f (L @ l @ xs)))))"
      apply safe
      by blast+
    have lessThan : "\<And>c. Suc nat \<le> c + nat + 1" by simp
    show ?thesis
      apply (simp add:eval_list_disj Suc)
      unfolding ExN[symmetric]
      unfolding opt[symmetric, of "(QE_dnf opt step \<phi>)"]
      unfolding dnf_modified_eval[symmetric, of "(opt (QE_dnf opt step \<phi>))"]
      unfolding h
      apply(rule bex_cong)
      apply simp
      subgoal for f
        apply(cases f)
        subgoal for a b c
          apply simp
          using steph[of "Suc nat" "c+nat",symmetric, OF lessThan]
          apply (auto simp add:eval_list_conj)
          subgoal for L
            apply(rule exI[where x="drop c L"])
            apply auto
            apply(rule exI[where x="take c L"])
            apply auto
            apply (metis Un_iff append.assoc append_take_drop_id eval.simps(1) image_eqI)
            by (metis Un_iff append.assoc append_take_drop_id)
          subgoal for L l
            apply(rule exI[where x="l@L"])
            by auto
          done
        done
      done
  qed
next
  case (AllN x1 \<phi>)
  then show ?case 
  proof(cases x1)
    case 0
    then show ?thesis using AllN by simp
  next
    case (Suc nat)
    have h : "(\<exists>l. length l = Suc nat \<and>
         (\<exists>(al, fl, n)\<in>set (dnf_modified (opt (neg(QE_dnf opt step \<phi>)))).
             \<exists>L. length L = n \<and> (\<forall>a\<in>set al. aEval a (L @ l @ xs)) \<and> (\<forall>f\<in>set fl. eval f (L @ l @ xs)))) = 
        (\<exists>(al, fl, n)\<in>set (dnf_modified (opt (neg(QE_dnf opt step \<phi>)))). (\<exists>l. length l = Suc nat \<and>
             (\<exists>L. length L = n \<and> (\<forall>a\<in>set al. aEval a (L @ l @ xs)) \<and> (\<forall>f\<in>set fl. eval f (L @ l @ xs)))))"
      apply safe
      by blast+
    have lessThan : "\<And>c. Suc nat \<le> c + nat + 1" by simp
    show ?thesis
      apply (simp add:eval_list_disj Suc)
      unfolding AllN[symmetric]
      unfolding eval_neg[symmetric, of "QE_dnf opt step \<phi>"]
      unfolding HOL.imp_conv_disj
      unfolding HOL.de_Morgan_conj[symmetric]
      unfolding opt[symmetric, of "neg(QE_dnf opt step \<phi>)"]
      unfolding dnf_modified_eval[symmetric, of "(opt (neg(QE_dnf opt step \<phi>)))"]
      unfolding HOL.Not_eq_iff[symmetric, of "(\<forall>f\<in>set (dnf_modified (opt (neg (QE_dnf opt step \<phi>)))).
        \<not> eval (case f of (al, fl, n) \<Rightarrow> ExN (Suc (n + nat)) (step (Suc nat) (n + nat) al fl)) xs)"]
      unfolding SMT.verit_connective_def(3)[symmetric]
      unfolding boundedFlipNegQuantifier
      unfolding h
      apply(rule bex_cong)
      apply simp
      subgoal for f
        apply(cases f)
        subgoal for a b c
          apply simp
          using steph[of "Suc nat" "c+nat",symmetric, OF lessThan]
          apply (auto simp add:eval_list_conj)
          subgoal for L
            apply(rule exI[where x="drop c L"])
            apply auto
            apply(rule exI[where x="take c L"])
            apply auto
            apply (metis Un_iff append.assoc append_take_drop_id eval.simps(1) image_eqI)
            by (metis Un_iff append.assoc append_take_drop_id)
          subgoal for L l
            apply(rule exI[where x="l@L"])
            by auto
          done
        done
      done
  qed
qed auto

lemma opt: "eval ((push_forall \<circ> nnf \<circ> unpower 0 o groupQuantifiers o clearQuantifiers) F) L= eval F L"
  using push_forall_eval eval_nnf unpower_eval groupQuantifiers_eval clearQuantifiers_eval by auto

lemma opt': "eval ((push_forall ( nnf ( unpower 0 ( groupQuantifiers (clearQuantifiers F)))))) L= eval F L"
  using push_forall_eval eval_nnf unpower_eval groupQuantifiers_eval clearQuantifiers_eval by auto

lemma opt_no_group: "eval ((push_forall \<circ> nnf \<circ> unpower 0 o clearQuantifiers) F) L= eval F L"
  using push_forall_eval eval_nnf unpower_eval clearQuantifiers_eval by auto



lemma  repeatAmountOfQuantifiers_helper_eval : 
  assumes  "\<And>xs F. eval F xs = eval (step F) xs"
  shows  "eval F xs = eval (repeatAmountOfQuantifiers_helper step n F) xs"
  apply(induction n arbitrary : F)
  apply simp_all
  subgoal for n F
    using assms[of F xs] by auto
  done


lemma  repeatAmountOfQuantifiers_eval : 
  assumes  "\<And>xs F. eval F xs = eval (step F) xs"
  shows  "eval F xs = eval (repeatAmountOfQuantifiers step F) xs"
proof-
  define F' where "F' = step F"
  have h:  "eval F xs = eval F' xs"
    using assms unfolding F'_def by auto
  show ?thesis
    apply (simp add: F'_def[symmetric] h)
    using repeatAmountOfQuantifiers_helper_eval[OF assms] by auto
qed

end
