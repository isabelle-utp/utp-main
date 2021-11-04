section "QE Algorithm Proofs"
subsection "DNF"
theory DNF
  imports VSAlgos
begin


theorem dnf_eval : 
  "(\<exists>(al,fl)\<in>set (dnf \<phi>). 
     (\<forall>a\<in>set al. aEval a xs) 
   \<and> (\<forall>f\<in>set fl. eval f xs))
   = eval \<phi> xs"
proof(induction \<phi>)
  case (And \<phi>1 \<phi>2)
  define f where "f = (\<lambda>a. case a of
        (al, fl) \<Rightarrow> (\<forall>a\<in>set al. aEval a xs) \<and> (\<forall>f\<in>set fl. eval f xs))"
  have h1:"(\<exists>a\<in>set (dnf (And \<phi>1 \<phi>2)). f a) = (\<exists>a\<in>set (dnf \<phi>1). \<exists>a'\<in>set(dnf \<phi>2). f a \<and> f a')"
    apply simp unfolding f_def apply auto
      apply blast
     apply blast
    subgoal for a b c d
      apply(rule bexI[where x="(a,b)"])
       apply(rule exI[where x="a@c"])
       apply(rule exI[where x="b@d"])
      by auto
    done
  also have h2 : "... = ((\<exists>a\<in>set (dnf \<phi>1). f a)\<and>(\<exists>a\<in>set(dnf \<phi>2). f a))"
    by auto
  show ?case unfolding f_def[symmetric] unfolding h1 h2 unfolding f_def using And by auto
qed auto


theorem dnf_modified_eval : 
  "(\<exists>(al,fl,n)\<in>set (dnf_modified \<phi>).
      (\<exists>L. (length L = n 
       \<and> (\<forall>a\<in>set al. aEval a (L@xs))
       \<and> (\<forall>f\<in>set fl. eval f (L@xs))))) = eval \<phi> xs"
proof(induction \<phi> arbitrary:xs)
  case (Atom x)
  then show ?case
    by (cases x, auto)
next
  case (And \<phi>1 \<phi>2)
  {fix d1 d2 A A' B B' L1 L2
    assume A : "(A,A',length (L1::real list))\<in>set (dnf_modified \<phi>1)" and "(B,B',length (L2::real list))\<in>set (dnf_modified \<phi>2)"
    have "(
      (\<forall>a\<in>set ((map (liftAtom (length L1) (length L2)) A @ map (liftAtom 0 (length L1)) B)). aEval a ((L1@L2) @ xs)) 
    \<and> (\<forall>f\<in>set ( map (liftFm (length L1) (length L2)) A' @ map (liftFm 0 (length L1)) B'). eval f ((L1@L2) @ xs))) = 
      (
      (\<forall>a\<in>set(map (liftAtom (length L1) (length L2)) A) \<union> set( map (liftAtom 0 (length L1)) B). aEval a ((L1@L2) @ xs)) 
    \<and> (\<forall>f\<in>set( map (liftFm (length L1) (length L2)) A') \<union> set(map (liftFm 0 (length L1)) B'). eval f ((L1@L2) @ xs)))"
      by auto
    also have "... = (
      (\<forall>a\<in>set(map (liftAtom (length L1) (length L2)) A).aEval a ((L1@L2) @ xs))
    \<and> (\<forall>a\<in>set(map (liftAtom 0 (length L1)) B). aEval a ((L1@L2) @ xs)) 
    \<and> (\<forall>f\<in>set(map (liftFm (length L1) (length L2)) A').eval f ((L1@L2) @ xs))
    \<and> (\<forall>f\<in>set(map (liftFm 0 (length L1)) B'). eval f ((L1@L2) @ xs)))"
      by blast
    also have "... =  (
      (\<forall>a\<in>set A. aEval (liftAtom (length L1) (length L2) a) ((L1@L2) @ xs))
    \<and> (\<forall>a\<in>set B. aEval (liftAtom 0 (length L1) a) ((L1@L2) @ xs)) 
    \<and> (\<forall>f\<in>set A'. eval (liftFm (length L1) (length L2) f) ((L1@L2) @ xs))
    \<and> (\<forall>f\<in>set B'. eval (liftFm 0 (length L1) f) ((L1@L2) @ xs)))"
      by simp 
    also have "... =  (
      (\<forall>a\<in>set A. aEval (liftAtom (length L1) (length L2) a) (insert_into (L1 @ xs) (length L1) L2))
    \<and> (\<forall>a\<in>set B. aEval (liftAtom 0 (length L1) a) (insert_into (L2 @ xs) 0 L1)) 
    \<and> (\<forall>f\<in>set A'. eval (liftFm (length L1) (length L2) f) (insert_into (L1 @ xs) (length L1) L2))
    \<and> (\<forall>f\<in>set B'. eval (liftFm 0 (length L1) f) (insert_into (L2 @ xs) 0 L1)))"
      by auto
    also have "... = ( 
          ((\<forall>a\<in>set A. aEval a (L1 @ xs)) \<and> (\<forall>f\<in>set A'. eval f (L1 @ xs))) \<and> 
          ((\<forall>a\<in>set B. aEval a (L2 @ xs)) \<and> (\<forall>f\<in>set B'. eval f (L2 @ xs))) )"
    proof safe
      fix a
      show "\<forall>a\<in>set A. aEval (liftAtom (length L1) (length L2) a) (insert_into (L1 @ xs) (length L1) L2) \<Longrightarrow>
           a \<in> set A \<Longrightarrow> aEval a (L1 @ xs)"
        using eval_liftFm[of L2 "length L2" "length L1" "L1 @ xs" "Atom a", OF refl]
        by auto
    next
      fix f
      show "\<forall>f\<in>set A'. eval (liftFm (length L1) (length L2) f) (insert_into (L1 @ xs) (length L1) L2) \<Longrightarrow>
          f \<in> set A' \<Longrightarrow> eval f (L1 @ xs)"
        using eval_liftFm[of L2 "length L2" "length L1" "L1 @ xs" f, OF refl] by auto
    next 
      fix a
      show " \<forall>a\<in>set B. aEval (liftAtom 0 (length L1) a) (insert_into (L2 @ xs) 0 L1) \<Longrightarrow>
            a \<in> set B \<Longrightarrow> aEval a (L2 @ xs)"
        using eval_liftFm[of L1 "length L1" "0" "L2@xs" "Atom a", OF refl] by auto
    next
      fix f
      show " \<forall>f\<in>set B'. eval (liftFm 0 (length L1) f) (insert_into (L2 @ xs) 0 L1) \<Longrightarrow> f \<in> set B' \<Longrightarrow> eval f (L2 @ xs)"
        using eval_liftFm[of L1 "length L1" "0" "L2 @ xs" f, OF refl] by auto
    next
      fix a
      show " \<forall>a\<in>set A. aEval a (L1 @ xs) \<Longrightarrow>
         a \<in> set A \<Longrightarrow> aEval (liftAtom (length L1) (length L2) a) (insert_into (L1 @ xs) (length L1) L2)"
        using eval_liftFm[of L2 "length L2" "length L1" "L1 @ xs" "Atom a", OF refl] by auto
    next
      fix a
      show "\<forall>a\<in>set B. aEval a (L2 @ xs) \<Longrightarrow> a \<in> set B \<Longrightarrow> aEval (liftAtom 0 (length L1) a) (insert_into (L2 @ xs) 0 L1)"
        using eval_liftFm[of L1 "length L1" "0" "L2@xs" "Atom a", OF refl] by auto
    next
      fix f 
      show "\<forall>f\<in>set A'. eval f (L1 @ xs) \<Longrightarrow>
         f \<in> set A' \<Longrightarrow> eval (liftFm (length L1) (length L2) f) (insert_into (L1 @ xs) (length L1) L2)"
        using eval_liftFm[of L2 "length L2" "length L1" "L1 @ xs" f, OF refl] by auto
    next
      fix f
      show "\<forall>f\<in>set B'. eval f (L2 @ xs) \<Longrightarrow> f \<in> set B' \<Longrightarrow> eval (liftFm 0 (length L1) f) (insert_into (L2 @ xs) 0 L1)"
        using eval_liftFm[of L1 "length L1" "0" "L2 @ xs" f, OF refl] by auto
    qed
    finally have "(
      (\<forall>a\<in>set ((map (liftAtom (length L1) (length L2)) A @ map (liftAtom 0 (length L1)) B)). aEval a ((L1@L2) @ xs)) 
    \<and> (\<forall>f\<in>set ( map (liftFm (length L1) (length L2)) A' @ map (liftFm 0 (length L1)) B'). eval f ((L1@L2) @ xs))) = ( 
          ((\<forall>a\<in>set A. aEval a (L1 @ xs)) \<and> (\<forall>f\<in>set A'. eval f (L1 @ xs))) \<and> 
          ((\<forall>a\<in>set B. aEval a (L2 @ xs)) \<and> (\<forall>f\<in>set B'. eval f (L2 @ xs))) )"
      by simp
  }
  then have h : "(\<exists>(A,A',d1)\<in>set (dnf_modified \<phi>1). \<exists>(B,B',d2)\<in>set (dnf_modified \<phi>2).
      (\<exists>L1.\<exists>L2. length L1 = d1 \<and> length L2 = d2 \<and> 
      (\<forall>a\<in>set ((map (liftAtom d1 d2) A @ map (liftAtom 0 d1) B)). aEval a ((L1@L2) @ xs)) 
    \<and> (\<forall>f\<in>set ( map (liftFm d1 d2) A' @ map (liftFm 0 d1) B'). eval f ((L1@L2) @ xs)))) = ((\<exists>(A,A',d1)\<in>set (dnf_modified \<phi>1). \<exists>(B,B',d2)\<in>set(dnf_modified \<phi>2). 
          (\<exists>L1. length L1 = d1 \<and> (\<forall>a\<in>set A. aEval a (L1 @ xs)) \<and> (\<forall>f\<in>set A'. eval f (L1 @ xs))) \<and> 
          (\<exists>L2. length L2 = d2 \<and> (\<forall>a\<in>set B. aEval a (L2 @ xs)) \<and> (\<forall>f\<in>set B'. eval f (L2 @ xs))) ))"
  proof safe
    fix A A' B B'  L1 L2
    assume prev : "(\<And>A A' L1 B B' L2.
           (A, A', length L1) \<in> set (dnf_modified \<phi>1) \<Longrightarrow>
           (B, B', length L2) \<in> set (dnf_modified \<phi>2) \<Longrightarrow>
           ((\<forall>a\<in>set (map (liftAtom (length L1) (length L2)) A @ map (liftAtom 0 (length L1)) B).
                aEval a ((L1 @ L2) @ xs)) \<and>
            (\<forall>f\<in>set (map (liftFm (length L1) (length L2)) A' @ map (liftFm 0 (length L1)) B').
                eval f ((L1 @ L2) @ xs))) =
           (((\<forall>a\<in>set A. aEval a (L1 @ xs)) \<and> (\<forall>f\<in>set A'. eval f (L1 @ xs))) \<and>
            (\<forall>a\<in>set B. aEval a (L2 @ xs)) \<and> (\<forall>f\<in>set B'. eval f (L2 @ xs))))"
      and A: "(A,A',length L1)\<in>set (dnf_modified \<phi>1)" and B: "(B,B',length L2)\<in>set (dnf_modified \<phi>2)"
      and h1 : "\<forall>a\<in>set (map (liftAtom (length L1) (length L2)) A @ map (liftAtom 0 (length L1)) B).
          aEval a ((L1 @ L2) @ xs)"
      and h2 : "\<forall>f\<in>set (map (liftFm (length L1) (length L2)) A' @ map (liftFm 0 (length L1)) B').
          eval f ((L1 @ L2) @ xs)"
    have h : "((\<forall>a\<in>set (map (liftAtom (length L1) (length L2)) A @ map (liftAtom 0 (length L1)) B).
         aEval a ((L1 @ L2) @ xs)) \<and>
     (\<forall>f\<in>set (map (liftFm (length L1) (length L2)) A' @ map (liftFm 0 (length L1)) B').
         eval f ((L1 @ L2) @ xs))) =
    (((\<forall>a\<in>set A. aEval a (L1 @ xs)) \<and> (\<forall>f\<in>set A'. eval f (L1 @ xs))) \<and>
     (\<forall>a\<in>set B. aEval a (L2 @ xs)) \<and> (\<forall>f\<in>set B'. eval f (L2 @ xs)))"
      using prev[where A="A", where A'="A'", where B="B", where B'="B'"] A B by simp
    show "\<exists>(A, A', d1)\<in>set (dnf_modified \<phi>1).
          \<exists>(B, B', d2)\<in>set (dnf_modified \<phi>2).
             (\<exists>L1. length L1 = d1 \<and> (\<forall>a\<in>set A. aEval a (L1 @ xs)) \<and> (\<forall>f\<in>set A'. eval f (L1 @ xs))) \<and>
             (\<exists>L2. length L2 = d2 \<and> (\<forall>a\<in>set B. aEval a (L2 @ xs)) \<and> (\<forall>f\<in>set B'. eval f (L2 @ xs)))"
      apply (rule bexI[where x="(A, A', length L1)", OF _ A])
      apply auto defer
      apply (rule bexI[where x="(B, B', length L2)", OF _ B])
      apply auto
      using h h1 h2
      by auto
  next
    fix A A' d1 B B' d2 L1 L2
    assume prev : "(\<And>A A' L1 B B' L2.
           (A, A', length L1) \<in> set (dnf_modified \<phi>1) \<Longrightarrow>
           (B, B', length L2) \<in> set (dnf_modified \<phi>2) \<Longrightarrow>
           ((\<forall>a\<in>set (map (liftAtom (length L1) (length L2)) A @ map (liftAtom 0 (length L1)) B).
                aEval a ((L1 @ L2) @ xs)) \<and>
            (\<forall>f\<in>set (map (liftFm (length L1) (length L2)) A' @ map (liftFm 0 (length L1)) B').
                eval f ((L1 @ L2) @ xs))) =
           (((\<forall>a\<in>set A. aEval a (L1 @ xs)) \<and> (\<forall>f\<in>set A'. eval f (L1 @ xs))) \<and>
            (\<forall>a\<in>set B. aEval a (L2 @ xs)) \<and> (\<forall>f\<in>set B'. eval f (L2 @ xs))))"
      and A: "(A,A',length L1)\<in>set (dnf_modified \<phi>1)" and B: "(B,B',length L2)\<in>set (dnf_modified \<phi>2)"
      and h1 : "\<forall>a\<in>set A. aEval a (L1 @ xs)" "\<forall>f\<in>set A'. eval f (L1 @ xs)"
      "\<forall>a\<in>set B. aEval a (L2 @ xs)" "\<forall>f\<in>set B'. eval f (L2 @ xs)"
    have h : "((\<forall>a\<in>set (map (liftAtom (length L1) (length L2)) A @ map (liftAtom 0 (length L1)) B).
         aEval a ((L1 @ L2) @ xs)) \<and>
     (\<forall>f\<in>set (map (liftFm (length L1) (length L2)) A' @ map (liftFm 0 (length L1)) B').
         eval f ((L1 @ L2) @ xs))) =
    (((\<forall>a\<in>set A. aEval a (L1 @ xs)) \<and> (\<forall>f\<in>set A'. eval f (L1 @ xs))) \<and>
     (\<forall>a\<in>set B. aEval a (L2 @ xs)) \<and> (\<forall>f\<in>set B'. eval f (L2 @ xs)))"
      using prev[where A="A", where A'="A'", where B="B", where B'="B'"] h1 A B by simp
    show "\<exists>(A, A', d1)\<in>set (dnf_modified \<phi>1).
          \<exists>(B, B', d2)\<in>set (dnf_modified \<phi>2).
             \<exists>L1 L2.
                length L1 = d1 \<and>
                length L2 = d2 \<and>
                (\<forall>a\<in>set (map (liftAtom d1 d2) A @ map (liftAtom 0 d1) B). aEval a ((L1 @ L2) @ xs)) \<and>
                (\<forall>f\<in>set (map (liftFm d1 d2) A' @ map (liftFm 0 d1) B'). eval f ((L1 @ L2) @ xs))"
      apply (rule bexI[where x="(A, A', length L1)", OF _ A])
      apply auto defer
      apply (rule bexI[where x="(B, B', length L2)", OF _ B])
      apply auto
      apply (rule exI[where x="L1"])
      apply auto
      apply (rule exI[where x="L2"])
      apply auto
      using h h1 by auto
  qed

  define f where "f (x:: (atom list * atom fm list * nat)) = (case x of (al,fl,n) \<Rightarrow> (\<exists>L. length L = n \<and> (\<forall>a\<in>set al. aEval a (L @ xs)) \<and> (\<forall>f\<in>set fl. eval f (L @ xs))))" for x
  define g where "((g (uuaa::atom list) (uua::atom fm list) (uu::nat) x):: (atom list * atom fm list * nat)) = (
 case x of
                       (B, B', d2) \<Rightarrow>
                         (map (liftAtom uu d2) uuaa @ map (liftAtom 0 uu) B,
                          map (\<lambda>x. map_fm_binders (\<lambda>a x. liftAtom (uu + x) d2 a) x 0) uua @
                          map (\<lambda>x. map_fm_binders (\<lambda>a x. liftAtom (0 + x) uu a) x 0) B',
                          uu + d2))" for uuaa uua uu x

  define f' where "f' L A A' d1 B B' d2 = ((\<forall>a\<in>set ((map (liftAtom d1 d2) A @ map (liftAtom 0 d1) B)). aEval a (L @ xs)) 
    \<and> (\<forall>f\<in>set ( map (liftFm d1 d2) A' @ map (liftFm 0 d1) B'). eval f (L @ xs)))" for L A A' d1 B B' d2
  have "(\<exists>(al, fl, n)\<in>set (dnf_modified (And \<phi>1 \<phi>2)).
               \<exists>L. length L = n \<and> (\<forall>a\<in>set al. aEval a (L @ xs)) \<and> (\<forall>f\<in>set fl. eval f (L @ xs)))
        = (\<exists>y\<in>set (dnf_modified (And \<phi>1 \<phi>2)). f y)"
    unfolding f_def by simp
  also have "... = (\<exists>y\<in>set (dnf_modified \<phi>1).
        \<exists>a aa b.
           (\<exists>uu uua uuaa.
               (uuaa, uua, uu) = y \<and>
               (a, aa, b)
               \<in> (g uuaa uua uu) `
                  set (dnf_modified \<phi>2)) \<and>
           f (a, aa, b))"
    using g_def by simp
  also have "... = (\<exists>(A,A',d1)\<in>set (dnf_modified \<phi>1).
        \<exists>x\<in>set (dnf_modified \<phi>2).
           f (g A A' d1 x))"
    by (smt case_prodE f_def imageE image_eqI prod.simps(2))
  also have "... = (\<exists>(A,A',d1)\<in>set (dnf_modified \<phi>1).
        \<exists>x\<in>set (dnf_modified \<phi>2).
           f (case x of (B,B',d2) \<Rightarrow> (map (liftAtom d1 d2) A @ map (liftAtom 0 d1) B,
                          map (\<lambda>x. liftFm d1 d2 x) A' @
                          map (\<lambda>x. liftFm 0 d1 x) B',
                          d1 + d2)))"
    using g_def by simp 
  also have "... = (\<exists>(A,A',d1)\<in>set (dnf_modified \<phi>1). \<exists>x\<in>set (dnf_modified \<phi>2).
      (case (case x of (B,B',d2) \<Rightarrow> (map (liftAtom d1 d2) A @ map (liftAtom 0 d1) B,
                          map (\<lambda>x. liftFm d1 d2 x) A' @ map (\<lambda>x. liftFm 0 d1 x) B',
                          d1 + d2)) of (al,fl,n) \<Rightarrow> (\<exists>L. length L = n \<and> (\<forall>a\<in>set al. aEval a (L @ xs)) \<and> (\<forall>f\<in>set fl. eval f (L @ xs))))
)"
    using f_def by simp
  also have "... = (\<exists>(A,A',d1)\<in>set (dnf_modified \<phi>1). \<exists>(B,B',d2)\<in>set (dnf_modified \<phi>2).
      (case ((map (liftAtom d1 d2) A @ map (liftAtom 0 d1) B,
                          map (\<lambda>x. liftFm d1 d2 x) A' @ map (\<lambda>x. liftFm 0 d1 x) B',
                          d1 + d2)) of (al,fl,n) \<Rightarrow> (\<exists>L. length L = n \<and> (\<forall>a\<in>set al. aEval a (L @ xs)) \<and> (\<forall>f\<in>set fl. eval f (L @ xs))))
)"  
    by(smt case_prodE case_prodE2 old.prod.case)
  also have "... = (\<exists>(A,A',d1)\<in>set (dnf_modified \<phi>1). \<exists>(B,B',d2)\<in>set (dnf_modified \<phi>2).
      (\<exists>L. length L = d1 + d2 \<and> 
      (\<forall>a\<in>set ((map (liftAtom d1 d2) A @ map (liftAtom 0 d1) B)). aEval a (L @ xs)) 
    \<and> (\<forall>f\<in>set ( map (liftFm d1 d2) A' @ map (liftFm 0 d1) B'). eval f (L @ xs))))"  
    by(smt case_prodE case_prodE2 old.prod.case)
  also have "... = (\<exists>(A,A',d1)\<in>set (dnf_modified \<phi>1). \<exists>(B,B',d2)\<in>set (dnf_modified \<phi>2).
      (\<exists>L. length L = d1 + d2 \<and> (f' L A A' d1 B B' d2)))"  
    using f'_def by simp
  also have "... = (\<exists>(A,A',d1)\<in>set (dnf_modified \<phi>1). \<exists>(B,B',d2)\<in>set (dnf_modified \<phi>2).
      (\<exists>L1.\<exists>L2. length L1 = d1 \<and> length L2 = d2 \<and> (f' (L1@L2) A A' d1 B B' d2)))"
  proof safe
    fix A A' d1 B B' d2 L
    assume A: "(A,A',d1)\<in>set (dnf_modified \<phi>1)" and B: "(B,B',d2)\<in>set (dnf_modified \<phi>2)"
      and L: "length L = d1 + d2" "(f' L A A' d1 B B' d2)"
    show "\<exists>(A, A', d1)\<in>set (dnf_modified \<phi>1).
          \<exists>(B, B', d2)\<in>set (dnf_modified \<phi>2). \<exists>L1 L2. length L1 = d1 \<and> length L2 = d2 \<and> f' (L1 @ L2) A A' d1 B B' d2"
      apply (rule bexI[where x="(A, A', d1)", OF _ A])
      apply auto
      apply (rule bexI[where x="(B, B', d2)", OF _ B])
      apply auto
      apply (rule exI[where x="take d1 L"])
      apply auto   defer
      apply (rule exI[where x="drop d1 L"])
      using L
      by auto
  next
    fix A A' d1 B B' d2 L1 L2
    assume A: "(A,A', length L1)\<in>set (dnf_modified \<phi>1)" and B: "(B,B',length L2)\<in>set (dnf_modified \<phi>2)"
      and L: "(f' (L1 @ L2) A A' (length L1) B B' (length L2))"
    thm exI
    thm bexI
    show "\<exists>(A, A', d1)\<in>set (dnf_modified \<phi>1). \<exists>(B, B', d2)\<in>set (dnf_modified \<phi>2). \<exists>L. length L = d1 + d2 \<and> f' L A A' d1 B B' d2 "
      apply (rule bexI[where x="(A, A', length L1)", OF _ A])
      apply auto
      apply (rule bexI[where x="(B, B', length L2)", OF _ B])
      apply auto
      apply (rule exI[where x="L1 @ L2"])
      using L
      by auto
  qed

  also have "... = (\<exists>(A,A',d1)\<in>set (dnf_modified \<phi>1). \<exists>(B,B',d2)\<in>set (dnf_modified \<phi>2).
      (\<exists>L1.\<exists>L2. length L1 = d1 \<and> length L2 = d2 \<and> 
      (\<forall>a\<in>set ((map (liftAtom d1 d2) A @ map (liftAtom 0 d1) B)). aEval a ((L1@L2) @ xs)) 
    \<and> (\<forall>f\<in>set ( map (liftFm d1 d2) A' @ map (liftFm 0 d1) B'). eval f ((L1@L2) @ xs))))" 
    unfolding f'_def by simp
      (*also have "... = (\<exists>(A,A',d1)\<in>set (dnf_modified \<phi>1). \<exists>(B,B',d2)\<in>set (dnf_modified \<phi>2).
      (\<exists>L1.\<exists>L2. length L1 = d1 \<and> length L2 = d2 \<and> 
      (\<forall>a\<in>set (map (liftAtom d1 d2) A) \<union> set ( map (liftAtom 0 d1) B). aEval a ((L1@L2) @ xs)) 
    \<and> (\<forall>f\<in>set ( map (liftFm d1 d2) A' @ map (liftFm 0 d1) B'). eval f ((L1@L2) @ xs))))"
    proof -
      have *: "(\<forall>a\<in>set (map (liftAtom d1 d2) A @ map (liftAtom 0 d1) B). aEval a ((L1 @ L2) @ xs))
        = (\<forall>a\<in>set (map (liftAtom d1 d2) A) \<union> set ( map (liftAtom 0 d1) B). aEval a ((L1@L2) @ xs))"
        for d1 d2 A B L1 L2 by auto
      then show ?thesis apply (subst * ) ..
    qed (*
      apply (rule bex_cong[OF refl])
      unfolding split_beta
      apply (rule bex_cong[OF refl])
      apply (rule ex_cong1)+
      apply (rule conj_cong refl)+
      by auto *)
    *)
  also have "... = ((\<exists>(A,A',d1)\<in>set (dnf_modified \<phi>1). \<exists>(B,B',d2)\<in>set(dnf_modified \<phi>2). 
          (\<exists>L. length L = d1 \<and> (\<forall>a\<in>set A. aEval a (L @ xs)) \<and> (\<forall>f\<in>set A'. eval f (L @ xs))) \<and> 
          (\<exists>L. length L = d2 \<and> (\<forall>a\<in>set B. aEval a (L @ xs)) \<and> (\<forall>f\<in>set B'. eval f (L @ xs))) ))"
    using h by simp
  also have "... = ((\<exists>(A,A',d1)\<in>set (dnf_modified \<phi>1). \<exists>(B,B',d2)\<in>set(dnf_modified \<phi>2). 
          f (A,A',d1) \<and> 
          f (B,B',d2)))"
    using f_def by simp
  also have "... = ((\<exists>a\<in>set (dnf_modified \<phi>1). \<exists>a1\<in>set(dnf_modified \<phi>2). f a \<and> f a1))"
    by (simp add: Bex_def_raw)
  also have "... = ((\<exists>a\<in>set (dnf_modified \<phi>1). f a) \<and> (\<exists>a\<in>set (dnf_modified \<phi>2). f a))"
    by blast
  also have "... = eval (And \<phi>1 \<phi>2) xs"
    using And f_def by simp
  finally have "(\<exists>(al, fl, n)\<in>set (dnf_modified (And \<phi>1 \<phi>2)).
               \<exists>L. length L = n \<and> (\<forall>a\<in>set al. aEval a (L @ xs)) \<and> (\<forall>f\<in>set fl. eval f (L @ xs))) =
         eval (And \<phi>1 \<phi>2) xs"
    by simp
  then show ?case by simp
next
  case (Or \<phi>1 \<phi>2)
  have h1 : "eval (Or \<phi>1 \<phi>2) xs = eval \<phi>1 xs \<or> eval \<phi>2 xs"
    using eval.simps(5) by blast
  have h2 : "set (dnf_modified (Or \<phi>1 \<phi>2)) = set(dnf_modified \<phi>1) \<union> set(dnf_modified \<phi>2)"
    by simp 
  show ?case using Or h1 h2
    by (metis (no_types, lifting) Un_iff eval.simps(5)) 
next
  case (ExQ \<phi>)
  have h1 : "((\<exists>x. (\<exists>(al, fl, n)\<in>set (dnf_modified \<phi>).
               \<exists>L. length L = n \<and> (\<forall>a\<in>set al. aEval a (L @ (x#xs))) \<and> (\<forall>f\<in>set fl. eval f (L @ (x#xs)))))
              =
              (\<exists>(al, fl, n)\<in>set (dnf_modified \<phi>).
               (\<exists>x.\<exists>L. length L = n \<and> (\<forall>a\<in>set al. aEval a ((L@[x]) @ xs)) \<and> (\<forall>f\<in>set fl. eval f ((L@[x]) @ xs)))))"
    apply simp by blast
  { fix n al fl
    define f where "f L = (length (L:: real list) = ((n::nat)+1) \<and> (\<forall>a\<in>set al. aEval a (L @ xs)) \<and> (\<forall>f\<in>set fl. eval f (L @ xs)))" for L
    have "(\<exists>x.\<exists>L. f (L@[x])) = (\<exists>L. f L)"
      by (metis (full_types) One_nat_def add_Suc_right f_def list.size(3) nat.simps(3) rev_exhaust)
    then have "((\<exists>x. \<exists>L. length (L@[x]) = (n+1) \<and> (\<forall>a\<in>set al. aEval a ((L@[x]) @ xs)) \<and> (\<forall>f\<in>set fl. eval f ((L@[x]) @ xs)))
              =
            (\<exists>L. length L = (n+1) \<and> (\<forall>a\<in>set al. aEval a (L @ xs)) \<and> (\<forall>f\<in>set fl. eval f (L @ xs))))"
      unfolding f_def by simp  
  }
  then have h2 : "\<forall>n al fl. (
              (\<exists>x. \<exists>L. length (L@[x]) = (n+1) \<and> (\<forall>a\<in>set al. aEval a ((L@[x]) @ xs)) \<and> (\<forall>f\<in>set fl. eval f ((L@[x]) @ xs)))
              =
              (\<exists>L. length L = (n+1) \<and> (\<forall>a\<in>set al. aEval a (L @ xs)) \<and> (\<forall>f\<in>set fl. eval f (L @ xs)))
            )"
    by simp
  { fix al fl n
    define f where "f al fl n = (\<exists>L. length L = n \<and> (\<forall>a\<in>set al. aEval a (L @ xs)) \<and> (\<forall>f\<in>set fl. eval f (L @ xs)))" for al fl n
    have "f al fl (n+1) = (case (case (al, fl, n) of (A, A', d) \<Rightarrow> (A, A',d+1)) of
             (al, fl, n) \<Rightarrow> f al fl n)"
      by simp
    then have "(\<exists>L. length L = (n+1) \<and> (\<forall>a\<in>set al. aEval a (L @ xs)) \<and> (\<forall>f\<in>set fl. eval f (L @ xs)))
              = (
             case (case (al, fl, n) of (A, A', d) \<Rightarrow> (A, A',d+1)) of
             (al, fl, n) \<Rightarrow>
               \<exists>L. length L = n \<and> (\<forall>a\<in>set al. aEval a (L @ xs)) \<and> (\<forall>f\<in>set fl. eval f (L @ xs)))"
      unfolding f_def by simp
  }
  then have h3 : "
              (\<exists>(al, fl, n)\<in>set (dnf_modified \<phi>).
               \<exists>L. length L = (n+1) \<and> (\<forall>a\<in>set al. aEval a (L @ xs)) \<and> (\<forall>f\<in>set fl. eval f (L @ xs)))
              = (\<exists>a\<in>set (dnf_modified \<phi>).
             case (case a of (A, A', d) \<Rightarrow> (A, A',d+1)) of
             (al, fl, n) \<Rightarrow>
               \<exists>L. length L = n \<and> (\<forall>a\<in>set al. aEval a (L @ xs)) \<and> (\<forall>f\<in>set fl. eval f (L @ xs)))"
    by (smt case_prodE case_prodI2) (* takes a second *)
  show ?case using ExQ h1 h2 h3 by simp
next
  case (ExN x1 \<phi>)

  show ?case
    apply simp proof safe
    fix a aa b L
    have takedrop: "(take b L @ drop b L @ xs) = (L @ xs)" by auto
    assume h: "(a, aa, b) \<in> set (dnf_modified \<phi>)" "length L = b + x1" "\<forall>a\<in>set a. aEval a (L @ xs)" "\<forall>f\<in>set aa. eval f (L @ xs)"
    show "\<exists>l. length l = x1 \<and> eval \<phi> (l @ xs)"
      apply(rule exI[where x="drop b L"])
      apply auto
      using h(2) apply simp
      unfolding ExN[symmetric]
      apply(rule bexI[where x="(a,aa,b)"])
      apply simp
      apply(rule exI[where x="take b L"])
      apply auto
      using h apply simp
      unfolding takedrop
      using h by auto
  next
    fix l
    assume h: "eval \<phi> (l @ xs)" "x1 = length l" 
    obtain al fl n where h1 : "(al, fl, n)\<in>set (dnf_modified \<phi>)" "\<exists>L. length L = n \<and> (\<forall>a\<in>set al. aEval a (L @ l @ xs)) \<and> (\<forall>f\<in>set fl. eval f (L @ l @ xs))"
      using h(1) unfolding ExN[symmetric]
      by blast 
    obtain L where h2 : "length L = n" "(\<forall>a\<in>set al. aEval a (L @ l @ xs))" "(\<forall>f\<in>set fl. eval f (L @ l @ xs))" using h1(2) by metis 
    show "\<exists>x\<in>set (dnf_modified \<phi>).
            case case x of (A, A', d) \<Rightarrow> (A, A', d + length l) of
            (al, fl, n) \<Rightarrow> \<exists>L. length L = n \<and> (\<forall>a\<in>set al. aEval a (L @ xs)) \<and> (\<forall>f\<in>set fl. eval f (L @ xs))"
      apply(rule bexI[where x="(al,fl,n)"])
      apply simp
      apply(rule exI[where x="L@l"])
      apply auto
      using h2 h1 by auto
  qed
qed auto
end