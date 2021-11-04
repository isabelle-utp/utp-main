theory GeneralVSProofs
  imports  DNFUni EqualityVS VSAlgos
begin


fun separateAtoms :: "atomUni list \<Rightarrow> (real * real * real) list * (real * real * real) list * (real * real * real) list * (real * real * real) list" where
  "separateAtoms [] = ([],[],[],[])"|
  "separateAtoms (EqUni p # L) = (let (a,b,c,d) = separateAtoms(L) in (p#a,b,c,d))"|
  "separateAtoms (LessUni p # L) = (let (a,b,c,d) = separateAtoms(L) in (a,p#b,c,d))"|
  "separateAtoms (LeqUni p # L) = (let (a,b,c,d) = separateAtoms(L) in (a,b,p#c,d))"|
  "separateAtoms (NeqUni p # L) = (let (a,b,c,d) = separateAtoms(L) in (a,b,c,p#d))"


lemma separate_aEval :
  assumes "separateAtoms L = (a,b,c,d)"
  shows "(\<forall>l\<in>set L. aEvalUni l x) = 
      ((\<forall>(a,b,c)\<in>set a. a*x^2+b*x+c=0) \<and> (\<forall>(a,b,c)\<in>set b. a*x^2+b*x+c<0) \<and>
      (\<forall>(a,b,c)\<in>set c. a*x^2+b*x+c\<le>0) \<and> (\<forall>(a,b,c)\<in>set d. a*x^2+b*x+c\<noteq>0))"
  using assms proof(induction L arbitrary :a b c d)
  case Nil
  then show ?case by auto
next
  case (Cons At L)
  then have Cons1 : "\<And>a b c d. separateAtoms L = (a, b, c, d) \<Longrightarrow>
    (\<forall>l\<in>set L. aEvalUni l x) =
    ((\<forall>a\<in>set a. case a of (a, ba, c) \<Rightarrow> a * x\<^sup>2 + ba * x + c = 0) \<and>
     (\<forall>a\<in>set b. case a of (a, ba, c) \<Rightarrow> a * x\<^sup>2 + ba * x + c < 0)\<and>
     (\<forall>a\<in>set c. case a of (a, ba, c) \<Rightarrow> a * x\<^sup>2 + ba * x + c \<le> 0) \<and>
     (\<forall>a\<in>set d. case a of (a, ba, c) \<Rightarrow> a * x\<^sup>2 + ba * x + c \<noteq> 0))" "
    separateAtoms (At # L) = (a, b,c,d)" by auto
  then show ?case proof(cases At)
    case (LessUni p)
    show ?thesis proof(cases b)
      case Nil
      show ?thesis using Cons(2) unfolding LessUni separateAtoms.simps Nil
        apply(cases "separateAtoms L") by simp
    next
      case (Cons p' b')
      then have p_def : "p' = p" using Cons1(2) unfolding LessUni separateAtoms.simps
        apply(cases "separateAtoms L") by simp
      have h1 :  "separateAtoms L = (a,b',c,d)" using Cons Cons1(2) unfolding LessUni separateAtoms.simps
        apply(cases "separateAtoms L") by simp
      have h2 : "(\<forall>a\<in>set (p # b'). case a of (a, ba, c) \<Rightarrow> a * x\<^sup>2 + ba * x + c < 0) = (
          (\<forall>a\<in>set (b'). case a of (a, ba, c) \<Rightarrow> a * x\<^sup>2 + ba * x + c < 0)\<and> (case p of (a, ba, c) \<Rightarrow> a * x\<^sup>2 + ba * x + c < 0))"
        by auto
      have h3 : "(\<forall>l\<in>set (LessUni p # L). aEvalUni l x) = ((\<forall>l\<in>set (L). aEvalUni l x)\<and>(case p of (a, ba, c) \<Rightarrow> a * x\<^sup>2 + ba * x + c < 0))"
        by auto
      show ?thesis unfolding Cons LessUni p_def h2 h3 using Cons1(1)[OF h1]
        by auto
    qed
  next
    case (EqUni p)
    show ?thesis proof(cases a)
      case Nil
      show ?thesis using Cons(2) unfolding EqUni separateAtoms.simps Nil
        apply(cases "separateAtoms L") by simp
    next
      case (Cons p' a')
      then have p_def : "p' = p" using Cons1(2) unfolding EqUni separateAtoms.simps
        apply(cases "separateAtoms L") by simp
      have h1 :  "separateAtoms L = (a',b,c,d)" using Cons Cons1(2) unfolding EqUni separateAtoms.simps
        apply(cases "separateAtoms L") by simp
      have h2 : "(\<forall>a\<in>set (p # a'). case a of (a, ba, c) \<Rightarrow> a * x\<^sup>2 + ba * x + c = 0) = (
          (\<forall>a\<in>set (a'). case a of (a, ba, c) \<Rightarrow> a * x\<^sup>2 + ba * x + c = 0)\<and> (case p of (a, ba, c) \<Rightarrow> a * x\<^sup>2 + ba * x + c = 0))"
        by auto
      have h3 : "(\<forall>l\<in>set (EqUni p # L). aEvalUni l x) = ((\<forall>l\<in>set (L). aEvalUni l x)\<and>(case p of (a, ba, c) \<Rightarrow> a * x\<^sup>2 + ba * x + c = 0))"
        by auto
      show ?thesis unfolding Cons EqUni p_def h2 h3 using Cons1(1)[OF h1]
        by auto
    qed
  next
    case (LeqUni p)
    then show ?thesis proof(cases c)
      case Nil
      show ?thesis using Cons(2) unfolding LeqUni separateAtoms.simps Nil
        apply(cases "separateAtoms L") by simp
    next
      case (Cons p' a')
      then have p_def : "p' = p" using Cons1(2) unfolding LeqUni separateAtoms.simps
        apply(cases "separateAtoms L") by simp
      have h1 :  "separateAtoms L = (a,b,a',d)" using Cons Cons1(2) unfolding LeqUni separateAtoms.simps
        apply(cases "separateAtoms L") by simp
      have h2 : "(\<forall>a\<in>set (p # a'). case a of (a, ba, c) \<Rightarrow> a * x\<^sup>2 + ba * x + c \<le> 0) = (
          (\<forall>a\<in>set (a'). case a of (a, ba, c) \<Rightarrow> a * x\<^sup>2 + ba * x + c \<le> 0)\<and> (case p of (a, ba, c) \<Rightarrow> a * x\<^sup>2 + ba * x + c \<le> 0))"
        by auto
      have h3 : "(\<forall>l\<in>set (LeqUni p # L). aEvalUni l x) = ((\<forall>l\<in>set (L). aEvalUni l x)\<and>(case p of (a, ba, c) \<Rightarrow> a * x\<^sup>2 + ba * x + c \<le> 0))"
        by auto
      show ?thesis unfolding Cons LeqUni p_def h2 h3 using Cons1(1)[OF h1]
        by auto
    qed
  next
    case (NeqUni p)
    then show ?thesis proof(cases d)
      case Nil
      show ?thesis using Cons(2) unfolding NeqUni separateAtoms.simps Nil
        apply(cases "separateAtoms L") by simp
    next
      case (Cons p' a')
      then have p_def : "p' = p" using Cons1(2) unfolding NeqUni separateAtoms.simps
        apply(cases "separateAtoms L") by simp
      have h1 :  "separateAtoms L = (a,b,c,a')" using Cons Cons1(2) unfolding NeqUni separateAtoms.simps
        apply(cases "separateAtoms L") by simp
      have h2 : "(\<forall>a\<in>set (p # a'). case a of (a, ba, c) \<Rightarrow> a * x\<^sup>2 + ba * x + c \<noteq> 0) = (
          (\<forall>a\<in>set (a'). case a of (a, ba, c) \<Rightarrow> a * x\<^sup>2 + ba * x + c \<noteq> 0)\<and> (case p of (a, ba, c) \<Rightarrow> a * x\<^sup>2 + ba * x + c \<noteq> 0))"
        by auto
      have h3 : "(\<forall>l\<in>set (NeqUni p # L). aEvalUni l x) = ((\<forall>l\<in>set (L). aEvalUni l x)\<and>(case p of (a, ba, c) \<Rightarrow> a * x\<^sup>2 + ba * x + c \<noteq> 0))"
        by auto
      show ?thesis unfolding Cons NeqUni p_def h2 h3 using Cons1(1)[OF h1]
        by auto
    qed
  qed
qed

lemma splitAtoms_negInfinity :
  assumes "separateAtoms L = (a,b,c,d)"
  shows "(\<forall>l\<in>set L. evalUni (substNegInfinityUni l) x) = (
  (\<forall>(a,b,c)\<in>set a.(\<exists>x. \<forall>y<x. a*y^2+b*y+c=0))\<and>
  (\<forall>(a,b,c)\<in>set b.(\<exists>x. \<forall>y<x. a*y^2+b*y+c<0))\<and>
  (\<forall>(a,b,c)\<in>set c.(\<exists>x. \<forall>y<x. a*y^2+b*y+c\<le>0))\<and>
  (\<forall>(a,b,c)\<in>set d.(\<exists>x. \<forall>y<x. a*y^2+b*y+c\<noteq>0)))"
  using assms proof(induction L arbitrary :a b c d)
  case Nil
  then show ?case by auto
next
  case (Cons At L)
  then have Cons1 : "\<And>a b c d. separateAtoms L = (a, b, c, d) \<Longrightarrow>
    (\<forall>l\<in>set L. evalUni (substNegInfinityUni l) x) =
    ((\<forall>a\<in>set a. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c = 0) \<and>
     (\<forall>a\<in>set b. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c < 0)\<and>
     (\<forall>a\<in>set c. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<le> 0)\<and>
     (\<forall>a\<in>set d. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<noteq> 0))" "separateAtoms (At # L) = (a, b, c, d)" by auto
  then show ?case proof(cases At)
    case (LessUni p)
    show ?thesis using LessUni Cons proof(induction b rule : list.induct)
      case Nil
      then have Nil : "b = []"
        using Cons.prems by auto
      show ?case using Cons(2) unfolding LessUni separateAtoms.simps Nil
        apply(cases "separateAtoms L") by simp
    next
      case (Cons p' b')
      then have p_def : "p' = p" using Cons1(2) unfolding LessUni separateAtoms.simps
        apply(cases "separateAtoms L") by simp
      have h1 :  "separateAtoms L = (a,b',c,d)" using Cons Cons1(2) unfolding LessUni separateAtoms.simps
        apply(cases "separateAtoms L") by simp
      have h2 : "(\<forall>a\<in>set (p # b'). case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c < 0) = (
          (\<forall>a\<in>set ( b'). case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c < 0)\<and> (case p of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c < 0))"
        by auto
      have one: "(\<exists>x. \<forall>y<x. aEvalUni (LessUni p) y) = (case p of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c < 0)"
        apply(cases p) by simp
      have "(\<forall>l\<in>set (LessUni p # L). evalUni (substNegInfinityUni l) x) = ((evalUni (substNegInfinityUni (LessUni p)) x)\<and>(\<forall>l\<in>set ( L). evalUni (substNegInfinityUni l) x))"
        by auto
      also have "... = (
      (case p of (a,ba,c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c < 0)\<and>
      (\<forall>a\<in>set a. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c = 0) \<and>
     (\<forall>a\<in>set b'. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c < 0)\<and>
     (\<forall>a\<in>set c. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<le> 0)\<and>
     (\<forall>a\<in>set d. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<noteq> 0))"
        unfolding infinity_evalUni[of "LessUni p" x, symmetric] Cons(3)[OF h1]  LessUni one by simp
      finally have h3 : "(\<forall>l\<in>set (LessUni p # L). evalUni (substNegInfinityUni l) x) = (
      (case p of (a,ba,c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c < 0)\<and>
      (\<forall>a\<in>set a. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c = 0) \<and>
     (\<forall>a\<in>set b'. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c < 0)\<and>
     (\<forall>a\<in>set c. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<le> 0)\<and>
     (\<forall>a\<in>set d. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<noteq> 0) )"
        by auto
      show ?case unfolding Cons LessUni p_def h2 h3 using Cons1(1)[OF h1]
        by auto
    qed
  next
    case (EqUni p)
    show ?thesis using EqUni Cons proof(induction a rule : list.induct)
      case Nil
      then have Nil : "a = []"
        using Cons.prems by auto
      show ?case using Cons(2) unfolding EqUni separateAtoms.simps Nil
        apply(cases "separateAtoms L") by simp
    next
      case (Cons p' a')
      then have p_def : "p' = p" using Cons1(2) unfolding EqUni separateAtoms.simps
        apply(cases "separateAtoms L") by simp
      have h1 :  "separateAtoms L = (a',b,c,d)" using Cons Cons1(2) unfolding EqUni separateAtoms.simps
        apply(cases "separateAtoms L") by simp
      have h2 : "(\<forall>a\<in>set (p # a'). case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c = 0) = (
          (\<forall>a\<in>set ( a'). case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c = 0)\<and> (case p of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c = 0))"
        by auto
      have one: "(\<exists>x. \<forall>y<x. aEvalUni (EqUni p) y) = (case p of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c = 0)"
        apply(cases p) by simp
      have "(\<forall>l\<in>set (EqUni p # L). evalUni (substNegInfinityUni l) x) = ((evalUni (substNegInfinityUni (EqUni p)) x)\<and>(\<forall>l\<in>set ( L). evalUni (substNegInfinityUni l) x))"
        by auto
      also have "... = (
      (case p of (a,ba,c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c = 0)\<and>
      (\<forall>a\<in>set a'. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c = 0) \<and>
     (\<forall>a\<in>set b. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c < 0)\<and>
     (\<forall>a\<in>set c. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<le> 0)\<and>
     (\<forall>a\<in>set d. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<noteq> 0))"
        unfolding infinity_evalUni[of "EqUni p" x, symmetric] Cons(3)[OF h1] EqUni one by simp
      finally have h3 : "(\<forall>l\<in>set (EqUni p # L). evalUni (substNegInfinityUni l) x) = (
      (case p of (a,ba,c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c = 0)\<and>
      (\<forall>a\<in>set a'. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c = 0) \<and>
     (\<forall>a\<in>set b. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c < 0)\<and>
     (\<forall>a\<in>set c. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<le> 0)\<and>
     (\<forall>a\<in>set d. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<noteq> 0))"
        by auto
      show ?case unfolding Cons EqUni p_def h2 h3 using Cons1(1)[OF h1]
        by auto
    qed
  next
    case (LeqUni p)
    show ?thesis using LeqUni Cons proof(induction c rule : list.induct)
      case Nil
      then have Nil : "c = []"
        using Cons.prems by auto
      show ?case using Cons(2) unfolding LeqUni separateAtoms.simps Nil
        apply(cases "separateAtoms L") by simp
    next
      case (Cons p' c')
      then have p_def : "p' = p" using Cons1(2) unfolding LeqUni separateAtoms.simps
        apply(cases "separateAtoms L") by simp
      have h1 :  "separateAtoms L = (a,b,c',d)" using Cons Cons1(2) unfolding LeqUni separateAtoms.simps
        apply(cases "separateAtoms L") by simp
      have h2 : "(\<forall>a\<in>set (p # c'). case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<le> 0) = (
          (\<forall>a\<in>set ( c'). case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<le> 0)\<and> (case p of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<le> 0))"
        by auto
      have one: "(\<exists>x. \<forall>y<x. aEvalUni (LeqUni p) y) = (case p of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<le> 0)"
        apply(cases p) by simp
      have "(\<forall>l\<in>set (LeqUni p # L). evalUni (substNegInfinityUni l) x) = ((evalUni (substNegInfinityUni (LeqUni p)) x)\<and>(\<forall>l\<in>set ( L). evalUni (substNegInfinityUni l) x))"
        by auto
      also have "... = (
      (case p of (a,ba,c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<le> 0)\<and>
      (\<forall>a\<in>set a. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c = 0) \<and>
     (\<forall>a\<in>set b. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c < 0)\<and>
     (\<forall>a\<in>set c'. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<le> 0)\<and>
     (\<forall>a\<in>set d. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<noteq> 0))"
        unfolding infinity_evalUni[of "LeqUni p" x, symmetric] Cons(3)[OF h1]  LeqUni one 
        by simp
      finally have h3 : "(\<forall>l\<in>set (LeqUni p # L). evalUni (substNegInfinityUni l) x) = (
      (case p of (a,ba,c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<le> 0)\<and>
      (\<forall>a\<in>set a. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c = 0) \<and>
     (\<forall>a\<in>set b. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c < 0)\<and>
     (\<forall>a\<in>set c'. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<le> 0)\<and>
     (\<forall>a\<in>set d. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<noteq> 0) )"
        by auto
      show ?case unfolding Cons LeqUni p_def h2 h3 using Cons1(1)[OF h1]
        by auto
    qed
  next
    case (NeqUni p)
    show ?thesis using NeqUni Cons proof(induction d rule : list.induct)
      case Nil
      then have Nil : "d = []"
        using Cons.prems by auto
      show ?case using Cons(2) unfolding NeqUni separateAtoms.simps Nil
        apply(cases "separateAtoms L") by simp
    next
      case (Cons p' d')
      then have p_def : "p' = p" using Cons1(2) unfolding NeqUni separateAtoms.simps
        apply(cases "separateAtoms L") by simp
      have h1 :  "separateAtoms L = (a,b,c,d')" using Cons Cons1(2) unfolding NeqUni separateAtoms.simps
        apply(cases "separateAtoms L") by simp
      have h2 : "(\<forall>a\<in>set (p # d'). case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<noteq> 0) = (
          (\<forall>a\<in>set ( d'). case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<noteq> 0)\<and> (case p of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<noteq> 0))"
        by auto
      have one: "(\<exists>x. \<forall>y<x. aEvalUni (NeqUni p) y) = (case p of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<noteq> 0)"
        apply(cases p) by simp
      have "(\<forall>l\<in>set (NeqUni p # L). evalUni (substNegInfinityUni l) x) = ((evalUni (substNegInfinityUni (NeqUni p)) x)\<and>(\<forall>l\<in>set ( L). evalUni (substNegInfinityUni l) x))"
        by auto
      also have "... = (
      (case p of (a,ba,c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<noteq> 0)\<and>
      (\<forall>a\<in>set a. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c = 0) \<and>
     (\<forall>a\<in>set b. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c < 0)\<and>
     (\<forall>a\<in>set c. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<le> 0)\<and>
     (\<forall>a\<in>set d'. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<noteq> 0))"
        unfolding infinity_evalUni[of "NeqUni p" x, symmetric] Cons(3)[OF h1]  NeqUni one 
        by simp
      finally have h3 : "(\<forall>l\<in>set (NeqUni p # L). evalUni (substNegInfinityUni l) x) = (
      (case p of (a,ba,c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<noteq> 0)\<and>
      (\<forall>a\<in>set a. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c = 0) \<and>
     (\<forall>a\<in>set b. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c < 0)\<and>
     (\<forall>a\<in>set c. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<le> 0)\<and>
     (\<forall>a\<in>set d'. case a of (a, ba, c) \<Rightarrow> \<exists>x. \<forall>y<x. a * y\<^sup>2 + ba * y + c \<noteq> 0) )"
        by auto
      show ?case unfolding Cons NeqUni p_def h2 h3 using Cons1(1)[OF h1]
        by auto
    qed
  qed
qed

lemma set_split : 
  assumes "separateAtoms L = (eq,les,leq,neq)"
  shows "set L = set (map EqUni eq @ map LessUni les @ map LeqUni leq @ map NeqUni neq)"
  using assms proof(induction L arbitrary :eq les leq neq)
  case Nil
  then show ?case by auto
next
  case (Cons At L)
  then show ?case proof(cases At)
    case (LessUni p)
    have "\<exists>les'. p#les' = les \<and> separateAtoms L = (eq, les', leq, neq)" using Cons(2) unfolding LessUni apply (cases "separateAtoms L") by auto
    then obtain les' where les' : "p#les' = les" "separateAtoms L = (eq, les', leq, neq)" by auto
    show ?thesis unfolding LessUni les'(1)[symmetric] using Cons(1)[OF les'(2)] by auto
  next
    case (EqUni p)
    have "\<exists>eq'. p#eq' = eq \<and> separateAtoms L = (eq', les, leq, neq)" using Cons(2) unfolding EqUni apply (cases "separateAtoms L") by auto
    then obtain eq' where eq' : "p#eq' = eq" "separateAtoms L = (eq', les, leq, neq)" by auto
    show ?thesis unfolding EqUni eq'(1)[symmetric] using Cons(1)[OF eq'(2)] by auto
  next
    case (LeqUni p)
    have "\<exists>leq'. p#leq' = leq \<and> separateAtoms L = (eq, les, leq', neq)" using Cons(2) unfolding LeqUni apply (cases "separateAtoms L")
      by auto
    then obtain leq' where leq' : "p#leq' = leq" "separateAtoms L = (eq, les, leq', neq)" by auto
    show ?thesis unfolding LeqUni leq'(1)[symmetric] using Cons(1)[OF leq'(2)] by auto
  next
    case (NeqUni p)
    have "\<exists>neq'. p#neq' = neq \<and> separateAtoms L = (eq, les, leq, neq')" using Cons(2) unfolding NeqUni apply (cases "separateAtoms L")
      by auto
    then obtain neq' where neq' : "p#neq' = neq" "separateAtoms L = (eq, les, leq, neq')" by auto
    show ?thesis unfolding NeqUni neq'(1)[symmetric] using Cons(1)[OF neq'(2)] by auto
  qed
qed

lemma set_split' : assumes "separateAtoms L = (eq,les,leq,neq)"
  shows "set (map P L) = set (map (P o EqUni) eq @ map (P o LessUni) les @ map (P o LeqUni) leq @ map (P o NeqUni) neq)"
  unfolding image_set[symmetric] set_split[OF assms]
  unfolding image_set map_append map_map by auto

lemma split_elimVar :
  assumes "separateAtoms L = (eq,les,leq,neq)"
  shows "(\<exists>l\<in>set L. evalUni (elimVarUni_atom L' l) x) = 
  ((\<exists>(a',b',c')\<in>set eq. (evalUni (elimVarUni_atom L' (EqUni(a',b',c'))) x))
  \<or> (\<exists>(a',b',c')\<in>set les. 
    (evalUni (elimVarUni_atom L' (LessUni(a',b',c'))) x))
\<or> (\<exists>(a',b',c')\<in>set leq. 
    (evalUni (elimVarUni_atom L' (LeqUni(a',b',c'))) x))
\<or> (\<exists>(a',b',c')\<in>set neq. 
    (evalUni (elimVarUni_atom L' (NeqUni(a',b',c'))) x)))"
proof-
  have c1: "(\<exists>l\<in>set eq. evalUni (elimVarUni_atom L' (EqUni l)) x) = (\<exists>(a', b', c')\<in>set eq. evalUni (elimVarUni_atom L' (EqUni (a', b', c'))) x)"
    by (metis (no_types, lifting) case_prodE case_prodI2)
  have c2: "(\<exists>l\<in>set les. evalUni (elimVarUni_atom L' (LessUni l)) x) = (\<exists>(a', b', c')\<in>set les. evalUni (elimVarUni_atom L' (LessUni (a', b', c'))) x)"
    by (metis (no_types, lifting) case_prodE case_prodI2)
  have c3: "(\<exists>l\<in>set leq. evalUni (elimVarUni_atom L' (LeqUni l)) x) = (\<exists>(a', b', c')\<in>set leq. evalUni (elimVarUni_atom L' (LeqUni (a', b', c'))) x)"
    by (metis (no_types, lifting) case_prodE case_prodI2)
  have c4: "(\<exists>l\<in>set neq. evalUni (elimVarUni_atom L' (NeqUni l)) x) = (\<exists>(a', b', c')\<in>set neq. evalUni (elimVarUni_atom L' (NeqUni (a', b', c'))) x)"
    by (metis (no_types, lifting) case_prodE case_prodI2)
  have h :  "((\<exists>l\<in>EqUni ` set eq. evalUni (elimVarUni_atom L' l) x) \<or>
         (\<exists>l\<in>LessUni ` set les. evalUni (elimVarUni_atom L' l) x) \<or>
    (\<exists>l\<in>LeqUni ` set leq. evalUni (elimVarUni_atom L' l) x) \<or>
    (\<exists>l\<in>NeqUni ` set neq. evalUni (elimVarUni_atom L' l) x)
    ) = 
        ((\<exists>l\<in>set eq. evalUni (elimVarUni_atom L' (EqUni l)) x) \<or>
         (\<exists>l\<in>set les. evalUni (elimVarUni_atom L' (LessUni l)) x) \<or>
    (\<exists>l\<in>set leq. evalUni (elimVarUni_atom L' (LeqUni l)) x) \<or>
    (\<exists>l\<in>set neq. evalUni (elimVarUni_atom L' (NeqUni l)) x)
    )"
    by auto
  then have "... = ((\<exists>(a', b', c')\<in>set eq. evalUni (elimVarUni_atom L' (EqUni (a', b', c'))) x) \<or>
     (\<exists>(a', b', c')\<in>set les. evalUni (elimVarUni_atom L' (LessUni (a', b', c'))) x) \<or>
     (\<exists>(a', b', c')\<in>set leq. evalUni (elimVarUni_atom L' (LeqUni (a', b', c'))) x) \<or>
     (\<exists>(a', b', c')\<in>set neq. evalUni (elimVarUni_atom L' (NeqUni (a', b', c'))) x))"
    using c1 c2 c3 c4 by auto
  then show ?thesis 
    unfolding set_split[OF assms] set_append bex_Un image_set[symmetric]
    using case_prodE case_prodI2  by auto
qed

lemma split_elimvar : 
  assumes "separateAtoms L = (eq,les,leq,neq)"
  shows "evalUni (elimVarUni_atom L At) x = evalUni (elimVarUni_atom ((map EqUni eq)@(map LessUni les) @ map LeqUni leq @ map NeqUni neq) At) x"
proof(cases At)
  case (LessUni p)
  then show ?thesis apply(cases p) apply simp unfolding eval_list_conj_Uni set_split'[OF assms] by simp
next
  case (EqUni p)
  then show ?thesis apply(cases p) apply simp unfolding eval_list_conj_Uni set_split'[OF assms] by simp
next
  case (LeqUni p)
  then show ?thesis apply(cases p) apply simp unfolding eval_list_conj_Uni set_split'[OF assms] by simp
next
  case (NeqUni p)
  then show ?thesis apply(cases p) apply simp unfolding eval_list_conj_Uni set_split'[OF assms] by simp
qed




lemma less : "
         ((a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a. evalUni (substInfinitesimalLinearUni b' c' (EqUni (d, e, f))) x) \<and>
         (\<forall>(d, e, f)\<in>set b. evalUni (substInfinitesimalLinearUni b' c' (LessUni (d, e, f))) x) \<and>
         (\<forall>(d, e, f)\<in>set c. evalUni (substInfinitesimalLinearUni b' c' (LeqUni (d, e, f))) x) \<and>
         (\<forall>(d, e, f)\<in>set d. evalUni (substInfinitesimalLinearUni b' c' (NeqUni (d, e, f))) x) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              evalUni
               (substInfinitesimalQuadraticUni (- b') 1 (b'\<^sup>2 - 4 * a' * c') (2 * a')
                 (EqUni (d, e, f)))
               x) \<and>
          (\<forall>(d, e, f)\<in>set b.
              evalUni
               (substInfinitesimalQuadraticUni (- b') 1 (b'\<^sup>2 - 4 * a' * c') (2 * a')
                 (LessUni (d, e, f)))
               x) \<and>
          (\<forall>(d, e, f)\<in>set c.
              evalUni
               (substInfinitesimalQuadraticUni (- b') 1 (b'\<^sup>2 - 4 * a' * c') (2 * a')
                 (LeqUni (d, e, f)))
               x) \<and>
          (\<forall>(d, e, f)\<in>set d.
              evalUni
               (substInfinitesimalQuadraticUni (- b') 1 (b'\<^sup>2 - 4 * a' * c') (2 * a')
                 (NeqUni (d, e, f)))
               x) \<or>
          (\<forall>(d, e, f)\<in>set a.
              evalUni
               (substInfinitesimalQuadraticUni (- b') (- 1) (b'\<^sup>2 - 4 * a' * c') (2 * a')
                 (EqUni (d, e, f)))
               x) \<and>
          (\<forall>(d, e, f)\<in>set b.
              evalUni
               (substInfinitesimalQuadraticUni (- b') (- 1) (b'\<^sup>2 - 4 * a' * c') (2 * a')
                 (LessUni (d, e, f)))
               x) \<and>
          (\<forall>(d, e, f)\<in>set c.
              evalUni
               (substInfinitesimalQuadraticUni (- b') (- 1) (b'\<^sup>2 - 4 * a' * c') (2 * a')
                 (LeqUni (d, e, f)))
               x) \<and>
          (\<forall>(d, e, f)\<in>set d.
              evalUni
               (substInfinitesimalQuadraticUni (- b') (- 1) (b'\<^sup>2 - 4 * a' * c') (2 * a')
                 (NeqUni (d, e, f)))
               x))) = 

          ((a' = 0 \<and> b' \<noteq> 0) \<and>
         (\<forall>(d, e, f)\<in>set a.
             (\<exists>y'::real>-c'/b'. \<forall>x::real \<in>{-c'/b'<..y'}. aEvalUni (EqUni (d, e, f)) x)) \<and>
         (\<forall>(d, e, f)\<in>set b.
            (\<exists>y'::real>-c'/b'. \<forall>x::real \<in>{-c'/b'<..y'}. aEvalUni (LessUni (d, e, f)) x))\<and>
         (\<forall>(d, e, f)\<in>set c.
             (\<exists>y'::real>-c'/b'. \<forall>x::real \<in>{-c'/b'<..y'}. aEvalUni (LeqUni (d, e, f)) x)) \<and>
         (\<forall>(d, e, f)\<in>set d.
            (\<exists>y'::real>-c'/b'. \<forall>x::real \<in>{-c'/b'<..y'}. aEvalUni (NeqUni (d, e, f)) x)) \<or>
         a' \<noteq> 0 \<and>
         - b'\<^sup>2 + 4 * a' * c' \<le> 0 \<and>
         ((\<forall>(d, e, f)\<in>set a.
              (\<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
        \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
           aEvalUni (EqUni (d,e,f)) x)) \<and>
          (\<forall>(d, e, f)\<in>set b.
              (\<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
        \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
           aEvalUni (LessUni (d,e,f)) x)) \<and>
          (\<forall>(d, e, f)\<in>set c.
              (\<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
        \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
           aEvalUni (LeqUni (d,e,f)) x)) \<and>
          (\<forall>(d, e, f)\<in>set d.
              (\<exists>y'>(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
        \<forall>x\<in>{(- b' + 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
           aEvalUni (NeqUni (d,e,f)) x)) \<or>
          (\<forall>(d, e, f)\<in>set a.
              (\<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
        \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
           aEvalUni (EqUni (d,e,f)) x)) \<and>
          (\<forall>(d, e, f)\<in>set b.
              (\<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
        \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
           aEvalUni (LessUni (d,e,f)) x)) \<and> 
          (\<forall>(d, e, f)\<in>set c.
              (\<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
        \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
           aEvalUni (LeqUni (d,e,f)) x)) \<and>
          (\<forall>(d, e, f)\<in>set d.
              (\<exists>y'>(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a').
        \<forall>x\<in>{(- b' + - 1 * sqrt (b'\<^sup>2 - 4 * a' * c')) / (2 * a')<..y'}.
           aEvalUni (NeqUni (d,e,f)) x))))"
proof(cases "a'=0")
  case True
  then have a' :  "a'=0" by auto
  then show ?thesis proof(cases "b'=0")
    case True
    then show ?thesis using a' by auto
  next
    case False
    then show ?thesis using True unfolding infinitesimal_linear'[of b' c' _ x, symmetric, OF False] by auto
  qed 
next
  case False
  then have a' : "a' \<noteq> 0" by auto
  then have d : "2 * a' \<noteq> 0" by auto
  show ?thesis proof(cases "0 \<le> b'\<^sup>2 - 4 * a' * c'")
    case True
    then show ?thesis using False
      unfolding infinitesimal_quad[OF d True, of "-b'", symmetric] by auto
  next
    case False
    then show ?thesis using a' by auto
  qed 
qed

lemma eq_inf : "(\<forall>(a, b, c)\<in>set (a::(real*real*real) list). \<exists>x. \<forall>y<x. a * y\<^sup>2 + b * y + c = 0) = (\<forall>(a, b, c)\<in>set a. a=0\<and>b=0\<and>c=0)"
  using infinity_evalUni_EqUni[of _ x] by auto



text "This is the main quantifier elimination lemma, in the simplified framework. We are located directly underneath 
the most internal existential quantifier so F is completely free in quantifier and consists only of conjunction and disjunction.
The variable we are evaluating on, x, is removed in the generalVS\\_DNF converted formula as expanding out the evalUni function
determines that x doesn't play a role in the computation of it. It would be okay to replace the x in the second half with any variable,
but it is simplier this way

This conversion is defined as a \"veritcal\" translation as we remain within the univariate framework in both sides of the expression"

lemma eval_generalVS'' : "(\<exists>x. evalUni (list_conj_Uni (map AtomUni L)) x) =
                               evalUni (generalVS_DNF L) x"
proof(cases "separateAtoms L")
  case (fields a b c d)
  have a : "\<And> P. (\<forall>l\<in>set (map EqUni a) \<union> (set (map LessUni b) \<union> (set (map LeqUni c) \<union> set (map NeqUni d))).P l) = 
            ((\<forall>(d,e,f)\<in>set a. P (EqUni (d,e,f))) \<and> (\<forall>(d,e,f)\<in>set b. P (LessUni (d,e,f))) \<and> (\<forall>(d,e,f)\<in>set c. P (LeqUni (d,e,f))) \<and> (\<forall>(d,e,f)\<in>set d. P (NeqUni (d,e,f))))"
    by auto
  show ?thesis apply(simp add: eval_list_conj_Uni separate_aEval[OF fields]
        splitAtoms_negInfinity[OF fields] eval_list_disj_Uni 
        del:elimVar.simps)

    unfolding eval_conj_atom generalVS_DNF.simps 
      split_elimVar[OF fields ] 

split_elimvar[OF fields]

    unfolding elimVarUni_atom.simps evalUni.simps aEvalUni.simps
      Rings.mult_zero_class.mult_zero_left Groups.add_0 eval_list_conj_Uni Groups.group_add_class.minus_zero 
      eval_map_all linearSubstitutionUni.simps quadraticSubUni.simps evalUni_if aEvalUni.simps
      set_append a less eq_inf
    using qe  by auto
qed


lemma forallx_substNegInf : "(\<not>evalUni (map_atomUni substNegInfinityUni F) x) = (\<forall>x. \<not> evalUni (map_atomUni substNegInfinityUni F) x)"
proof(induction F)
  case TrueFUni
  then show ?case by simp
next
  case FalseFUni
  then show ?case  by simp
next
  case (AtomUni At)
  then show ?case apply(cases At) by auto  
next
  case (AndUni F1 F2)
  then show ?case  by auto
next
  case (OrUni F1 F2)
  then show ?case  by auto
qed

lemma linear_subst_map: "evalUni (map_atomUni (linearSubstitutionUni b c) F) x = evalUni F (-c/b)"
  apply(induction F)by auto

lemma quadratic_subst_map : "evalUni (map_atomUni (quadraticSubUni a b c d) F) x = evalUni F ((a+b*sqrt(c))/d)"
  apply(induction F)by auto




fun convert_atom_list :: "nat \<Rightarrow> atom list \<Rightarrow> real list \<Rightarrow> (atomUni list) option" where
  "convert_atom_list var [] xs = Some []"|
  "convert_atom_list var (a#as) xs = (
  case convert_atom var a xs of Some(a) \<Rightarrow> 
  (case convert_atom_list var as xs of Some(as) \<Rightarrow> Some(a#as) | None \<Rightarrow> None)
   | None \<Rightarrow> None
)"





lemma convert_atom_list_change :
  assumes "length xs' = var"
  shows "convert_atom_list var L (xs' @ x # \<Gamma>) = convert_atom_list var L (xs' @ x' # \<Gamma>)"
  apply(induction L)using convert_atom_change[OF assms] apply simp_all
  by (metis)

lemma negInf_convert :
  assumes "convert_atom_list var L (xs' @ x # xs) = Some L'"
  assumes "length xs' = var"
  shows "(\<forall>f\<in>set L. eval (substNegInfinity var f) (xs' @ x # xs))
         = (\<forall>f\<in>set L'. evalUni (substNegInfinityUni f) x)"
  using assms
proof(induction L arbitrary : L')
  case Nil
  then show ?case by auto
next
  case (Cons a L)
  then show ?case proof(cases a)
    case (Less p)
    have h:  "MPoly_Type.degree p var < 3 \<Longrightarrow>
          eval (substNegInfinity var (Less p)) (xs' @ x # xs) = evalUni
           (substNegInfinityUni
             (LessUni
               (insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var 2),
                insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var (Suc 0)),
                insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var 0))))
           x"
      using convert_substNegInfinity[of var "Less p" xs' x xs, OF _ assms(2)] by simp
    show ?thesis using Cons(2)[symmetric] Cons(1) unfolding Less apply(cases " MPoly_Type.degree p var < 3")
      defer apply simp apply(cases "convert_atom_list var L (xs' @ x # xs)") apply (simp_all del: substNegInfinity.simps substNegInfinityUni.simps)
      unfolding h
      using assms(2) by presburger
  next
    case (Eq p)
    have h:  "MPoly_Type.degree p var < 3 \<Longrightarrow>
          eval (substNegInfinity var (Eq p)) (xs' @ x # xs) = evalUni
           (substNegInfinityUni
             (EqUni
               (insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var 2),
                insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var (Suc 0)),
                insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var 0))))
           x"
      using convert_substNegInfinity[of var "Eq p", OF _ assms(2)] by simp
    show ?thesis using Cons(2)[symmetric] Cons(1) unfolding Eq apply(cases " MPoly_Type.degree p var < 3")
      defer apply simp apply(cases "convert_atom_list var L (xs' @ x # xs)") apply (simp_all del: substNegInfinity.simps substNegInfinityUni.simps)
      unfolding h assms by auto
  next
    case (Leq p)
    have h:  "MPoly_Type.degree p var < 3 \<Longrightarrow>
          eval (substNegInfinity var (Leq p)) (xs' @ x # xs) = evalUni
           (substNegInfinityUni
             (LeqUni
               (insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var 2),
                insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var (Suc 0)),
                insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var 0))))
           x"
      using convert_substNegInfinity[of var "Leq p", OF _ assms(2)] by simp
    show ?thesis using Cons(2) unfolding Leq apply(cases " MPoly_Type.degree p var < 3") 
      defer apply simp 
      apply(cases "convert_atom_list var L (xs' @ x # xs)") 
      apply (simp_all del: substNegInfinity.simps substNegInfinityUni.simps)
      unfolding h using Cons.IH assms by auto 
  next
    case (Neq p)
    have h:  "MPoly_Type.degree p var < 3 \<Longrightarrow>
          eval (substNegInfinity var (Neq p)) (xs' @ x # xs) = evalUni
           (substNegInfinityUni
             (NeqUni
               (insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var 2),
                insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var (Suc 0)),
                insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var 0))))
           x"
      using convert_substNegInfinity[of var "Neq p", OF _ assms(2)] by simp
    show ?thesis using Cons(2) unfolding Neq apply(cases " MPoly_Type.degree p var < 3") defer apply simp 
      apply(cases "convert_atom_list var L (xs' @ x # xs)") 
      apply (simp_all del: substNegInfinity.simps substNegInfinityUni.simps)
      unfolding h using Cons.IH assms by auto
  qed
qed

lemma elimVar_atom_single :
  assumes "convert_atom var A (xs' @ x # xs) = Some A'"
  assumes "convert_atom_list var L2 (xs' @ x # xs) = Some L2'"
  assumes "length xs' = var"
  shows "eval (elimVar var L2 [] A) (xs' @ x # xs) = evalUni (elimVarUni_atom L2' A') x"
proof(cases A)
  case (Less p)
  define a where "a = insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var 2)"
  have a_def' : "a = insertion (nth_default 0 (xs' @ 0 # xs)) (isolate_variable_sparse p var 2)" unfolding a_def
    using insertion_isovarspars_free[of "(xs' @ x # xs)" var x p 2 0] assms by auto
  define b where "b = insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var (Suc 0))"
  have b_def' : "b = insertion (nth_default 0 (xs' @ 0 # xs)) (isolate_variable_sparse p var (Suc 0))" unfolding b_def
    using insertion_isovarspars_free[of "(xs' @ x # xs)" var x p "(Suc 0)" 0] assms by auto
  define c where "c = insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var 0)"
  have c_def' : "c = insertion (nth_default 0 (xs' @ 0 # xs)) (isolate_variable_sparse p var 0)" unfolding c_def
    using insertion_isovarspars_free[of "(xs' @ x # xs)" var x p 0 0] assms by auto
  have linear : "b\<noteq>0 \<Longrightarrow> (\<forall>f\<in>set L2.
         eval
          (substInfinitesimalLinear var (-isolate_variable_sparse p var 0) (isolate_variable_sparse p var (Suc 0)) f)
          (xs' @ x # xs)) = (\<forall>l\<in>set L2'. evalUni (substInfinitesimalLinearUni b c l) x)"
    using assms(2) proof(induction L2 arbitrary : L2')
    case Nil
    then show ?case by auto
  next
    case (Cons At L2)
    have "\<exists>At'. convert_atom var At (xs' @ x # xs) = Some At'" proof(cases At)
      case (Less p)
      then show ?thesis using Cons(3) apply simp apply(cases "MPoly_Type.degree p var < 3") by simp_all
    next
      case (Eq p)
      then show ?thesis using Cons(3) apply simp apply(cases "MPoly_Type.degree p var < 3") by simp_all
    next
      case (Leq p)
      then show ?thesis using Cons(3) apply simp apply(cases "MPoly_Type.degree p var < 3") by auto
    next
      case (Neq p)
      then show ?thesis using Cons(3) apply simp apply(cases "MPoly_Type.degree p var < 3") by auto
    qed 
    then obtain At' where At' : "convert_atom var At (xs' @ x # xs) = Some At'" by auto
    have "\<exists>L2's. convert_atom_list var L2 (xs' @ x # xs) = Some L2's"
      using Cons(3) At'
      apply(cases "convert_atom_list var L2 (xs' @ x # xs)") by auto
    then obtain L2's where L2's : "convert_atom_list var L2 (xs' @ x # xs) = Some L2's" by auto
    have L2' : "L2' = At' # L2's"
      using Cons(3) At'
      by (simp_all add: L2's)
    have h : "eval
         (substInfinitesimalLinear var (-isolate_variable_sparse p var 0) (isolate_variable_sparse p var (Suc 0))
            At)
         (xs' @ x # xs) = evalUni (substInfinitesimalLinearUni b c At') x"
    proof(cases "convert_atom var At (xs' @ x # xs)")
      case None
      then show ?thesis using At' apply(cases At)  by simp_all
    next
      case (Some a)
      have h1 : "var \<notin> vars (isolate_variable_sparse p var (Suc 0))"
        by (simp add: not_in_isovarspar) 
      have h2 : "var \<notin> vars (isolate_variable_sparse p var 0)"by (simp add: not_in_isovarspar) 
      have h :  "evalUni (substInfinitesimalLinearUni b c a) x =
    evalUni (substInfinitesimalLinearUni b c At') x"
      proof(cases At)
        case (Less p)
        then show ?thesis using At'[symmetric] Some[symmetric] apply(cases "MPoly_Type.degree p var < 3") by simp_all
      next
        case (Eq p)
        then show ?thesis using At'[symmetric] Some[symmetric] apply(cases "MPoly_Type.degree p var < 3") by simp_all
      next
        case (Leq x3)
        then show ?thesis using At' Some by auto 
      next
        case (Neq x4)
        then show ?thesis using At' Some by auto 
      qed
      show ?thesis unfolding convert_substInfinitesimalLinear[OF Some b_def[symmetric] c_def[symmetric] Cons(2) h1 h2 assms(3)]
        using h .
    qed
    show ?case unfolding L2' using h Cons(1)[OF Cons(2) L2's] by auto
  qed
  have quadratic_1 : "(a \<noteq> 0) \<Longrightarrow>
     (4 * a * c \<le> b\<^sup>2) \<Longrightarrow> (\<forall>f\<in>set L2.
          eval
           (substInfinitesimalQuadratic var
             (- isolate_variable_sparse p var (Suc 0)) 1
             ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
              4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)
             (2 * isolate_variable_sparse p var 2) f)
           (xs' @ x # xs)) = (\<forall>l\<in>set L2'.
          evalUni
           (substInfinitesimalQuadraticUni (- b) 1 (b\<^sup>2 - 4 * a * c) (2 * a) l)
           x)"
    using assms(2) proof(induction L2 arbitrary: L2')
    case Nil
    then show ?case by auto
  next
    case (Cons At L2)
    have "\<exists>At'. convert_atom var At (xs' @ x # xs) = Some At'" proof(cases At)
      case (Less p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by simp_all
    next
      case (Eq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by simp_all
    next
      case (Leq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by auto
    next
      case (Neq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by auto
    qed 
    then obtain At' where At' : "convert_atom var At (xs' @ x # xs) = Some At'" by auto
    have "\<exists>L2's. convert_atom_list var L2 (xs' @ x # xs) = Some L2's"
      using Cons(4) At'
      apply(cases "convert_atom_list var L2 (xs' @ x # xs)") by auto
    then obtain L2's where L2's : "convert_atom_list var L2 (xs' @ x # xs) = Some L2's" by auto
    have L2' : "L2' = At' # L2's"
      using Cons(4) At' apply(cases At) apply auto
      by (simp_all add: L2's)
    have h1 :  "var < length (xs' @ x # xs)" using assms by auto
    have h2 : "2*a \<noteq>0" using Cons by auto
    have h3 : "0\<le>b^2-4*a*c" using Cons(3) by auto
    have h4 : "var\<notin>vars ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
            4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)"
      by (metis add_uminus_conv_diff not_in_add not_in_isovarspar not_in_mult not_in_neg not_in_pow num_double numeral_times_numeral one_add_one power_0)
    have h5 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa])) (- isolate_variable_sparse p var (Suc 0)) = -b"
      unfolding insertion_neg b_def
      by (metis insertion_isovarspars_free list_update_id) 
    have h6 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa])) 1 = 1" by auto
    have h7 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa]))
        ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
         4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0) =
       b\<^sup>2 - 4 * a * c" apply(simp add: insertion_four insertion_mult insertion_sub insertion_pow b_def a_def c_def)
      by (metis insertion_isovarspars_free list_update_id)
    have "\<And>xa. insertion (nth_default 0 (xs' @ xa # xs)) (2::real mpoly)  = (2::real)"
      by (metis MPoly_Type.insertion_one insertion_add one_add_one)  
    then have h8 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa])) (2 * isolate_variable_sparse p var 2) = 2 * a"
      unfolding insertion_mult a_def apply auto
      by (metis assms(3) insertion_lowerPoly1 list_update_length not_in_isovarspar)
    have h9 : "var\<notin>vars(- isolate_variable_sparse p var (Suc 0))"
      by (simp add: not_in_isovarspar not_in_neg)
    have h10 : "var\<notin>vars(1::real mpoly)"
      by (metis h9 not_in_pow power.simps(1))
    have h11 : "var\<notin>vars(2 * isolate_variable_sparse p var 2)"
      by (metis isovarspar_sum mult_2 not_in_isovarspar)
    have h :  "eval
      (substInfinitesimalQuadratic var (- isolate_variable_sparse p var (Suc 0)) 1
        ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
         4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)
        (2 * isolate_variable_sparse p var 2) At)
      (xs' @ x # xs) =  evalUni
      (substInfinitesimalQuadraticUni (- b) 1 (b\<^sup>2 - 4 * a * c) (2 * a) At') x"
    proof (cases "convert_atom var At (xs' @ x # xs)")
      case None
      then show ?thesis using At' apply(cases At) by auto
    next
      case (Some aT)
      have h1 : "insertion (nth_default 0 (xs' @ x # xs)) (- isolate_variable_sparse p var (Suc 0)) = (-b)" unfolding b_def insertion_neg by auto
      have h2 : "insertion (nth_default 0 (xs' @ x # xs)) 1 = 1" by auto
      have h3 : "insertion (nth_default 0 (xs' @ x # xs)) (((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
        4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)) = (b\<^sup>2 - 4 * a * c)"
        unfolding insertion_mult insertion_pow insertion_four insertion_neg insertion_sub a_def b_def c_def
        by auto
      have h4 : "insertion (nth_default 0 (xs' @ x # xs)) (2 * isolate_variable_sparse p var 2) = 2 * a"
        unfolding insertion_mult a_def
        by (metis insertion_add insertion_mult mult_2)
      have h5 : "2 * a \<noteq> 0" using Cons by auto
      have h6 : "0 \<le> b\<^sup>2 - 4 * a * c" using Cons by auto
      have h7 : "var\<notin>vars(- isolate_variable_sparse p var (Suc 0))"
        by (simp add: not_in_isovarspar not_in_neg)
      have h8 : "var\<notin>vars(1::real mpoly)"
        by (metis h9 not_in_pow power.simps(1))
      have h9 : "var \<notin> vars ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
             4 * isolate_variable_sparse p var 2 *
             isolate_variable_sparse p var 0)"
        by (metis add_uminus_conv_diff not_in_add not_in_isovarspar not_in_mult not_in_neg not_in_pow num_double numeral_times_numeral one_add_one power_0)
      have h10 : "var\<notin>vars(2 * isolate_variable_sparse p var 2)"
        by (metis isovarspar_sum mult_2 not_in_isovarspar)
      have h : "evalUni (substInfinitesimalQuadraticUni (- b) 1 (b\<^sup>2 - 4 * a * c) (2 * a) aT)
     x =
    evalUni (substInfinitesimalQuadraticUni (- b) 1 (b\<^sup>2 - 4 * a * c) (2 * a) At')
     x"proof(cases At)
        case (Less p)
        then show ?thesis using At'[symmetric] Some[symmetric] apply(cases "MPoly_Type.degree p var < 3") by auto
      next
        case (Eq p)
        then show ?thesis using At'[symmetric] Some[symmetric] apply(cases "MPoly_Type.degree p var < 3") by auto
      next
        case (Leq x3)
        then show ?thesis using At' using Some by auto
      next
        case (Neq x4)
        then show ?thesis using At' using Some by auto 
      qed
      show ?thesis unfolding convert_substInfinitesimalQuadratic[OF Some h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 assms(3)]
        using h .
    qed


    show ?case
      unfolding L2' apply(simp del : substInfinitesimalQuadratic.simps substInfinitesimalQuadraticUni.simps)
      unfolding 
        Cons(1)[OF Cons(2) Cons(3) L2's]
      unfolding h
      by auto
  qed
  have quadratic_2 : "(a \<noteq> 0) \<Longrightarrow>
     (4 * a * c \<le> b\<^sup>2) \<Longrightarrow> (\<forall>f\<in>set L2.
          eval
           (substInfinitesimalQuadratic var
             (- isolate_variable_sparse p var (Suc 0)) (- 1)
             ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
              4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)
             (2 * isolate_variable_sparse p var 2) f)
           (xs' @ x # xs)) = (\<forall>l\<in>set L2'.
          evalUni
           (substInfinitesimalQuadraticUni (- b) (- 1) (b\<^sup>2 - 4 * a * c) (2 * a)
             l)
           x)" 
    using assms(2) proof(induction L2 arbitrary: L2')
    case Nil
    then show ?case by auto
  next
    case (Cons At L2)
    have "\<exists>At'. convert_atom var At (xs' @ x # xs) = Some At'" proof(cases At)
      case (Less p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by simp_all
    next
      case (Eq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by simp_all
    next
      case (Leq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by auto
    next
      case (Neq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by auto
    qed 
    then obtain At' where At' : "convert_atom var At (xs' @ x # xs) = Some At'" by auto
    have "\<exists>L2's. convert_atom_list var L2 (xs' @ x # xs) = Some L2's"
      using Cons(4) At'
      apply(cases "convert_atom_list var L2 (xs' @ x # xs)") by auto
    then obtain L2's where L2's : "convert_atom_list var L2 (xs' @ x # xs) = Some L2's" by auto
    have L2' : "L2' = At' # L2's"
      using Cons(4) At' apply(cases At) apply auto
      by (simp_all add: L2's)
    have h1 :  "var < length (xs' @ x # xs)" using assms by auto
    have h2 : "2*a \<noteq>0" using Cons by auto
    have h3 : "0\<le>b^2-4*a*c" using Cons(3) by auto
    have h4 : "var\<notin>vars ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
            4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)"
      by (metis add_uminus_conv_diff not_in_add not_in_isovarspar not_in_mult not_in_neg not_in_pow num_double numeral_times_numeral one_add_one power_0)
    have h5 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa])) (- isolate_variable_sparse p var (Suc 0)) = -b"
      unfolding insertion_neg b_def
      by (metis insertion_isovarspars_free list_update_id) 
    have h6 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa])) (-1) = (-1)" unfolding insertion_neg by auto
    have h7 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa]))
        ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
         4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0) =
       b\<^sup>2 - 4 * a * c" apply(simp add: insertion_four insertion_mult insertion_sub insertion_pow b_def a_def c_def) using assms
      by (metis insertion_isovarspars_free list_update_id)
    have "\<And>xa. insertion (nth_default 0 (xs' @ xa # xs)) (2::real mpoly)  = (2::real)"
      by (metis MPoly_Type.insertion_one insertion_add one_add_one)  
    then have h8 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa])) (2 * isolate_variable_sparse p var 2) = 2 * a"
      unfolding insertion_mult a_def apply auto using assms
      by (metis (no_types, hide_lams) MPoly_Type.insertion_one add.inverse_inverse add_uminus_conv_diff arith_special(3) insertion_isovarspars_free insertion_neg insertion_sub list_update_id) 
    have h9 : "var\<notin>vars(- isolate_variable_sparse p var (Suc 0))"
      by (simp add: not_in_isovarspar not_in_neg)
    have h10 : "var\<notin>vars(- 1::real mpoly)"
      by (metis h9 not_in_neg not_in_pow power.simps(1))
    have h11 : "var\<notin>vars(2 * isolate_variable_sparse p var 2)"
      by (metis isovarspar_sum mult_2 not_in_isovarspar)
    have h :  "eval
      (substInfinitesimalQuadratic var (- isolate_variable_sparse p var (Suc 0)) (-1)
        ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
         4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)
        (2 * isolate_variable_sparse p var 2) At)
      (xs' @ x # xs) =  evalUni
      (substInfinitesimalQuadraticUni (- b) (-1) (b\<^sup>2 - 4 * a * c) (2 * a) At') x"
    proof (cases "convert_atom var At (xs' @ x # xs)")
      case None
      then show ?thesis using At' apply(cases At) by auto
    next
      case (Some aT)
      have h1 : "insertion (nth_default 0 (xs' @ x # xs)) (- isolate_variable_sparse p var (Suc 0)) = (-b)" unfolding b_def insertion_neg by auto
      have h2 : "insertion (nth_default 0 (xs' @ x # xs)) (-1) = -1" unfolding insertion_neg by auto
      have h3 : "insertion (nth_default 0 (xs' @ x # xs)) (((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
        4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)) = (b\<^sup>2 - 4 * a * c)"
        unfolding insertion_mult insertion_pow insertion_four insertion_neg insertion_sub a_def b_def c_def using assms
        by auto
      have h4 : "insertion (nth_default 0 (xs' @ x # xs)) (2 * isolate_variable_sparse p var 2) = 2 * a"
        unfolding insertion_mult a_def
        by (metis insertion_add insertion_mult mult_2)
      have h5 : "2 * a \<noteq> 0" using Cons by auto
      have h6 : "0 \<le> b\<^sup>2 - 4 * a * c" using Cons by auto
      have h7 : "var\<notin>vars(- isolate_variable_sparse p var (Suc 0))"
        by (simp add: not_in_isovarspar not_in_neg)
      have h8 : "var\<notin>vars(- 1::real mpoly)"
        by (simp add: h10 not_in_neg)
      have h9 : "var \<notin> vars ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
             4 * isolate_variable_sparse p var 2 *
             isolate_variable_sparse p var 0)"
        by (metis add_uminus_conv_diff not_in_add not_in_isovarspar not_in_mult not_in_neg not_in_pow num_double numeral_times_numeral one_add_one power_0)
      have h10 : "var\<notin>vars(2 * isolate_variable_sparse p var 2)"
        by (metis isovarspar_sum mult_2 not_in_isovarspar)
      have h : "evalUni (substInfinitesimalQuadraticUni (- b) (-1) (b\<^sup>2 - 4 * a * c) (2 * a) aT)
     x =
    evalUni (substInfinitesimalQuadraticUni (- b) (-1) (b\<^sup>2 - 4 * a * c) (2 * a) At')
     x"proof(cases At)
        case (Less p)
        then show ?thesis using At'[symmetric] Some[symmetric] apply(cases "MPoly_Type.degree p var < 3") by auto
      next
        case (Eq p)
        then show ?thesis using At'[symmetric] Some[symmetric] apply(cases "MPoly_Type.degree p var < 3") by auto
      next
        case (Leq x3)
        then show ?thesis using At'
          using Some option.inject by auto 
      next
        case (Neq x4)
        then show ?thesis using At'
          using Some by auto 
      qed
      show ?thesis unfolding convert_substInfinitesimalQuadratic[OF Some h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 assms(3)]
        using h .
    qed


    show ?case
      unfolding L2' apply(simp del : substInfinitesimalQuadratic.simps substInfinitesimalQuadraticUni.simps)
      unfolding 
        Cons(1)[OF Cons(2) Cons(3) L2's]
      unfolding h
      by auto
  qed

  show ?thesis using assms(1)[symmetric] unfolding Less apply(cases "MPoly_Type.degree p var < 3") apply simp_all
    apply(simp del : substInfinitesimalLinear.simps substInfinitesimalLinearUni.simps substInfinitesimalQuadratic.simps substInfinitesimalQuadraticUni.simps
        add: insertion_neg insertion_mult insertion_add insertion_pow insertion_sub insertion_four
        a_def[symmetric] b_def[symmetric] c_def[symmetric] a_def'[symmetric] b_def'[symmetric] c_def'[symmetric] eval_list_conj
        eval_list_conj_Uni
        ) using linear quadratic_1 quadratic_2 by smt
next
  case (Eq p)
  define a where "a = insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var 2)"
  have a_def' : "a = insertion (nth_default 0 (xs' @ 0 # xs)) (isolate_variable_sparse p var 2)" unfolding a_def
    using insertion_isovarspars_free[of "xs' @x#xs" var x p 2 0] using assms by auto
  define b where "b = insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var (Suc 0))"
  have b_def' : "b = insertion (nth_default 0 (xs' @ 0 # xs)) (isolate_variable_sparse p var (Suc 0))" unfolding b_def
    using insertion_isovarspars_free[of "xs' @x#xs" var x p "(Suc 0)" 0] using assms by auto
  define c where "c = insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var 0)"
  have c_def' : "c = insertion (nth_default 0 (xs' @ 0 # xs)) (isolate_variable_sparse p var 0)" unfolding c_def
    using insertion_isovarspars_free[of "xs' @x#xs" var x p 0 0]using assms by auto
  have linear : "a=0 \<Longrightarrow> b\<noteq>0 \<Longrightarrow> (\<forall>f\<in>set L2.
         aEval
          (linear_substitution var 
            (-isolate_variable_sparse p var 0) (isolate_variable_sparse p var (Suc 0)) f)
          (xs' @ x # xs)) = (\<forall>l\<in>set L2'. evalUni (linearSubstitutionUni b c l) x)"

    using assms(2)
  proof(induction L2 arbitrary: L2')
    case Nil
    then show ?case by auto
  next
    case (Cons At L2)
    have "\<exists>At'. convert_atom var At (xs' @ x # xs) = Some At'" proof(cases At)
      case (Less p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by simp_all
    next
      case (Eq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by simp_all
    next
      case (Leq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by auto
    next
      case (Neq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by auto
    qed 
    then obtain At' where At' : "convert_atom var At (xs' @ x # xs) = Some At'" by auto
    have "\<exists>L2's. convert_atom_list var L2 (xs' @ x # xs) = Some L2's"
      using Cons(4) At'
      apply(cases "convert_atom_list var L2 (xs' @ x # xs)") by auto
    then obtain L2's where L2's : "convert_atom_list var L2 (xs' @ x # xs) = Some L2's" by auto
    have L2' : "L2' = At' # L2's"
      using Cons(4) At' apply(cases At) apply auto
      by (simp_all add: L2's)
    have h1 : "var \<notin> vars (isolate_variable_sparse p var (Suc 0))"
      by (simp add: not_in_isovarspar) 
    have h2 : "var \<notin> vars (isolate_variable_sparse p var 0)"by (simp add: not_in_isovarspar) 
    have h : "aEval
         (linear_substitution var
           (-isolate_variable_sparse p var 0) (isolate_variable_sparse p var (Suc 0)) At)
         (xs' @ x # xs) = evalUni (linearSubstitutionUni b c At') x"
    proof(cases "convert_atom var At (xs' @ x # xs)")
      case None
      then show ?thesis using At' apply(cases At) by auto
    next
      case (Some a)
      have h : "a=At'"
        using At' Some by auto
      show ?thesis unfolding convert_linearSubstitutionUni[OF Some b_def[symmetric] c_def[symmetric] Cons(3) h1 h2 assms(3)] 
        unfolding h by auto
    qed 
    have "(\<forall>f\<in>set (At # L2).
        aEval
         (linear_substitution var
           (-isolate_variable_sparse p var 0) (isolate_variable_sparse p var (Suc 0)) f)
         (xs' @ x # xs)) = (aEval
         (linear_substitution var 
           (-isolate_variable_sparse p var 0)(isolate_variable_sparse p var (Suc 0)) At)
         (xs' @ x # xs)\<and> (\<forall>f\<in>set (L2).
        aEval
         (linear_substitution var
           (-isolate_variable_sparse p var 0) (isolate_variable_sparse p var (Suc 0)) f)
         (xs' @ x # xs)))" by auto
    also have "... = (evalUni (linearSubstitutionUni b c At') x \<and>
     (\<forall>l\<in>set L2's. evalUni (linearSubstitutionUni b c l) x))"
      unfolding h Cons(1)[OF Cons(2) Cons(3) L2's]  by auto
    finally show ?case   unfolding L2' by auto
  qed

  have quadratic_1 : "(a \<noteq> 0) \<Longrightarrow>
     (4 * a * c \<le> b\<^sup>2) \<Longrightarrow>(\<forall>f\<in>set L2.
          eval
           (quadratic_sub var (- isolate_variable_sparse p var (Suc 0)) 1
             ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
              4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)
             (2 * isolate_variable_sparse p var 2) f)
           (xs' @ x # xs)) = (\<forall>l\<in>set L2'.
          evalUni (quadraticSubUni (- b) 1 (b\<^sup>2 - 4 * a * c) (2 * a) l) x)"
    using assms(2) proof(induction L2 arbitrary: L2')
    case Nil
    then show ?case by auto
  next
    case (Cons At L2)
    have "\<exists>At'. convert_atom var At (xs' @ x # xs) = Some At'" proof(cases At)
      case (Less p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by simp_all
    next
      case (Eq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by simp_all
    next
      case (Leq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by auto
    next
      case (Neq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by auto
    qed 
    then obtain At' where At' : "convert_atom var At (xs' @ x # xs) = Some At'" by auto
    have "\<exists>L2's. convert_atom_list var L2 (xs' @ x # xs) = Some L2's"
      using Cons(4) At'
      apply(cases "convert_atom_list var L2 (xs' @ x # xs)") by auto
    then obtain L2's where L2's : "convert_atom_list var L2 (xs' @ x # xs) = Some L2's" by auto
    have L2' : "L2' = At' # L2's"
      using Cons(4) At' apply(cases At) apply auto
      by (simp_all add: L2's)
    have h1 :  "var < length (xs' @ x # xs)" using assms by auto
    have h2 : "2*a \<noteq>0" using Cons by auto
    have h3 : "0\<le>b^2-4*a*c" using Cons(3) by auto
    have h4 : "var\<notin>vars ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
            4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)"
      by (metis add_uminus_conv_diff not_in_add not_in_isovarspar not_in_mult not_in_neg not_in_pow num_double numeral_times_numeral one_add_one power_0)
    have h5 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa])) (- isolate_variable_sparse p var (Suc 0)) = -b"
      unfolding insertion_neg b_def
      by (metis insertion_isovarspars_free list_update_id) 
    have h6 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa])) 1 = 1" by auto
    have h7 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa]))
        ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
         4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0) =
       b\<^sup>2 - 4 * a * c" apply(simp add: insertion_four insertion_mult insertion_sub insertion_pow b_def a_def c_def)
      by (metis insertion_isovarspars_free list_update_id)
    have "\<And>xa. insertion (nth_default 0 (xs' @ xa # xs)) (2::real mpoly)  = (2::real)"
      by (metis MPoly_Type.insertion_one insertion_add one_add_one)  
    then have h8 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa])) (2 * isolate_variable_sparse p var 2) = 2 * a"
      unfolding insertion_mult a_def apply auto
      by (metis assms(3) insertion_add insertion_isovarspars_free insertion_mult list_update_length mult_2)
    have h9 : "var\<notin>vars(- isolate_variable_sparse p var (Suc 0))"
      by (simp add: not_in_isovarspar not_in_neg)
    have h10 : "var\<notin>vars(1::real mpoly)"
      by (metis h9 not_in_pow power.simps(1))
    have h11 : "var\<notin>vars(2 * isolate_variable_sparse p var 2)"
      by (metis isovarspar_sum mult_2 not_in_isovarspar)
    have h :  "eval
     (quadratic_sub var (- isolate_variable_sparse p var (Suc 0)) 1
       ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
        4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)
       (2 * isolate_variable_sparse p var 2) At)
     (xs' @ x # xs) =  aEval At (xs' @ (((- b + 1 * sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a)) # xs))"
      using quadratic_sub[OF h1 h2 h3 h4 h5 h6 h7 h8, symmetric, of At]
        free_in_quad[OF h9 h10 h4 h11]
      by (metis assms(3) list_update_length var_not_in_eval3) 
    have h2 : "aEval At (xs' @ (- b + 1 * sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a) # xs) = evalUni (quadraticSubUni (- b) 1 (b\<^sup>2 - 4 * a * c) (2 * a) At') x"
    proof(cases At)
      case (Less p)
      then show ?thesis
      proof(cases "convert_atom var At (xs' @ x # xs)")
        case None
        then show ?thesis
          using At'[symmetric] apply(cases "MPoly_Type.degree p var < 3") by simp_all
      next
        case (Some aT)
        then have Some : "\<And>x. convert_atom var At (xs' @ x # xs) = Some aT"
          by (metis assms(3) convert_atom_change) 
        show ?thesis unfolding aEval_aEvalUni[OF Some assms(3)]
          using At'[symmetric] Some[symmetric]
          unfolding Less apply(cases "MPoly_Type.degree p var < 3")  by simp_all
      qed
    next
      case (Eq p)
      then show ?thesis proof(cases "convert_atom var At (xs' @ x # xs)")
        case None
        then show ?thesis
          using At'[symmetric] apply(cases "MPoly_Type.degree p var < 3") by simp_all
      next
        case (Some aT)
        then have Some : "\<And>x. convert_atom var At (xs' @ x # xs) = Some aT"
          by (metis assms(3) convert_atom_change) 
        show ?thesis unfolding aEval_aEvalUni[OF Some assms(3)]
          using At'[symmetric] Some[symmetric]
          unfolding Eq apply(cases "MPoly_Type.degree p var < 3")  by simp_all
      qed
    next
      case (Leq x3)
      then show ?thesis proof(cases "convert_atom var At (xs' @ x # xs)")
        case None
        then show ?thesis
          using At'[symmetric] apply(cases "MPoly_Type.degree p var < 3") by simp_all
      next
        case (Some aT)
        then have Some : "\<And>x. convert_atom var At (xs' @ x # xs) = Some aT"
          by (metis assms(3) convert_atom_change) 
        show ?thesis unfolding aEval_aEvalUni[OF Some assms(3)]
          using At'[symmetric] Some[symmetric]
          unfolding Leq apply(cases "MPoly_Type.degree p var < 3") by auto
      qed
    next
      case (Neq x4)
      then show ?thesis 
      proof(cases "convert_atom var At (xs' @ x # xs)")
        case None
        then show ?thesis
          using At'[symmetric] apply(cases "MPoly_Type.degree p var < 3") by simp_all
      next
        case (Some aT)
        then have Some : "\<And>x. convert_atom var At (xs' @ x # xs) = Some aT"
          by (metis assms(3) convert_atom_change) 
        show ?thesis unfolding aEval_aEvalUni[OF Some assms(3)]
          using At'[symmetric] Some[symmetric]
          unfolding Neq apply(cases "MPoly_Type.degree p var < 3") by auto
      qed
    qed
    show ?case
      unfolding L2' apply(simp del : quadratic_sub.simps quadraticSubUni.simps)
      unfolding 
        Cons(1)[OF Cons(2) Cons(3) L2's]
      unfolding h h2
      by auto
  qed
  have quadratic_2 : "(a \<noteq> 0) \<Longrightarrow>
     (4 * a * c \<le> b\<^sup>2) \<Longrightarrow> (\<forall>f\<in>set L2.
          eval
           (quadratic_sub var (- isolate_variable_sparse p var (Suc 0)) (- 1)
             ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
              4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)
             (2 * isolate_variable_sparse p var 2) f)
           (xs' @ x # xs)) = (\<forall>l\<in>set L2'.
          evalUni (quadraticSubUni (- b) (- 1) (b\<^sup>2 - 4 * a * c) (2 * a) l) x)"
    using assms(2) proof(induction L2 arbitrary: L2')
    case Nil
    then show ?case by auto
  next
    case (Cons At L2)
    have "\<exists>At'. convert_atom var At (xs' @ x # xs) = Some At'" proof(cases At)
      case (Less p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by simp_all
    next
      case (Eq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by simp_all
    next
      case (Leq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by auto
    next
      case (Neq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by auto
    qed 
    then obtain At' where At' : "convert_atom var At (xs' @ x # xs) = Some At'" using assms by auto
    have "\<exists>L2's. convert_atom_list var L2 (xs' @ x # xs) = Some L2's"
      using Cons(4) At'
      apply(cases "convert_atom_list var L2 (xs' @ x # xs)") by auto
    then obtain L2's where L2's : "convert_atom_list var L2 (xs' @ x # xs) = Some L2's" by auto
    have L2' : "L2' = At' # L2's"
      using Cons(4) At' apply(cases At) apply auto
      by (simp_all add: L2's)
    have h1 :  "var < length (xs' @ x # xs)" using assms by auto
    have h2 : "2*a \<noteq>0" using Cons by auto
    have h3 : "0\<le>b^2-4*a*c" using Cons(3) by auto
    have h4 : "var\<notin>vars ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
            4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)"
      by (metis add_uminus_conv_diff not_in_add not_in_isovarspar not_in_mult not_in_neg not_in_pow num_double numeral_times_numeral one_add_one power_0)
    have h5 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa])) (- isolate_variable_sparse p var (Suc 0)) = -b"
      unfolding insertion_neg b_def
      by (metis insertion_isovarspars_free list_update_id) 
    have h6 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa])) (-1) = -1"
      unfolding insertion_neg
      by auto
    have h7 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa]))
        ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
         4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0) =
       b\<^sup>2 - 4 * a * c" apply(simp add: insertion_four insertion_mult insertion_sub insertion_pow b_def a_def c_def)
      by (metis insertion_isovarspars_free list_update_id)
    have "\<And>xa. insertion (nth_default 0 (xs' @xa # xs)) (2::real mpoly)  = (2::real)"
      by (metis MPoly_Type.insertion_one insertion_add one_add_one)  
    then have h8 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa])) (2 * isolate_variable_sparse p var 2) = 2 * a"
      unfolding insertion_mult a_def apply auto
      by (metis assms(3) insertion_lowerPoly1 list_update_length not_in_isovarspar)
    have h9 : "var\<notin>vars(- isolate_variable_sparse p var (Suc 0))"
      by (simp add: not_in_isovarspar not_in_neg)
    have h10 : "var\<notin>vars(-1::real mpoly)"
      by (metis h9 not_in_neg not_in_pow power.simps(1))
    have h11 : "var\<notin>vars(2 * isolate_variable_sparse p var 2)"
      by (metis isovarspar_sum mult_2 not_in_isovarspar)
    have h :  "eval
     (quadratic_sub var (- isolate_variable_sparse p var (Suc 0)) (-1)
       ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
        4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)
       (2 * isolate_variable_sparse p var 2) At)
     (xs' @ x # xs) =  aEval At (xs' @ (((- b - 1 * sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a)) # xs))"
      using quadratic_sub[OF h1 h2 h3 h4 h5 h6 h7 h8, symmetric, of At]
        var_not_in_eval3 free_in_quad[OF h9 h10 h4 h11]
      using assms(3) by fastforce 
    have h2 : "aEval At (xs'  @ (- b - 1 * sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a) # xs) = evalUni (quadraticSubUni (- b) (-1) (b\<^sup>2 - 4 * a * c) (2 * a) At') x"
    proof(cases At)
      case (Less p)
      then show ?thesis
      proof(cases "convert_atom var At (xs' @ x # xs)")
        case None
        then show ?thesis
          using At'[symmetric] apply(cases "MPoly_Type.degree p var < 3") by simp_all
      next
        case (Some aT)
        then have Some : "\<And>x. convert_atom var At (xs' @ x # xs) = Some aT"
          by (metis assms(3) convert_atom_change) 
        show ?thesis unfolding aEval_aEvalUni[OF Some assms(3)]
          using At'[symmetric] Some[symmetric]
          unfolding Less apply(cases "MPoly_Type.degree p var < 3")  by simp_all
      qed
    next
      case (Eq p)
      then show ?thesis proof(cases "convert_atom var At (xs' @ x # xs)")
        case None
        then show ?thesis
          using At'[symmetric] apply(cases "MPoly_Type.degree p var < 3") by simp_all
      next
        case (Some aT)
        then have Some : "\<And>x. convert_atom var At (xs' @ x # xs) = Some aT"
          by (metis assms(3) convert_atom_change) 
        show ?thesis unfolding aEval_aEvalUni[OF Some assms(3)]
          using At'[symmetric] Some[symmetric]
          unfolding Eq apply(cases "MPoly_Type.degree p var < 3") by simp_all
      qed
    next
      case (Leq x3)
      then show ?thesis proof(cases "convert_atom var At (xs' @ x # xs)")
        case None
        then show ?thesis
          using At'[symmetric] apply(cases "MPoly_Type.degree p var < 3") by simp_all
      next
        case (Some aT)
        then have Some : "\<And>x. convert_atom var At (xs' @ x # xs) = Some aT"
          by (metis assms(3) convert_atom_change) 
        show ?thesis unfolding aEval_aEvalUni[OF Some assms(3)]
          using At'[symmetric] Some[symmetric]
          unfolding Leq apply(cases "MPoly_Type.degree p var < 3") by auto
      qed
    next
      case (Neq x4)
      then show ?thesis proof(cases "convert_atom var At (xs' @ x # xs)")
        case None
        then show ?thesis
          using At'[symmetric] apply(cases "MPoly_Type.degree p var < 3") by simp_all
      next
        case (Some aT)
        then have Some : "\<And>x. convert_atom var At (xs' @ x # xs) = Some aT"
          by (metis assms(3) convert_atom_change) 
        show ?thesis unfolding aEval_aEvalUni[OF Some assms(3)]
          using At'[symmetric] Some[symmetric]
          unfolding Neq apply(cases "MPoly_Type.degree p var < 3") by auto
      qed
    qed
    show ?case
      unfolding L2' apply(simp del : quadratic_sub.simps quadraticSubUni.simps)
      unfolding 
        Cons(1)[OF Cons(2) Cons(3) L2's]
      unfolding h h2
      by auto
  qed
  show ?thesis using assms(1)[symmetric] unfolding Eq apply(cases "MPoly_Type.degree p var < 3") apply simp_all
    apply(simp del : linearSubstitutionUni.simps quadraticSubUni.simps
        add: insertion_neg insertion_mult insertion_add insertion_pow insertion_sub insertion_four
        a_def[symmetric] b_def[symmetric] c_def[symmetric] a_def'[symmetric] b_def'[symmetric] c_def'[symmetric] eval_list_conj
        eval_list_conj_Uni )using linear
    using quadratic_1 quadratic_2
    by smt
next
  case (Leq p)
  define a where "a = insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var 2)"
  have a_def' : "a = insertion (nth_default 0 (xs' @ 0 # xs)) (isolate_variable_sparse p var 2)" unfolding a_def
    using insertion_isovarspars_free[of "xs'@ x#xs" var x p 2 0] using assms by auto
  define b where "b = insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var (Suc 0))"
  have b_def' : "b = insertion (nth_default 0 (xs'@ 0 # xs)) (isolate_variable_sparse p var (Suc 0))" unfolding b_def
    using insertion_isovarspars_free[of "xs'@x#xs" var x p "(Suc 0)" 0] using assms by auto
  define c where "c = insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var 0)"
  have c_def' : "c = insertion (nth_default 0 (xs'@ 0 # xs)) (isolate_variable_sparse p var 0)" unfolding c_def
    using insertion_isovarspars_free[of "xs'@ x#xs" var x p 0 0] using assms by auto
  have linear : "a=0 \<Longrightarrow> b\<noteq>0 \<Longrightarrow> (\<forall>f\<in>set L2.
         aEval
          (linear_substitution var 
            (-isolate_variable_sparse p var 0) (isolate_variable_sparse p var (Suc 0)) f)
          (xs' @ x # xs)) = (\<forall>l\<in>set L2'. evalUni (linearSubstitutionUni b c l) x)"
    using assms(2)
  proof(induction L2 arbitrary: L2')
    case Nil
    then show ?case by auto
  next
    case (Cons At L2)
    have "\<exists>At'. convert_atom var At (xs' @ x # xs) = Some At'" proof(cases At)
      case (Less p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by simp_all
    next
      case (Eq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by simp_all
    next
      case (Leq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by auto
    next
      case (Neq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by auto
    qed 
    then obtain At' where At' : "convert_atom var At (xs' @ x # xs) = Some At'" by auto
    have "\<exists>L2's. convert_atom_list var L2 (xs' @ x # xs) = Some L2's"
      using Cons(4) At'
      apply(cases "convert_atom_list var L2 (xs' @ x # xs)") by auto
    then obtain L2's where L2's : "convert_atom_list var L2 (xs' @ x # xs) = Some L2's" by auto
    have L2' : "L2' = At' # L2's"
      using Cons(4) At' apply(cases At) apply auto
      by (simp_all add: L2's)
    have h1 : "var \<notin> vars (isolate_variable_sparse p var (Suc 0))"
      by (simp add: not_in_isovarspar) 
    have h2 : "var \<notin> vars (isolate_variable_sparse p var 0)"by (simp add: not_in_isovarspar) 
    have h : "aEval
         (linear_substitution var 
           (-isolate_variable_sparse p var 0) (isolate_variable_sparse p var (Suc 0)) At)
         (xs' @ x # xs) = evalUni (linearSubstitutionUni b c At') x"
    proof(cases "convert_atom var At (xs' @ x # xs)")
      case None
      then show ?thesis using At' apply(cases At) by auto
    next
      case (Some a)
      have h : "a=At'"
        using At' Some by auto
      show ?thesis unfolding convert_linearSubstitutionUni[OF Some b_def[symmetric] c_def[symmetric] Cons(3) h1 h2 assms(3)] 
        unfolding h by auto
    qed 
    have "(\<forall>f\<in>set (At # L2).
        aEval
         (linear_substitution var 
           (-isolate_variable_sparse p var 0) (isolate_variable_sparse p var (Suc 0)) f)
         (xs' @ x # xs)) = (aEval
         (linear_substitution var 
           (-isolate_variable_sparse p var 0) (isolate_variable_sparse p var (Suc 0)) At)
         (xs' @ x # xs)\<and> (\<forall>f\<in>set (L2).
        aEval
         (linear_substitution var 
           (-isolate_variable_sparse p var 0) (isolate_variable_sparse p var (Suc 0)) f)
         (xs' @ x # xs)))" by auto
    also have "... = (evalUni (linearSubstitutionUni b c At') x \<and>
     (\<forall>l\<in>set L2's. evalUni (linearSubstitutionUni b c l) x))"
      unfolding h Cons(1)[OF Cons(2) Cons(3) L2's]  by auto
    finally show ?case   unfolding L2' by auto
  qed

  have quadratic_1 : "(a \<noteq> 0) \<Longrightarrow>
     (4 * a * c \<le> b\<^sup>2) \<Longrightarrow>(\<forall>f\<in>set L2.
          eval
           (quadratic_sub var (- isolate_variable_sparse p var (Suc 0)) 1
             ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
              4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)
             (2 * isolate_variable_sparse p var 2) f)
           (xs' @ x # xs)) = (\<forall>l\<in>set L2'.
          evalUni (quadraticSubUni (- b) 1 (b\<^sup>2 - 4 * a * c) (2 * a) l) x)"
    using assms(2) proof(induction L2 arbitrary: L2')
    case Nil
    then show ?case by auto
  next
    case (Cons At L2)
    have "\<exists>At'. convert_atom var At (xs' @ x # xs) = Some At'" proof(cases At)
      case (Less p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by simp_all
    next
      case (Eq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by simp_all
    next
      case (Leq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by auto
    next
      case (Neq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by auto
    qed 
    then obtain At' where At' : "convert_atom var At (xs' @ x # xs) = Some At'" by auto
    have "\<exists>L2's. convert_atom_list var L2 (xs' @ x # xs) = Some L2's"
      using Cons(4) At'
      apply(cases "convert_atom_list var L2 (xs' @ x # xs)") by auto
    then obtain L2's where L2's : "convert_atom_list var L2 (xs' @ x # xs) = Some L2's" by auto
    have L2' : "L2' = At' # L2's"
      using Cons(4) At' apply(cases At) apply auto
      by (simp_all add: L2's)
    have h1 :  "var < length (xs' @ x # xs)" using assms by auto
    have h2 : "2*a \<noteq>0" using Cons by auto
    have h3 : "0\<le>b^2-4*a*c" using Cons(3) by auto
    have h4 : "var\<notin>vars ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
            4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)"
      by (metis add_uminus_conv_diff not_in_add not_in_isovarspar not_in_mult not_in_neg not_in_pow num_double numeral_times_numeral one_add_one power_0)
    have h5 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa])) (- isolate_variable_sparse p var (Suc 0)) = -b"
      unfolding insertion_neg b_def
      by (metis insertion_isovarspars_free list_update_id) 
    have h6 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa])) 1 = 1" by auto
    have h7 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa]))
        ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
         4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0) =
       b\<^sup>2 - 4 * a * c" apply(simp add: insertion_four insertion_mult insertion_sub insertion_pow b_def a_def c_def)
      by (metis insertion_isovarspars_free list_update_id)
    have "\<And>xa. insertion (nth_default 0 (xs' @xa # xs)) (2::real mpoly)  = (2::real)"
      by (metis MPoly_Type.insertion_one insertion_add one_add_one)  
    then have h8 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa])) (2 * isolate_variable_sparse p var 2) = 2 * a"
      unfolding insertion_mult a_def apply auto
      by (metis assms(3) insertion_lowerPoly1 list_update_length not_in_isovarspar)
    have h9 : "var\<notin>vars(- isolate_variable_sparse p var (Suc 0))"
      by (simp add: not_in_isovarspar not_in_neg)
    have h10 : "var\<notin>vars(1::real mpoly)"
      by (metis h9 not_in_pow power.simps(1))
    have h11 : "var\<notin>vars(2 * isolate_variable_sparse p var 2)"
      by (metis isovarspar_sum mult_2 not_in_isovarspar)
    have h :  "eval
     (quadratic_sub var (- isolate_variable_sparse p var (Suc 0)) 1
       ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
        4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)
       (2 * isolate_variable_sparse p var 2) At)
     (xs' @ x # xs) =  aEval At (xs' @ (((- b + 1 * sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a)) # xs))"
      using quadratic_sub[OF h1 h2 h3 h4 h5 h6 h7 h8, symmetric, of At]
        var_not_in_eval3 free_in_quad[OF h9 h10 h4 h11]
      by (metis assms(3) list_update_length) 
    have h2 : "aEval At (xs' @ (- b + 1 * sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a) # xs) = evalUni (quadraticSubUni (- b) 1 (b\<^sup>2 - 4 * a * c) (2 * a) At') x"
    proof(cases At)
      case (Less p)
      then show ?thesis
      proof(cases "convert_atom var At (xs' @ x # xs)")
        case None
        then show ?thesis
          using At'[symmetric] apply(cases "MPoly_Type.degree p var < 3") by simp_all
      next
        case (Some aT)
        then have Some : "\<And>x. convert_atom var At (xs' @ x # xs) = Some aT"
          by (metis assms(3) convert_atom_change) 
        show ?thesis unfolding aEval_aEvalUni[OF Some assms(3)]
          using At'[symmetric] Some[symmetric]
          unfolding Less apply(cases "MPoly_Type.degree p var < 3") by simp_all
      qed
    next
      case (Eq p)
      then show ?thesis proof(cases "convert_atom var At (xs' @ x # xs)")
        case None
        then show ?thesis
          using At'[symmetric] apply(cases "MPoly_Type.degree p var < 3") by simp_all
      next
        case (Some aT)
        then have Some : "\<And>x. convert_atom var At (xs' @ x # xs) = Some aT"
          by (metis assms(3) convert_atom_change) 
        show ?thesis unfolding aEval_aEvalUni[OF Some assms(3)]
          using At'[symmetric] Some[symmetric]
          unfolding Eq apply(cases "MPoly_Type.degree p var < 3") by simp_all
      qed
    next
      case (Leq x3)
      then show ?thesis proof(cases "convert_atom var At (xs' @ x # xs)")
        case None
        then show ?thesis
          using At'[symmetric] apply(cases "MPoly_Type.degree p var < 3") by simp_all
      next
        case (Some aT)
        then have Some : "\<And>x. convert_atom var At (xs' @ x # xs) = Some aT"
          by (metis assms(3) convert_atom_change) 
        show ?thesis unfolding aEval_aEvalUni[OF Some assms(3)]
          using At'[symmetric] Some[symmetric]
          unfolding Leq apply(cases "MPoly_Type.degree p var < 3") by auto
      qed
    next
      case (Neq x4)
      then show ?thesis 
      proof(cases "convert_atom var At (xs' @ x # xs)")
        case None
        then show ?thesis
          using At'[symmetric] apply(cases "MPoly_Type.degree p var < 3") by simp_all
      next
        case (Some aT)
        then have Some : "\<And>x. convert_atom var At (xs' @ x # xs) = Some aT"
          by (metis assms(3) convert_atom_change) 
        show ?thesis unfolding aEval_aEvalUni[OF Some assms(3)]
          using At'[symmetric] Some[symmetric]
          unfolding Neq apply(cases "MPoly_Type.degree p var < 3") by auto
      qed
    qed
    show ?case
      unfolding L2' apply(simp del : quadratic_sub.simps quadraticSubUni.simps)
      unfolding 
        Cons(1)[OF Cons(2) Cons(3) L2's]
      unfolding h h2
      by auto
  qed
  have quadratic_2 : "(a \<noteq> 0) \<Longrightarrow>
     (4 * a * c \<le> b\<^sup>2) \<Longrightarrow> (\<forall>f\<in>set L2.
          eval
           (quadratic_sub var (- isolate_variable_sparse p var (Suc 0)) (- 1)
             ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
              4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)
             (2 * isolate_variable_sparse p var 2) f)
           (xs' @ x # xs)) = (\<forall>l\<in>set L2'.
          evalUni (quadraticSubUni (- b) (- 1) (b\<^sup>2 - 4 * a * c) (2 * a) l) x)"
    using assms(2) proof(induction L2 arbitrary: L2')
    case Nil
    then show ?case by auto
  next
    case (Cons At L2)
    have "\<exists>At'. convert_atom var At (xs' @ x # xs) = Some At'" proof(cases At)
      case (Less p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by simp_all
    next
      case (Eq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by simp_all
    next
      case (Leq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by auto
    next
      case (Neq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by auto
    qed 
    then obtain At' where At' : "convert_atom var At (xs' @ x # xs) = Some At'" by auto
    have "\<exists>L2's. convert_atom_list var L2 (xs' @ x # xs) = Some L2's"
      using Cons(4) At'
      apply(cases "convert_atom_list var L2 (xs' @ x # xs)") by auto
    then obtain L2's where L2's : "convert_atom_list var L2 (xs' @ x # xs) = Some L2's" by auto
    have L2' : "L2' = At' # L2's"
      using Cons(4) At' apply(cases At) apply auto
      by (simp_all add: L2's)
    have h1 :  "var < length (xs' @ x # xs)" using assms by auto
    have h2 : "2*a \<noteq>0" using Cons by auto
    have h3 : "0\<le>b^2-4*a*c" using Cons(3) by auto
    have h4 : "var\<notin>vars ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
            4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)"
      by (metis add_uminus_conv_diff not_in_add not_in_isovarspar not_in_mult not_in_neg not_in_pow num_double numeral_times_numeral one_add_one power_0)
    have h5 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa])) (- isolate_variable_sparse p var (Suc 0)) = -b"
      unfolding insertion_neg b_def
      by (metis insertion_isovarspars_free list_update_id) 
    have h6 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa])) (-1) = -1"
      unfolding insertion_neg
      by auto
    have h7 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa]))
        ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
         4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0) =
       b\<^sup>2 - 4 * a * c" apply(simp add: insertion_four insertion_mult insertion_sub insertion_pow b_def a_def c_def)
      by (metis insertion_isovarspars_free list_update_id)
    have "\<And>xa. insertion (nth_default 0 (xs' @ xa # xs)) (2::real mpoly)  = (2::real)"
      by (metis MPoly_Type.insertion_one insertion_add one_add_one)  
    then have h8 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa])) (2 * isolate_variable_sparse p var 2) = 2 * a"
      unfolding insertion_mult a_def apply auto
      by (metis assms(3) insertion_lowerPoly1 list_update_length not_in_isovarspar)
    have h9 : "var\<notin>vars(- isolate_variable_sparse p var (Suc 0))"
      by (simp add: not_in_isovarspar not_in_neg)
    have h10 : "var\<notin>vars(-1::real mpoly)"
      by (metis h9 not_in_neg not_in_pow power.simps(1))
    have h11 : "var\<notin>vars(2 * isolate_variable_sparse p var 2)"
      by (metis isovarspar_sum mult_2 not_in_isovarspar)
    have h :  "eval
     (quadratic_sub var (- isolate_variable_sparse p var (Suc 0)) (-1)
       ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
        4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)
       (2 * isolate_variable_sparse p var 2) At)
     (xs' @ x # xs) =  aEval At (xs' @(((- b - 1 * sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a)) # xs))"
      using quadratic_sub[OF h1 h2 h3 h4 h5 h6 h7 h8, symmetric, of At]
        var_not_in_eval3 free_in_quad[OF h9 h10 h4 h11]
      using assms(3) by fastforce 
    have h2 : "aEval At (xs'  @(- b - 1 * sqrt (b\<^sup>2 - 4 * a * c)) / (2 * a) # xs) = evalUni (quadraticSubUni (- b) (-1) (b\<^sup>2 - 4 * a * c) (2 * a) At') x"
    proof(cases At)
      case (Less p)
      then show ?thesis
      proof(cases "convert_atom var At (xs' @ x # xs)")
        case None
        then show ?thesis
          using At'[symmetric] apply(cases "MPoly_Type.degree p var < 3") by simp_all
      next
        case (Some aT)
        then have Some : "\<And>x. convert_atom var At (xs' @ x # xs) = Some aT"
          by (metis assms(3) convert_atom_change) 
        show ?thesis unfolding aEval_aEvalUni[OF Some assms(3)]
          using At'[symmetric] Some[symmetric]
          unfolding Less apply(cases "MPoly_Type.degree p var < 3")  by simp_all 
      qed
    next
      case (Eq p)
      then show ?thesis proof(cases "convert_atom var At (xs' @ x # xs)")
        case None
        then show ?thesis
          using At'[symmetric] apply(cases "MPoly_Type.degree p var < 3") by simp_all
      next
        case (Some aT)
        then have Some : "\<And>x. convert_atom var At (xs' @ x # xs) = Some aT"
          by (metis assms(3) convert_atom_change) 
        show ?thesis unfolding aEval_aEvalUni[OF Some assms(3)]
          using At'[symmetric] Some[symmetric]
          unfolding Eq apply(cases "MPoly_Type.degree p var < 3") by simp_all
      qed
    next
      case (Leq x3)
      then show ?thesis proof(cases "convert_atom var At (xs' @ x # xs)")
        case None
        then show ?thesis
          using At'[symmetric] apply(cases "MPoly_Type.degree p var < 3") by simp_all
      next
        case (Some aT)
        then have Some : "\<And>x. convert_atom var At (xs' @ x # xs) = Some aT"
          by (metis assms(3) convert_atom_change) 
        show ?thesis unfolding aEval_aEvalUni[OF Some assms(3)]
          using At'[symmetric] Some[symmetric]
          unfolding Leq apply(cases "MPoly_Type.degree p var < 3")
          by (auto)
      qed
    next
      case (Neq x4)
      then show ?thesis proof(cases "convert_atom var At (xs' @ x # xs)")
        case None
        then show ?thesis
          using At'[symmetric] apply(cases "MPoly_Type.degree p var < 3") by simp_all
      next
        case (Some aT)
        then have Some : "\<And>x. convert_atom var At (xs' @ x # xs) = Some aT"
          by (metis assms(3) convert_atom_change) 
        show ?thesis unfolding aEval_aEvalUni[OF Some assms(3)]
          using At'[symmetric] Some[symmetric]
          unfolding Neq apply(cases "MPoly_Type.degree p var < 3") by auto
      qed
    qed
    show ?case
      unfolding L2' apply(simp del : quadratic_sub.simps quadraticSubUni.simps)
      unfolding 
        Cons(1)[OF Cons(2) Cons(3) L2's]
      unfolding h h2
      by auto
  qed
  show ?thesis using assms(1)[symmetric] unfolding Leq apply(cases "MPoly_Type.degree p var < 3") apply simp_all
    apply(simp del : linearSubstitutionUni.simps quadraticSubUni.simps
        add: insertion_neg insertion_mult insertion_add insertion_pow insertion_sub insertion_four
        a_def[symmetric] b_def[symmetric] c_def[symmetric] a_def'[symmetric] b_def'[symmetric] c_def'[symmetric] eval_list_conj
        eval_list_conj_Uni ) using linear
    using quadratic_1 quadratic_2
    by smt
next
  case (Neq p)
  define a where "a = insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var 2)"
  have a_def' : "a = insertion (nth_default 0 (xs' @ 0 # xs)) (isolate_variable_sparse p var 2)" unfolding a_def
    using insertion_isovarspars_free[of "xs'  @x#xs" var x p 2 0] using assms by auto
  define b where "b = insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var (Suc 0))"
  have b_def' : "b = insertion (nth_default 0 (xs' @ 0 # xs)) (isolate_variable_sparse p var (Suc 0))" unfolding b_def
    using insertion_isovarspars_free[of "xs'@x#xs" var x p "(Suc 0)" 0] using assms by auto
  define c where "c = insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var 0)"
  have c_def' : "c = insertion (nth_default 0 (xs'@0 # xs)) (isolate_variable_sparse p var 0)" unfolding c_def
    using insertion_isovarspars_free[of "xs'@x#xs" var x p 0 0] using assms by auto
  have linear : "b\<noteq>0 \<Longrightarrow> (\<forall>f\<in>set L2.
         eval
          (substInfinitesimalLinear var 
            (-isolate_variable_sparse p var 0) (isolate_variable_sparse p var (Suc 0)) f)
          (xs' @ x # xs)) = (\<forall>l\<in>set L2'. evalUni (substInfinitesimalLinearUni b c l) x)"
    using assms(2) proof(induction L2 arbitrary : L2')
    case Nil
    then show ?case by auto
  next
    case (Cons At L2)
    have "\<exists>At'. convert_atom var At (xs' @ x # xs) = Some At'" proof(cases At)
      case (Less p)
      then show ?thesis using Cons(3) apply simp apply(cases "MPoly_Type.degree p var < 3") by simp_all
    next
      case (Eq p)
      then show ?thesis using Cons(3) apply simp apply(cases "MPoly_Type.degree p var < 3") by simp_all
    next
      case (Leq p)
      then show ?thesis using Cons(3) apply simp apply(cases "MPoly_Type.degree p var < 3") by auto
    next
      case (Neq p)
      then show ?thesis using Cons(3) apply simp apply(cases "MPoly_Type.degree p var < 3") by auto
    qed 
    then obtain At' where At' : "convert_atom var At (xs' @ x # xs) = Some At'" by auto
    have "\<exists>L2's. convert_atom_list var L2 (xs' @ x # xs) = Some L2's"
      using Cons(3) At'
      apply(cases "convert_atom_list var L2 (xs' @ x # xs)") by auto
    then obtain L2's where L2's : "convert_atom_list var L2 (xs' @ x # xs) = Some L2's" by auto
    have L2' : "L2' = At' # L2's"
      using Cons(3) At'
      by (simp_all add: L2's)
    have h : "eval
         (substInfinitesimalLinear var 
           (-isolate_variable_sparse p var 0) (isolate_variable_sparse p var (Suc 0)) At)
         (xs' @ x # xs) = evalUni (substInfinitesimalLinearUni b c At') x"
    proof(cases "convert_atom var At (xs' @ x # xs)")
      case None
      then show ?thesis using At' apply(cases At) by simp_all
    next
      case (Some a)
      have h1 : "var \<notin> vars (isolate_variable_sparse p var (Suc 0))"
        by (simp add: not_in_isovarspar) 
      have h2 : "var \<notin> vars (isolate_variable_sparse p var 0)"by (simp add: not_in_isovarspar) 
      have h :  "evalUni (substInfinitesimalLinearUni b c a) x =
    evalUni (substInfinitesimalLinearUni b c At') x"
      proof(cases At)
        case (Less p)
        then show ?thesis using At'[symmetric] Some[symmetric] apply(cases "MPoly_Type.degree p var < 3") by simp_all
      next
        case (Eq p)
        then show ?thesis using At'[symmetric] Some[symmetric] apply(cases "MPoly_Type.degree p var < 3") by simp_all
      next
        case (Leq x3)
        then show ?thesis using At' Some by auto 
      next
        case (Neq x4)
        then show ?thesis using At' Some by auto 
      qed
      show ?thesis unfolding convert_substInfinitesimalLinear[OF Some b_def[symmetric] c_def[symmetric] Cons(2) h1 h2 assms(3)]
        using h .
    qed
    show ?case unfolding L2' using h Cons(1)[OF Cons(2) L2's] by auto
  qed
  have quadratic_1 : "(a \<noteq> 0) \<Longrightarrow>
     (4 * a * c \<le> b\<^sup>2) \<Longrightarrow> (\<forall>f\<in>set L2.
          eval
           (substInfinitesimalQuadratic var
             (- isolate_variable_sparse p var (Suc 0)) 1
             ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
              4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)
             (2 * isolate_variable_sparse p var 2) f)
           (xs' @ x # xs)) = (\<forall>l\<in>set L2'.
          evalUni
           (substInfinitesimalQuadraticUni (- b) 1 (b\<^sup>2 - 4 * a * c) (2 * a) l)
           x)"
    using assms(2) proof(induction L2 arbitrary: L2')
    case Nil
    then show ?case by auto
  next
    case (Cons At L2)
    have "\<exists>At'. convert_atom var At (xs' @ x # xs) = Some At'" proof(cases At)
      case (Less p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by simp_all
    next
      case (Eq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by simp_all
    next
      case (Leq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by auto
    next
      case (Neq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by auto
    qed 
    then obtain At' where At' : "convert_atom var At (xs' @ x # xs) = Some At'" by auto
    have "\<exists>L2's. convert_atom_list var L2 (xs' @ x # xs) = Some L2's"
      using Cons(4) At'
      apply(cases "convert_atom_list var L2 (xs' @ x # xs)") by auto
    then obtain L2's where L2's : "convert_atom_list var L2 (xs' @ x # xs) = Some L2's" by auto
    have L2' : "L2' = At' # L2's"
      using Cons(4) At' apply(cases At) apply auto
      by (simp_all add: L2's)
    have h1 :  "var < length (xs' @ x # xs)" using assms by auto
    have h2 : "2*a \<noteq>0" using Cons by auto
    have h3 : "0\<le>b^2-4*a*c" using Cons(3) by auto
    have h4 : "var\<notin>vars ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
            4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)"
      by (metis add_uminus_conv_diff not_in_add not_in_isovarspar not_in_mult not_in_neg not_in_pow num_double numeral_times_numeral one_add_one power_0)
    have h5 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa])) (- isolate_variable_sparse p var (Suc 0)) = -b"
      unfolding insertion_neg b_def
      by (metis insertion_isovarspars_free list_update_id) 
    have h6 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa])) 1 = 1" by auto
    have h7 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa]))
        ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
         4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0) =
       b\<^sup>2 - 4 * a * c" apply(simp add: insertion_four insertion_mult insertion_sub insertion_pow b_def a_def c_def)
      by (metis insertion_isovarspars_free list_update_id)
    have "\<And>xa. insertion (nth_default 0 (xs' @xa # xs)) (2::real mpoly)  = (2::real)"
      by (metis MPoly_Type.insertion_one insertion_add one_add_one)  
    then have h8 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa])) (2 * isolate_variable_sparse p var 2) = 2 * a"
      unfolding insertion_mult a_def apply auto
      by (metis assms(3) insertion_lowerPoly1 list_update_length not_in_isovarspar)
    have h9 : "var\<notin>vars(- isolate_variable_sparse p var (Suc 0))"
      by (simp add: not_in_isovarspar not_in_neg)
    have h10 : "var\<notin>vars(1::real mpoly)"
      by (metis h9 not_in_pow power.simps(1))
    have h11 : "var\<notin>vars(2 * isolate_variable_sparse p var 2)"
      by (metis isovarspar_sum mult_2 not_in_isovarspar)
    have h :  "eval
      (substInfinitesimalQuadratic var (- isolate_variable_sparse p var (Suc 0)) 1
        ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
         4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)
        (2 * isolate_variable_sparse p var 2) At)
      (xs' @ x # xs) =  evalUni
      (substInfinitesimalQuadraticUni (- b) 1 (b\<^sup>2 - 4 * a * c) (2 * a) At') x"
    proof (cases "convert_atom var At (xs' @ x # xs)")
      case None
      then show ?thesis using At' apply(cases At) by auto
    next
      case (Some aT)
      have h1 : "insertion (nth_default 0 (xs' @ x # xs)) (- isolate_variable_sparse p var (Suc 0)) = (-b)" unfolding b_def insertion_neg by auto
      have h2 : "insertion (nth_default 0 (xs' @ x # xs)) 1 = 1" by auto
      have h3 : "insertion (nth_default 0 (xs' @ x # xs)) (((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
        4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)) = (b\<^sup>2 - 4 * a * c)"
        unfolding insertion_mult insertion_pow insertion_four insertion_neg insertion_sub a_def b_def c_def
        by auto
      have h4 : "insertion (nth_default 0 (xs' @ x # xs)) (2 * isolate_variable_sparse p var 2) = 2 * a"
        unfolding insertion_mult a_def
        by (metis insertion_add insertion_mult mult_2)
      have h5 : "2 * a \<noteq> 0" using Cons by auto
      have h6 : "0 \<le> b\<^sup>2 - 4 * a * c" using Cons by auto
      have h7 : "var\<notin>vars(- isolate_variable_sparse p var (Suc 0))"
        by (simp add: not_in_isovarspar not_in_neg)
      have h8 : "var\<notin>vars(1::real mpoly)"
        by (metis h9 not_in_pow power.simps(1))
      have h9 : "var \<notin> vars ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
             4 * isolate_variable_sparse p var 2 *
             isolate_variable_sparse p var 0)"
        by (metis add_uminus_conv_diff not_in_add not_in_isovarspar not_in_mult not_in_neg not_in_pow num_double numeral_times_numeral one_add_one power_0)
      have h10 : "var\<notin>vars(2 * isolate_variable_sparse p var 2)"
        by (metis isovarspar_sum mult_2 not_in_isovarspar)
      have h : "evalUni (substInfinitesimalQuadraticUni (- b) 1 (b\<^sup>2 - 4 * a * c) (2 * a) aT)
     x =
    evalUni (substInfinitesimalQuadraticUni (- b) 1 (b\<^sup>2 - 4 * a * c) (2 * a) At')
     x"proof(cases At)
        case (Less p)
        then show ?thesis using At'[symmetric] Some[symmetric] apply(cases "MPoly_Type.degree p var < 3") by auto
      next
        case (Eq p)
        then show ?thesis using At'[symmetric] Some[symmetric] apply(cases "MPoly_Type.degree p var < 3") by auto
      next
        case (Leq x3)
        then show ?thesis using At' using Some by auto
      next
        case (Neq x4)
        then show ?thesis using At' using Some by auto 
      qed
      show ?thesis unfolding convert_substInfinitesimalQuadratic[OF Some h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 assms(3)]
        using h .
    qed


    show ?case
      unfolding L2' apply(simp del : substInfinitesimalQuadratic.simps substInfinitesimalQuadraticUni.simps)
      unfolding 
        Cons(1)[OF Cons(2) Cons(3) L2's]
      unfolding h
      by auto
  qed
  have quadratic_2 : "(a \<noteq> 0) \<Longrightarrow>
     (4 * a * c \<le> b\<^sup>2) \<Longrightarrow> (\<forall>f\<in>set L2.
          eval
           (substInfinitesimalQuadratic var
             (- isolate_variable_sparse p var (Suc 0)) (- 1)
             ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
              4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)
             (2 * isolate_variable_sparse p var 2) f)
           (xs' @ x # xs)) = (\<forall>l\<in>set L2'.
          evalUni
           (substInfinitesimalQuadraticUni (- b) (- 1) (b\<^sup>2 - 4 * a * c) (2 * a)
             l)
           x)" 
    using assms(2) proof(induction L2 arbitrary: L2')
    case Nil
    then show ?case by auto
  next
    case (Cons At L2)
    have "\<exists>At'. convert_atom var At (xs' @ x # xs) = Some At'" proof(cases At)
      case (Less p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by simp_all
    next
      case (Eq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by simp_all
    next
      case (Leq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by auto
    next
      case (Neq p)
      then show ?thesis using Cons(4) apply simp apply(cases "MPoly_Type.degree p var < 3") by auto
    qed 
    then obtain At' where At' : "convert_atom var At (xs' @ x # xs) = Some At'" by auto
    have "\<exists>L2's. convert_atom_list var L2 (xs' @ x # xs) = Some L2's"
      using Cons(4) At'
      apply(cases "convert_atom_list var L2 (xs' @ x # xs)") by auto
    then obtain L2's where L2's : "convert_atom_list var L2 (xs' @ x # xs) = Some L2's" by auto
    have L2' : "L2' = At' # L2's"
      using Cons(4) At' apply(cases At) apply auto
      by (simp_all add: L2's)
    have h1 :  "var < length ((xs' @ x # xs))" using assms by auto
    have h2 : "2*a \<noteq>0" using Cons by auto
    have h3 : "0\<le>b^2-4*a*c" using Cons(3) by auto
    have h4 : "var\<notin>vars ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
            4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)"
      by (metis add_uminus_conv_diff not_in_add not_in_isovarspar not_in_mult not_in_neg not_in_pow num_double numeral_times_numeral one_add_one power_0)
    have h5 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa])) (- isolate_variable_sparse p var (Suc 0)) = -b"
      unfolding insertion_neg b_def
      by (metis insertion_isovarspars_free list_update_id) 
    have h6 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa])) (-1) = (-1)" unfolding insertion_neg by auto
    have h7 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa]))
        ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
         4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0) =
       b\<^sup>2 - 4 * a * c" apply(simp add: insertion_four insertion_mult insertion_sub insertion_pow b_def a_def c_def)
      by (metis insertion_isovarspars_free list_update_id)
    have "\<And>xa. insertion (nth_default 0 (xs' @ xa # xs)) (2::real mpoly)  = (2::real)"
      by (metis MPoly_Type.insertion_one insertion_add one_add_one)  
    then have h8 : "\<forall>xa. insertion (nth_default 0 ((xs' @ x # xs)[var := xa])) (2 * isolate_variable_sparse p var 2) = 2 * a"
      unfolding insertion_mult a_def apply auto
      by (metis assms(3) insertion_lowerPoly1 list_update_length not_in_isovarspar)
    have h9 : "var\<notin>vars(- isolate_variable_sparse p var (Suc 0))"
      by (simp add: not_in_isovarspar not_in_neg)
    have h10 : "var\<notin>vars(- 1::real mpoly)"
      by (metis h9 not_in_neg not_in_pow power.simps(1))
    have h11 : "var\<notin>vars(2 * isolate_variable_sparse p var 2)"
      by (metis isovarspar_sum mult_2 not_in_isovarspar)
    have h :  "eval
      (substInfinitesimalQuadratic var (- isolate_variable_sparse p var (Suc 0)) (-1)
        ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
         4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)
        (2 * isolate_variable_sparse p var 2) At)
      (xs' @ x # xs) =  evalUni
      (substInfinitesimalQuadraticUni (- b) (-1) (b\<^sup>2 - 4 * a * c) (2 * a) At') x"
    proof (cases "convert_atom var At (xs' @ x # xs)")
      case None
      then show ?thesis using At' apply(cases At) by auto
    next
      case (Some aT)
      have h1 : "insertion (nth_default 0 (xs' @ x # xs)) (- isolate_variable_sparse p var (Suc 0)) = (-b)" unfolding b_def insertion_neg by auto
      have h2 : "insertion (nth_default 0 (xs' @ x # xs)) (-1) = -1" unfolding insertion_neg by auto
      have h3 : "insertion (nth_default 0 (xs' @ x # xs)) (((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
        4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)) = (b\<^sup>2 - 4 * a * c)"
        unfolding insertion_mult insertion_pow insertion_four insertion_neg insertion_sub a_def b_def c_def
        by auto
      have h4 : "insertion (nth_default 0 (xs' @ x # xs)) (2 * isolate_variable_sparse p var 2) = 2 * a"
        unfolding insertion_mult a_def
        by (metis insertion_add insertion_mult mult_2)
      have h5 : "2 * a \<noteq> 0" using Cons by auto
      have h6 : "0 \<le> b\<^sup>2 - 4 * a * c" using Cons by auto
      have h7 : "var\<notin>vars(- isolate_variable_sparse p var (Suc 0))"
        by (simp add: not_in_isovarspar not_in_neg)
      have h8 : "var\<notin>vars(- 1::real mpoly)"
        by (simp add: h10 not_in_neg)
      have h9 : "var \<notin> vars ((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
             4 * isolate_variable_sparse p var 2 *
             isolate_variable_sparse p var 0)"
        by (metis add_uminus_conv_diff not_in_add not_in_isovarspar not_in_mult not_in_neg not_in_pow num_double numeral_times_numeral one_add_one power_0)
      have h10 : "var\<notin>vars(2 * isolate_variable_sparse p var 2)"
        by (metis isovarspar_sum mult_2 not_in_isovarspar)
      have h : "evalUni (substInfinitesimalQuadraticUni (- b) (-1) (b\<^sup>2 - 4 * a * c) (2 * a) aT)
     x =
    evalUni (substInfinitesimalQuadraticUni (- b) (-1) (b\<^sup>2 - 4 * a * c) (2 * a) At')
     x"proof(cases At)
        case (Less p)
        then show ?thesis using At'[symmetric] Some[symmetric] apply(cases "MPoly_Type.degree p var < 3") by auto
      next
        case (Eq p)
        then show ?thesis using At'[symmetric] Some[symmetric] apply(cases "MPoly_Type.degree p var < 3") by auto
      next
        case (Leq x3)
        then show ?thesis using At'
          using Some option.inject by auto 
      next
        case (Neq x4)
        then show ?thesis using At'
          using Some by auto 
      qed
      show ?thesis unfolding convert_substInfinitesimalQuadratic[OF Some h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 assms(3)]
        using h .
    qed


    show ?case
      unfolding L2' apply(simp del : substInfinitesimalQuadratic.simps substInfinitesimalQuadraticUni.simps)
      unfolding 
        Cons(1)[OF Cons(2) Cons(3) L2's]
      unfolding h
      by auto
  qed

  show ?thesis using assms(1)[symmetric] unfolding Neq apply(cases "MPoly_Type.degree p var < 3") apply simp_all
    apply(simp del : substInfinitesimalLinear.simps substInfinitesimalLinearUni.simps substInfinitesimalQuadratic.simps substInfinitesimalQuadraticUni.simps
        add: insertion_neg insertion_mult insertion_add insertion_pow insertion_sub insertion_four
        a_def[symmetric] b_def[symmetric] c_def[symmetric] a_def'[symmetric] b_def'[symmetric] c_def'[symmetric] eval_list_conj
        eval_list_conj_Uni
        ) using linear quadratic_1 quadratic_2 by smt
qed

lemma convert_list : 
  assumes "convert_atom_list var L (xs' @ x # xs) = Some L'"
  assumes "l\<in>set(L)"
  shows "\<exists>l'\<in> set L'. convert_atom var l (xs' @ x # xs) = Some l'"
  using assms
proof(induction L arbitrary : L')
  case Nil
  then show ?case by auto
next
  case (Cons At L)
  then show ?case proof(cases At)
    case (Less p)
    then show ?thesis  using Cons(2)[symmetric] Cons(1) Cons(3) unfolding Less apply simp apply(cases "MPoly_Type.degree p var < 3") apply simp_all
      apply(cases "convert_atom_list var L (xs' @ x # xs)") apply simp_all apply(cases "l = Less p") by simp_all
  next
    case (Eq p)
    show ?thesis  using Cons(2)[symmetric] Cons(1) Cons(3) unfolding Eq apply simp apply(cases "MPoly_Type.degree p var < 3") apply simp_all
      apply(cases "convert_atom_list var L (xs' @ x # xs)") apply simp_all apply(cases "l = Eq p") by simp_all
  next
    case (Leq p)
    then show ?thesis using Cons(2)[symmetric] Cons(1) Cons(3) unfolding Leq apply simp apply(cases "MPoly_Type.degree p var < 3") apply simp_all
      apply(cases "convert_atom_list var L (xs' @ x # xs)") apply simp_all apply(cases "l = Leq p") by simp_all
  next
    case (Neq p)
    then show ?thesis using Cons(2)[symmetric] Cons(1) Cons(3) unfolding Neq apply simp apply(cases "MPoly_Type.degree p var < 3") apply simp_all
      apply(cases "convert_atom_list var L (xs' @ x # xs)") apply simp_all apply(cases "l = Neq p") by simp_all
  qed
qed

lemma convert_list2 : 
  assumes "convert_atom_list var L (xs' @ x # xs) = Some L'"
  assumes "l'\<in>set(L')"
  shows "\<exists>l\<in> set L. convert_atom var l (xs' @ x # xs) = Some l'"
  using assms
proof(induction L arbitrary : L')
  case Nil
  then show ?case by auto
next
  case (Cons At L)
  then show ?case proof(cases At)
    case (Less p)
    then show ?thesis  using Cons(2)[symmetric] Cons(1) Cons(3) unfolding Less apply simp apply(cases "MPoly_Type.degree p var < 3") apply simp_all
      apply(cases "convert_atom_list var L (xs' @ x # xs)") apply simp_all
      by blast
  next
    case (Eq p)
    show ?thesis  using Cons(2)[symmetric] Cons(1) Cons(3) unfolding Eq apply simp apply(cases "MPoly_Type.degree p var < 3") apply simp_all
      apply(cases "convert_atom_list var L (xs' @ x # xs)") apply simp_all by blast
  next
    case (Leq p)
    then show ?thesis  using Cons(2)[symmetric] Cons(1) Cons(3) unfolding Leq apply simp apply(cases "MPoly_Type.degree p var < 3") apply simp_all
      apply(cases "convert_atom_list var L (xs' @ x # xs)") apply simp_all by blast
  next
    case (Neq p)
    then show ?thesis  using Cons(2)[symmetric] Cons(1) Cons(3) unfolding Neq apply simp apply(cases "MPoly_Type.degree p var < 3") apply simp_all
      apply(cases "convert_atom_list var L (xs' @ x # xs)") apply simp_all by blast
  qed
qed

lemma elimVar_atom_convert : 
  assumes "convert_atom_list var L (xs' @ x # xs) = Some L'"
  assumes "convert_atom_list var L2 (xs' @ x # xs) = Some L2'"
  assumes "length xs' = var"
  shows "(\<exists>f\<in>set L. eval (elimVar var L2 [] f) (xs' @ x # xs))
         = (\<exists>f\<in>set L'. evalUni (elimVarUni_atom L2' f) x)"
proof safe
  fix f
  assume h : "f \<in> set L"
    "eval (elimVar var L2 [] f) (xs' @ x # xs)"
  have "\<exists>f'\<in>set L'. convert_atom var f (xs' @ x # xs) = Some f'"
    using convert_list h assms by auto
  then obtain f' where f' : "f'\<in>set L'" "convert_atom var f (xs' @ x # xs) = Some f'" by metis
  show "\<exists>f\<in>set L'. evalUni (elimVarUni_atom L2' f) x"
    apply(rule bexI[where x=f']) using f' elimVar_atom_single[OF f'(2) assms(2) assms(3)] h by auto
next
  fix f'
  assume h : "f' \<in> set L'"
    "evalUni (elimVarUni_atom L2' f') x"
  have "\<exists>f\<in>set L. convert_atom var f (xs' @ x # xs) = Some f'" using convert_list2 h assms by auto
  then obtain f where f : "f\<in>set L" "convert_atom var f (xs' @ x # xs) = Some f'" by metis
  show "\<exists>f\<in>set L. eval (elimVar var L2 [] f) (xs' @ x # xs)"
    apply(rule bexI[where x=f]) using f elimVar_atom_single[OF f(2) assms(2) assms(3)] h by auto
qed


lemma eval_convert : 
  assumes "convert_atom_list var L (xs' @ x # xs) = Some L'"
  assumes "length xs' = var"
  shows "(\<forall>f\<in>set L. aEval f (xs' @ x # xs)) = (\<forall>f\<in>set L'. aEvalUni f x)"
  using assms
proof(induction L arbitrary : L')
  case Nil
  then show ?case by auto
next
  case (Cons a L)
  then show ?case proof(cases a)
    case (Less p)
    then show ?thesis using Cons(2)[symmetric] Cons(1) Cons(3) unfolding Less apply(cases " MPoly_Type.degree p var < 3")
      apply simp_all apply(cases "convert_atom_list var L (xs' @ x # xs)") apply simp_all
      by (simp add: poly_to_univar) 
  next
    case (Eq p)
    then show ?thesis using Cons(2)[symmetric] Cons(1) Cons(3) unfolding Eq apply(cases " MPoly_Type.degree p var < 3")
      apply simp_all apply(cases "convert_atom_list var L (xs' @ x # xs)") apply simp_all
      by (simp add: poly_to_univar) 
  next
    case (Leq p)
    show ?thesis  using Cons(2)[symmetric] Cons(1) Cons(3) unfolding Leq apply(cases " MPoly_Type.degree p var < 3") 
      apply simp_all apply(cases "convert_atom_list var L (xs' @ x # xs)") apply simp_all
      by (simp add: poly_to_univar) 
  next
    case (Neq p)
    show ?thesis  using Cons(2)[symmetric] Cons(1) Cons(3) unfolding Neq apply(cases " MPoly_Type.degree p var < 3") 
      apply simp_all apply(cases "convert_atom_list var L (xs' @ x # xs)") apply simp_all
      by (simp add: poly_to_univar) 
  qed
qed
lemma all_degree_2_convert : 
  assumes "all_degree_2 var L"
  shows "\<exists>L'. convert_atom_list var L xs = Some L'"
  using assms
proof(induction L)
  case Nil
  then show ?case by auto
next
  case (Cons a L)
  then show ?case proof(cases a)
    case (Less p)
    show ?thesis using Cons unfolding Less all_degree_2.simps convert_atom_list.simps convert_atom.simps
      using degree_convert_eq[of var p xs] by auto
  next
    case (Eq p)
    then show ?thesis using Cons unfolding Eq all_degree_2.simps convert_atom_list.simps convert_atom.simps
      using degree_convert_eq[of var p xs] by auto
  next
    case (Leq x3)
    then show ?thesis using Cons by auto
  next
    case (Neq x4)
    then show ?thesis using Cons by auto
  qed
qed
lemma gen_qe_eval :
  assumes hlength : "length xs = var"
  shows "(\<exists>x. (eval (list_conj ((map Atom L) @ F)) (xs @ (x#\<Gamma>)))) = (\<exists>x.(eval (gen_qe var L F) (xs @ (x#\<Gamma>))))"
proof(cases "luckyFind var L []")
  case None
  then have notLucky : "luckyFind var L [] = None" by auto 
  then show ?thesis proof(cases F)
    case Nil
    then show ?thesis proof(cases "all_degree_2 var L")
      case True
      then have "\<And>x.\<exists>L'. convert_atom_list var L (xs@x#\<Gamma>) = Some L'" using all_degree_2_convert[of var L "xs@_#\<Gamma>"] by auto
      then obtain L' where L' : "convert_atom_list var L (xs@x#\<Gamma>) = Some L'" by metis
      then have L' : "\<And>x. convert_atom_list var L (xs@x#\<Gamma>) = Some L'"
        by (metis convert_atom_list_change hlength)
      show ?thesis
        unfolding Nil apply (simp add:eval_list_conj eval_list_disj True del:luckyFind.simps) unfolding notLucky apply (simp add:eval_list_conj eval_list_disj)
        using negInf_convert[OF L' assms] elimVar_atom_convert[OF L' L' assms] eval_convert[OF L' assms]
        using eval_generalVS''[of L'] unfolding eval_list_conj_Uni generalVS_DNF.simps eval_list_conj_Uni eval_list_disj_Uni eval_append eval_map eval_map_all
          evalUni.simps 

        by auto
    next
      case False
      then show ?thesis using notLucky unfolding Nil  False apply simp
        by (metis append_Nil2 hlength notLucky option.simps(4) qe_eq_repeat.simps qe_eq_repeat_eval) 
    qed
  next
    case (Cons a list)
    show ?thesis
      apply(simp add:Cons del:qe_eq_repeat.simps)
      apply(rule qe_eq_repeat_eval[of xs var L "a # list" \<Gamma>])
      using assms .
  qed
next
  case (Some a)
  then show ?thesis
    using luckyFind_eval[OF Some assms] apply(cases F) apply simp 
    apply(simp add:Cons del:qe_eq_repeat.simps)
    using qe_eq_repeat_eval[of xs var L _ \<Gamma>]
    using assms  by auto
qed


lemma freeIn_elimVar : "freeIn var (elimVar var L F A)"
proof(cases A)
  case (Less p)
  have two: "2 = Suc(Suc 0)" by auto
  have notIn4: "var \<notin> vars (4::real mpoly)"
    by (metis isolate_var_one not_in_add not_in_isovarspar numeral_plus_numeral one_add_one semiring_norm(2) semiring_norm(6)) 
  show ?thesis using Less apply auto
    using not_in_isovarspar apply force+
    apply (rule freeIn_list_conj)
    apply auto
    defer defer
    using not_in_isovarspar apply force+
    using not_in_sub[OF not_in_mult[of var 4, OF _ not_in_mult[of var "isolate_variable_sparse p var 2" "isolate_variable_sparse p var 0"]], of "(isolate_variable_sparse p var (Suc 0))\<^sup>2"]
    apply (simp add:not_in_isovarspar two)
    using not_in_mult[of var "isolate_variable_sparse p var (Suc 0)" "isolate_variable_sparse p var (Suc 0)"]
    apply (simp add:not_in_isovarspar notIn4)
    apply (simp add: ideal.scale_scale)
    apply(rule freeIn_list_conj)
    apply auto
    defer defer
    apply(rule freeIn_list_conj)
    apply auto
    apply(rule freeIn_substInfinitesimalQuadratic) apply auto
    using not_in_isovarspar not_in_neg apply blast
    apply (metis not_in_isovarspar not_in_neg not_in_pow power_0)
    using notIn4 not_in_isovarspar not_in_mult not_in_pow not_in_sub apply auto[1]
    apply (metis isovarspar_sum mult_2 not_in_isovarspar)
    using freeIn_substInfinitesimalQuadratic_fm[of var "(- isolate_variable_sparse p var (Suc 0))" "-1" "((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
                      4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)" "(2 * isolate_variable_sparse p var 2)"] apply auto[1]
    apply (metis (no_types, lifting) mult_2 notIn4 not_in_add not_in_isovarspar not_in_mult not_in_neg not_in_pow not_in_sub power_0)
    apply(rule freeIn_substInfinitesimalLinear)
    apply (meson not_in_isovarspar not_in_neg)
    apply (simp add: not_in_isovarspar)
    using freeIn_substInfinitesimalLinear_fm
    using not_in_isovarspar not_in_neg apply force
    apply (metis (no_types, lifting) \<open>\<lbrakk>var \<notin> vars 4; var \<notin> vars (isolate_variable_sparse p var 2); var \<notin> vars (isolate_variable_sparse p var 0); var \<notin> vars ((isolate_variable_sparse p var (Suc 0))\<^sup>2)\<rbrakk> \<Longrightarrow> var \<notin> vars (4 * (isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0) - (isolate_variable_sparse p var (Suc 0))\<^sup>2)\<close> freeIn_substInfinitesimalQuadratic minus_diff_eq mult.assoc mult_2 notIn4 not_in_add not_in_isovarspar not_in_neg not_in_pow power_0)
    using freeIn_substInfinitesimalQuadratic_fm[of var "(- isolate_variable_sparse p var (Suc 0))" 1 "((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
                      4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)" "(2 * isolate_variable_sparse p var 2)"]
    apply auto
    by (metis (no_types, lifting) \<open>\<lbrakk>var \<notin> vars 4; var \<notin> vars (isolate_variable_sparse p var 2); var \<notin> vars (isolate_variable_sparse p var 0); var \<notin> vars ((isolate_variable_sparse p var (Suc 0))\<^sup>2)\<rbrakk> \<Longrightarrow> var \<notin> vars (4 * (isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0) - (isolate_variable_sparse p var (Suc 0))\<^sup>2)\<close> ideal.scale_scale minus_diff_eq mult_2 notIn4 not_in_add not_in_isovarspar not_in_neg not_in_pow power_0)
next
  case (Eq p)
  then show ?thesis using freeIn_elimVar_eq by auto
next
  case (Leq p)
  then show ?thesis using freeIn_elimVar_eq by auto
next
  case (Neq p)
  have two: "2 = Suc(Suc 0)" by auto
  have notIn4: "var \<notin> vars (4::real mpoly)"
    by (metis isolate_var_one not_in_add not_in_isovarspar numeral_plus_numeral one_add_one semiring_norm(2) semiring_norm(6)) 
  show ?thesis using Neq apply auto
    using not_in_isovarspar apply force+
    apply (rule freeIn_list_conj)
    apply auto
    defer defer
    using not_in_isovarspar apply force+
    using not_in_sub[OF not_in_mult[of var 4, OF _ not_in_mult[of var "isolate_variable_sparse p var 2" "isolate_variable_sparse p var 0"]], of "(isolate_variable_sparse p var (Suc 0))\<^sup>2"]
    apply (simp add:not_in_isovarspar two)
    using not_in_mult[of var "isolate_variable_sparse p var (Suc 0)" "isolate_variable_sparse p var (Suc 0)"]
    apply (simp add:not_in_isovarspar notIn4)
    apply (simp add: ideal.scale_scale)
    apply(rule freeIn_list_conj)
    apply auto
    defer defer
    apply(rule freeIn_list_conj)
    apply auto
    apply(rule freeIn_substInfinitesimalQuadratic) apply auto
    using not_in_isovarspar not_in_neg apply blast
    apply (metis not_in_isovarspar not_in_neg not_in_pow power_0)
    using notIn4 not_in_isovarspar not_in_mult not_in_pow not_in_sub apply auto[1]
    apply (metis isovarspar_sum mult_2 not_in_isovarspar)
    using freeIn_substInfinitesimalQuadratic_fm[of var "(- isolate_variable_sparse p var (Suc 0))" "-1" "((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
                      4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)" "(2 * isolate_variable_sparse p var 2)"] apply auto[1]
    apply (metis (no_types, lifting) mult_2 notIn4 not_in_add not_in_isovarspar not_in_mult not_in_neg not_in_pow not_in_sub power_0)
    apply(rule freeIn_substInfinitesimalLinear)
    apply (meson not_in_isovarspar not_in_neg)
    apply (simp add: not_in_isovarspar)
    using freeIn_substInfinitesimalLinear_fm
    using not_in_isovarspar not_in_neg apply force
    apply (metis (no_types, lifting) \<open>\<lbrakk>var \<notin> vars 4; var \<notin> vars (isolate_variable_sparse p var 2); var \<notin> vars (isolate_variable_sparse p var 0); var \<notin> vars ((isolate_variable_sparse p var (Suc 0))\<^sup>2)\<rbrakk> \<Longrightarrow> var \<notin> vars (4 * (isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0) - (isolate_variable_sparse p var (Suc 0))\<^sup>2)\<close> freeIn_substInfinitesimalQuadratic minus_diff_eq mult.assoc mult_2 notIn4 not_in_add not_in_isovarspar not_in_neg not_in_pow power_0)
    using freeIn_substInfinitesimalQuadratic_fm[of var "(- isolate_variable_sparse p var (Suc 0))" 1 "((isolate_variable_sparse p var (Suc 0))\<^sup>2 -
                      4 * isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0)" "(2 * isolate_variable_sparse p var 2)"]
    apply auto
    by (metis (no_types, lifting) \<open>\<lbrakk>var \<notin> vars 4; var \<notin> vars (isolate_variable_sparse p var 2); var \<notin> vars (isolate_variable_sparse p var 0); var \<notin> vars ((isolate_variable_sparse p var (Suc 0))\<^sup>2)\<rbrakk> \<Longrightarrow> var \<notin> vars (4 * (isolate_variable_sparse p var 2 * isolate_variable_sparse p var 0) - (isolate_variable_sparse p var (Suc 0))\<^sup>2)\<close> ideal.scale_scale minus_diff_eq mult_2 notIn4 not_in_add not_in_isovarspar not_in_neg not_in_pow power_0)
qed

lemma freeInDisj: "freeIn var (list_disj (list_conj (map (substNegInfinity var) L) # map (elimVar var L []) L))"
  apply(rule freeIn_list_disj)
  apply(auto)
  apply(rule freeIn_list_conj)
  apply simp

  using freeIn_substNegInfinity[of var]
  apply simp
  using freeIn_elimVar
  by simp

lemma gen_qe_eval' :
  assumes "all_degree_2 var L"
  assumes "length xs' = var"
  shows "(\<exists>x. (eval (list_conj (map Atom L)) (xs'@x#\<Gamma>))) = (\<forall>x.(eval (gen_qe var L []) (xs'@x#\<Gamma>)))"
    "freeIn var (gen_qe var L [])"
proof-
  have h : "(\<exists>x. (eval (list_conj (map Atom L)) (xs'@x#\<Gamma>))) = (\<exists>x. eval (gen_qe var L []) (xs'@x # \<Gamma>))"
    using gen_qe_eval[OF assms(2), of L "[]" \<Gamma>] unfolding List.append.left_neutral  by auto
  show "(\<exists>x. (eval (list_conj (map Atom L)) (xs'@x#\<Gamma>))) = (\<forall>x.(eval (gen_qe var L []) (xs'@x#\<Gamma>)))"
    unfolding h
    apply (simp add:assms)
    apply(cases "find_lucky_eq var L")
    apply simp using freeInDisj[of var L]
    using var_not_in_eval3[OF _ assms(2)] apply blast
    subgoal for a
      using freeIn_elimVar_eq[of var L "[]" a]
      apply(simp del:elimVar.simps)
      using var_not_in_eval3[OF _ assms(2)] by blast
    done
next
  show "freeIn var (gen_qe var L []) "
    apply(simp add:assms)
    apply(cases "find_lucky_eq var L") apply (simp add:freeInDisj)
    subgoal for a
      using freeIn_elimVar_eq[of var L "[]" a]
      by(simp del:elimVar.simps)
    done
qed



lemma gen_qe_eval'' :
  assumes "all_degree_2 var L"
  assumes "length xs' = var"
  shows "(\<exists>x. (eval (list_conj (map Atom L)) (xs'@x#\<Gamma>))) = (\<forall>x.(eval (list_disj
                          (list_conj (map (substNegInfinity var) L) # map (elimVar var L []) L)) (xs'@x#\<Gamma>)))"
proof(cases "convert_atom_list var L (xs'@x#\<Gamma>)")
  case None
  then show ?thesis using all_degree_2_convert[OF assms(1), of "(xs' @ x # \<Gamma>)"] by auto
next
  case (Some a)
  then have Some : "\<And>x. convert_atom_list var L (xs'@x#\<Gamma>) = Some a"  using convert_atom_list_change[OF assms(2), of L x \<Gamma>]
    by fastforce

  show ?thesis
    apply (simp add: eval_list_conj eval_list_disj)
    using negInf_convert[OF Some assms(2)] elimVar_atom_convert[OF Some Some assms(2)] eval_convert[OF Some assms(2)]
    using eval_generalVS''[of a] unfolding eval_list_conj_Uni generalVS_DNF.simps eval_list_conj_Uni eval_list_disj_Uni eval_append eval_map eval_map_all
      evalUni.simps 
    by auto
qed

end