section "More on Substitutions"

(*
  Originally for stuff from Term_Subst.ML

  Now has little do to with it and contains stuff about various substitutions in general
  Problem: Inconsistent naming
*)

theory Term_Subst
  imports Term
begin

fun subst_typ :: "((variable \<times> sort) \<times> typ) list \<Rightarrow> typ \<Rightarrow> typ" where
  "subst_typ insts (Ty a Ts) = 
    Ty a (map (subst_typ insts) Ts)"
| "subst_typ insts (Tv idn S) = the_default (Tv idn S) 
    (lookup (\<lambda>x . x = (idn, S)) insts)"

lemma subst_typ_nil[simp]: "subst_typ [] T = T" 
  by (induction T) (auto simp add: map_idI)
 
lemma subst_typ_irrelevant_order:
  assumes "distinct (map fst pairs)" and "distinct (map fst pairs')" and "set pairs = set pairs'"
shows "subst_typ pairs T = subst_typ pairs' T"
  using assms
proof(induction T)
  case (Ty n Ts)
  then show ?case by (induction Ts) auto
next
  case (Tv idn S)
  then show ?case using lookup_eq_order_irrelevant by (metis subst_typ.simps(2))
qed

(* Core lemma, Isabelle/Pure's instantiateT_same function can simulate abstract type subtitutions 
  in types *)
lemma subst_typ_simulates_tsubstT_gen': "distinct l \<Longrightarrow> tvsT T \<subseteq> set l 
  \<Longrightarrow> tsubstT T \<rho> = subst_typ (map (\<lambda>(x,y).((x,y), \<rho> x y)) l) T"
proof(induction T arbitrary: l)
  case (Ty n Ts)
  then show ?case by (induction Ts) auto
next
  case (Tv idn S)
  hence d: "distinct (map fst (map (\<lambda>(x,y).((x,y), \<rho> x y)) l))" 
    by (simp add: case_prod_beta map_idI)
  hence el: "((idn,S), \<rho> idn S) \<in> set (map (\<lambda>a. case a of (x, y) \<Rightarrow> ((x, y), \<rho> x y)) l)" 
    using Tv by auto
  show ?case using iffD1[OF lookup_present_eq_key, OF _ el]  Tv.prems d by auto
qed

lemma subst_typ_simulates_tsubstT_gen: "tsubstT T \<rho> 
  = subst_typ (map (\<lambda>(x,y).((x,y), \<rho> x y)) (SOME l . distinct l \<and> tvsT T \<subseteq> set l)) T"
proof(rule someI2_ex)
  show "\<exists>a. distinct a \<and> tvsT T \<subseteq> set a"
    using finite_tvsT finite_distinct_list
    by (metis order_refl)
next
  fix l assume l: "distinct l \<and> tvsT T \<subseteq> set l"
  then show "tsubstT T \<rho> = subst_typ (map (\<lambda>a. case a of (x, y) \<Rightarrow> ((x, y), \<rho> x y)) l) T"
    using subst_typ_simulates_tsubstT_gen' by blast
qed

corollary subst_typ_simulates_tsubstT: "tsubstT T \<rho> 
  = subst_typ (map (\<lambda>(x,y).((x,y), \<rho> x y)) (SOME l . distinct l \<and> set l = tvsT T)) T"
  apply (rule someI2_ex) 
  using finite_tvsT finite_distinct_list apply metis
  using subst_typ_simulates_tsubstT_gen' apply simp
  done

(* Other direction, can construct a abstract substitution for one performed by instantiateT_same *)
lemma tsubstT_simulates_subst_typ: "subst_typ insts T
  = tsubstT T (\<lambda>idn S . the_default (Tv idn S) (lookup (\<lambda>x. x=(idn, S)) insts))"
  by (induction T) auto

(* Somewhat janky version of "composition" for subst_typ *)
lemma subst_typ_comp: 
  "subst_typ inst1 (subst_typ inst2 T) = subst_typ (map (apsnd (subst_typ inst1)) inst2 @ inst1) T"
proof (induction inst2 T arbitrary: inst1 rule: subst_typ.induct)
  case (1 insts a Ts)
  then show ?case
    by auto
next
  case (2 insts idn S)
  then show ?case 
    by (induction insts) auto
qed
(* To make insts distinct again *)
lemma subst_typ_AList_clearjunk: "subst_typ insts T = subst_typ (AList.clearjunk insts) T"
proof (induction T)
  case (Ty n Ts)
  then show ?case 
    by auto
next
  case (Tv n S)
  then show ?case
  proof(induction insts)
    case Nil
    then show ?case
      by auto
  next
    case (Cons inst insts)
    then show ?case 
      by simp (metis clearjunk.simps(2) lookup_AList_clearjunk)
  qed
qed
  
fun subst_type_term :: "((variable \<times> sort) \<times> typ) list \<Rightarrow> 
    ((variable \<times> typ) \<times> term) list \<Rightarrow> term \<Rightarrow> term" where
  "subst_type_term instT insts (Ct c T) = Ct c (subst_typ instT T)"
| "subst_type_term instT insts (Fv idn T) = (let T' = subst_typ instT T in
    the_default (Fv idn T') (lookup (\<lambda>x. x = (idn, T')) insts))"
| "subst_type_term _ _ (Bv n) = Bv n"
| "subst_type_term instT insts (Abs T t) = Abs (subst_typ instT T) (subst_type_term instT insts t)"
| "subst_type_term instT insts (t $ u) = subst_type_term instT insts t $ subst_type_term instT insts u"

lemma subst_type_term_empty_no_change[simp]: "subst_type_term [] [] t = t"
  by (induction t) (simp_all add:)

lemma subst_type_term_irrelevant_order:
  assumes instT_assms: "distinct (map fst instT)" "distinct (map fst instT')" "set instT = set instT'"
  assumes insts_assms: "distinct (map fst insts)" "distinct (map fst insts')" "set insts = set insts'"
shows "subst_type_term instT insts t = subst_type_term instT' insts' t"
  using assms
proof(induction t)
  case (Fv idn T)
  then show ?case 
    apply (simp add: Let_def subst_typ_irrelevant_order[OF Fv.prems(1-3)])
    using lookup_eq_order_irrelevant by (metis Fv.prems(4) Fv.prems(5) insts_assms)
next
  case (Abs T t)
  then show ?case using subst_typ_irrelevant_order[OF instT_assms] by simp
qed (simp_all add: subst_typ_irrelevant_order[OF instT_assms])

(* Core lemma, Isabelle/Pure's instantiate_same function can simulate abstract 
  term/type subtitutions in terms 

  The tsubst should be no problem, can be rewritten to subst_type using previous simulation lemma
*)
lemma subst_type_term_simulates_subst_tsubst_gen':
  assumes lty_assms: "distinct lty" "tvs t \<subseteq> set lty"
  assumes lt_assms: "distinct lt" "fv (tsubst t \<rho>ty) \<subseteq> set lt"
  shows "subst (tsubst t \<rho>ty) \<rho>t 
    = subst_type_term (map (\<lambda>(x,y).((x,y), \<rho>ty x y)) lty) (map (\<lambda>(x,y).((x,y), \<rho>t x y)) lt) t"
proof-
  let ?lty = "map (\<lambda>(x,y).((x,y), \<rho>ty x y)) lty"

  have p1ty: "distinct (map fst ?lty)" using lty_assms
    by (simp add: case_prod_beta map_idI)

  let ?lt = "map (\<lambda>(x,y).((x,y), \<rho>t x y)) lt"

  have p1t: "distinct (map fst ?lt)" using lt_assms
    by (simp add: case_prod_beta map_idI)

  show ?thesis using assms
  proof(induction t arbitrary: lty lt)
    case (Fv idn T)
  
    let ?T = "tsubstT T \<rho>ty"  
    have el: "((idn, ?T), \<rho>t idn ?T) \<in> set (map (\<lambda>(x,y).((x,y), \<rho>t x y)) lt)" 
      using Fv by auto
    have d: "distinct (map fst (map (\<lambda>(x,y).((x,y), \<rho>t x y)) lt))" 
      using Fv by (simp add: case_prod_beta map_idI)
    show ?case using  Fv.prems d 
      by (auto simp add: iffD1[OF lookup_present_eq_key, OF d el] 
          subst_typ_simulates_tsubstT_gen'[symmetric] Let_def)
  qed (simp_all add: subst_typ_simulates_tsubstT_gen')
qed

corollary subst_type_term_simulates_subst_tsubst: "subst (tsubst t \<rho>ty) \<rho>t 
    = subst_type_term (map (\<lambda>(x,y).((x,y), \<rho>ty x y)) (SOME lty . distinct lty \<and> tvs t = set lty)) 
      (map (\<lambda>(x,y).((x,y), \<rho>t x y)) (SOME lt . distinct lt \<and> fv (tsubst t \<rho>ty) = set lt)) t"
  apply (rule someI2_ex)
  using finite_fv finite_distinct_list apply metis
  apply (rule someI2_ex) 
  using finite_tvs finite_distinct_list apply metis
  using subst_type_term_simulates_subst_tsubst_gen' by simp

abbreviation "subst_typ' pairs t \<equiv> map_types (subst_typ pairs) t"

lemma subst_typ'_nil[simp]: "subst_typ' [] A = A" 
  by (induction A) (auto simp add:)

lemma subst_typ'_simulates_tsubst_gen': "distinct pairs \<Longrightarrow> tvs t \<subseteq> set pairs
  \<Longrightarrow> tsubst t \<rho> = subst_typ' (map (\<lambda>(x,y).((x,y), \<rho> x y)) pairs) t"
  by (induction t arbitrary: pairs \<rho>) 
    (auto simp add: subst_typ_simulates_tsubstT_gen')

lemma subst_typ'_simulates_tsubst_gen: "tsubst t \<rho> 
  = subst_typ' (map (\<lambda>(x,y).((x,y), \<rho> x y)) (SOME l . distinct l \<and> tvs t \<subseteq> set l)) t"
proof(rule someI2_ex)
  show "\<exists>a. distinct a \<and> tvs t \<subseteq> set a"
    using finite_tvs finite_distinct_list
    by (metis order_refl)
next
  fix l assume l: "distinct l \<and> tvs t \<subseteq> set l"
  
  then show "tsubst t \<rho> = subst_typ' (map (\<lambda>a. case a of (x, y) \<Rightarrow> ((x, y), \<rho> x y)) l) t"
    using subst_typ'_simulates_tsubst_gen' by blast
qed

lemma tsubst_simulates_subst_typ': "subst_typ' insts T
  = tsubst T (\<lambda>idn S . the_default (Tv idn S) (lookup (\<lambda>x. x=(idn, S)) insts))"
  by (induction T) (auto simp add: tsubstT_simulates_subst_typ)

(* 
  Naming! 
*)
lemma subst_type_add_degenerate_instance: 
  "(idx,s) \<notin> set (map fst insts) \<Longrightarrow> subst_typ insts T = subst_typ (((idx,s), Tv idx s)#insts) T"
  by (induction T) (auto simp add: lookup_eq_key_not_present)

lemma subst_typ'_add_degenerate_instance: 
  "(idx,s) \<notin> set (map fst insts) \<Longrightarrow> subst_typ' insts t = subst_typ' (((idx,s), Tv idx s)#insts) t"
  by (induction t) (auto simp add: subst_type_add_degenerate_instance)

(* Again, janky composition *)
lemma subst_typ'_comp: 
  "subst_typ' inst1 (subst_typ' inst2 t) = subst_typ' (map (apsnd (subst_typ inst1)) inst2 @ inst1) t"
  by (induction t) (use subst_typ_comp in auto)

(* To make insts distinct again *)
lemma subst_typ'_AList_clearjunk: "subst_typ' insts t = subst_typ' (AList.clearjunk insts) t"
  by (induction t) (use subst_typ_AList_clearjunk in auto)

fun subst_term :: "((variable * typ) * term) list \<Rightarrow> term \<Rightarrow> term" where
  "subst_term insts (Ct c T) = Ct c T"
| "subst_term insts (Fv idn T) = the_default (Fv idn T) (lookup (\<lambda>x. x=(idn, T)) insts)"
| "subst_term _ (Bv n) = Bv n"
| "subst_term insts (Abs T t) = Abs T (subst_term insts t)"
| "subst_term insts (t $ u) = subst_term  insts t $ subst_term insts u"

lemma subst_term_empty_no_change[simp]: "subst_term [] t = t" 
  by (induction t) auto

lemma subst_type_term_without_type_insts_eq_subst_term[simp]: 
  "subst_type_term [] insts t = subst_term insts t"
  by (induction insts t rule: subst_term.induct) simp_all

lemma subst_type_term_split_levels: 
  "subst_type_term instT insts t = subst_term insts (subst_typ' instT t)"
  by (induction t) (auto simp add: Let_def)

(* Express parallel substitution as a series of single substitutions. *)

(* Deleted assms in the induction once, recheck proofs, maybe some get easier. *)
lemma subst_typ_stepwise:
  assumes "distinct (map fst instT)"
  assumes "\<And>x . x \<in> (\<Union>t \<in> snd ` set instT . tvsT t) \<Longrightarrow> x \<notin> fst ` set instT"
  shows "subst_typ instT T = fold (\<lambda>single acc . subst_typ [single] acc) instT T"
using assms proof (induction instT T rule: subst_typ.induct)
  case (1 inst a Ts)
  then show ?case
  proof (induction Ts arbitrary: inst)
    case Nil
    then show ?case by (induction inst) auto
  next
    case (Cons T Ts)
    hence "subst_typ inst (Ty a Ts) = fold (\<lambda>single. subst_typ [single]) inst (Ty a Ts)" 
      by simp
    moreover have "subst_typ inst T = fold (\<lambda>single. subst_typ [single]) inst T" 
        using Cons 1 by simp
    moreover have "fold (\<lambda>single. subst_typ [single]) inst (Ty a (T#Ts)) 
      = (Ty a (map (fold (\<lambda>single. subst_typ [single]) inst) (T#Ts)))"
    proof (induction inst rule: rev_induct)
      case Nil
      then show ?case by simp
    next
      case (snoc x xs)
      hence "fold (\<lambda>single. subst_typ [single]) (xs @ [x]) (Ty a (T # Ts)) =
        Ty a (map (subst_typ [x]) (map (fold (\<lambda>single. subst_typ [single]) xs) (T # Ts)))"
        by simp
      then show ?case by simp
    qed
    ultimately show ?case
      using Cons.prems(1) Cons.prems(2) local.Cons(4) by auto
  qed
next
  case (2 inst idn S)
  then show ?case
  proof (cases "lookup (\<lambda>x . x = (idn, S)) (inst)")
    case None
    hence "fst p \<noteq> (idn, S)" if "p\<in>set inst" for p using that by (auto simp add: lookup_None_iff)
    hence "subst_typ [p] (Tv idn S) = Tv idn S" if "p\<in>set inst" for p 
      using that by (cases p) fastforce
    from this None show ?thesis by (induction inst) (auto split: if_splits)
  next
    case (Some a)

    have elem: "((idn, S), a) \<in> set inst" using Some lookup_present_eq_key'' 2 by fastforce 
    from this obtain fs bs where split: "inst = fs @ ((idn, S), a) # bs"
      by (meson split_list) 
    hence "(idn, S) \<notin> set (map fst fs)" and "(idn, S) \<notin> set (map fst bs)" using 2 by simp_all

    hence "fst p \<noteq> (idn, S)" if "p\<in>set fs" for p 
      using that by force
    hence id_subst_fs: "subst_typ [p] (Tv idn S) = Tv idn S" if "p\<in>set fs" for p
      using that by (cases p) fastforce
    hence fs_step: "fold (\<lambda>single. subst_typ [single]) fs (Tv idn S) = Tv idn S"
      by (induction fs) (auto split: if_splits)

    have change_step: "subst_typ [((idn, S), a)] (Tv idn S) = a" by simp

    have bs_sub: "set bs \<subseteq> set inst" using split by auto
    hence "x \<notin> fst ` set bs" 
      if "x\<in> \<Union> (tvsT ` snd ` set bs)" for x
      using 2 that split by (auto simp add: image_iff)

    have "v \<notin> fst ` set bs" if "v \<in> tvsT a" for v
      using that 2 elem bs_sub by (fastforce simp add: image_iff)
    
    hence id_subst_bs: "subst_typ [p] a = a" if "p \<in> set bs" for p
    using that proof(cases p, induction a)
      case (Ty n Ts)
      then show ?case
        by (induction Ts) auto
    next
      case (Tv n S)
      then show ?case
        by force
    qed
    hence bs_step: "fold (\<lambda>single. subst_typ [single]) bs a = a"
      by (induction bs) auto

    from fs_step change_step bs_step split Some show ?thesis by simp 
  qed
qed

corollary subst_typ_split_first:
  assumes "distinct (map fst (x#xs))"
  assumes "\<And>y . y \<in> (\<Union>t \<in> snd ` set (x#xs) . tvsT t) \<Longrightarrow> y \<notin> fst ` (set (x#xs))"
  shows "subst_typ (x#xs) T = subst_typ xs (subst_typ [x] T)"
proof-
  have "subst_typ (x#xs) T = fold (\<lambda>single . subst_typ [single]) (x#xs) T" 
    using assms subst_typ_stepwise by blast
  also have "\<dots> = fold (\<lambda>single . subst_typ [single]) xs (subst_typ [x] T)"
    by simp
  also have "\<dots> = subst_typ xs (subst_typ [x] T)"
    using assms subst_typ_stepwise by simp
  finally show ?thesis .
qed

corollary subst_typ_split_last:
  assumes "distinct (map fst (xs @ [x]))"
  assumes "\<And>y . y \<in> (\<Union>t \<in> snd ` (set (xs @ [x])) . tvsT t) \<Longrightarrow> y \<notin> fst ` (set (xs @ [x]))"
  shows "subst_typ (xs @ [x]) T = subst_typ [x] (subst_typ xs T)"
proof-
  have "subst_typ (xs @ [x]) T = fold (\<lambda>single . subst_typ [single]) (xs@[x]) T" 
    using assms subst_typ_stepwise by blast
  also have "\<dots> = subst_typ [x] (fold (\<lambda>single . subst_typ [single]) xs T)"
    by simp
  also have "\<dots> = subst_typ [x] (subst_typ xs T)"
    using assms subst_typ_stepwise by simp
  finally show ?thesis .
qed

lemma subst_typ'_stepwise:
  assumes "distinct (map fst instT)"
  assumes "\<And>x . x \<in> (\<Union>t \<in> snd ` (set instT) . tvsT t) \<Longrightarrow> x \<notin> fst ` (set instT)"
  shows "subst_typ' instT t = fold (\<lambda>single acc . subst_typ' [single] acc) instT t"
(* I switched the order of inductions and 99% of the proof vanished *)
using assms proof (induction instT arbitrary: t rule: rev_induct)
  case Nil
  then show ?case by simp 
next
  case (snoc x xs)
  then show ?case
    apply (induction t) 
    using subst_typ_split_last apply simp_all
    apply (metis map_types.simps)+ (* ... *)
    done
qed


lemma subst_term_stepwise:
  assumes "distinct (map fst insts)"
  assumes "\<And>x . x \<in> (\<Union>t \<in> snd ` (set insts) . fv t) \<Longrightarrow> x \<notin> fst ` (set insts)"
  shows "subst_term insts t = fold (\<lambda>single acc . subst_term [single] acc) insts t"
using assms proof (induction insts arbitrary: t rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  then show ?case
  proof (induction t)
    case (Fv idn T)
    (* Allows more direct copy paste, hide structure of list, do proof properly later *)
    define insts where insts_def: "insts = xs @ [x]"
    have insts_thm1: "distinct (map fst insts)" using insts_def snoc by simp
    have insts_thm2: "x \<notin> fst ` set insts" if "x \<in> \<Union> (fv ` snd ` set insts)" for x
      using insts_def snoc that by blast
    from Fv show ?case 
    (* Proof copied from subst_typ *)
    proof (cases "lookup (\<lambda>x . x = (idn, T)) insts")
      case None
      hence "fst p \<noteq> (idn, T)" if "p\<in>set insts" for p using that by (auto simp add: lookup_None_iff)
      hence "subst_term [p] (Fv idn T) = Fv idn T" if "p\<in>set insts" for p 
        using that by (cases p) fastforce
      from this None show ?thesis 
        unfolding insts_def[symmetric] 
        by (induction insts) (auto split: if_splits)
    next
      case (Some a)
  
      have elem: "((idn, T), a) \<in> set insts" using Some lookup_present_eq_key'' insts_thm1 by fastforce
      from this obtain fs bs where split: "insts = fs @ ((idn, T), a) # bs"
        by (meson split_list) 
      hence "(idn, T) \<notin> set (map fst fs)" and "(idn, T) \<notin> set (map fst bs)" using insts_thm1 by simp_all
  
      hence "fst p ~= (idn, T)" if "p\<in>set fs" for p 
        using that by force
      hence id_subst_fs: "subst_term [p] (Fv idn T) = Fv idn T" if "p\<in>set fs" for p
        using that by (cases p) fastforce
      hence fs_step: "fold (\<lambda>single. subst_term [single]) fs (Fv idn T) = Fv idn T"
        by (induction fs) (auto split: if_splits)
  
      have change_step: "subst_term [((idn, T), a)] (Fv idn T) = a" by simp
  
      have bs_sub: "set bs \<subseteq> set insts" using split by auto
      hence "x \<notin> fst ` set bs" 
        if "x\<in> \<Union> (fv ` snd ` set bs)" for x
        using insts_thm2 that split by (auto simp add: image_iff)
  
      have "v \<notin> fst ` set bs" if "v \<in> fv a" for v
        using that insts_thm2 elem bs_sub by (fastforce simp add: image_iff)
      
      hence id_subst_bs: "subst_term [p] a = a" if "p\<in>set bs" for p
        using that by (cases p, induction a) force+
      hence bs_step: "fold (\<lambda>single. subst_term [single]) bs a = a"
        by (induction bs) auto
  
      from fs_step change_step bs_step split Some show ?thesis by (simp add: insts_def) 
    qed
  qed (simp, metis subst_term.simps)+
qed

corollary subst_term_split_last:
  assumes "distinct (map fst (xs @ [x]))"
  assumes "\<And>y . y \<in> (\<Union>t \<in> snd ` (set (xs @ [x])) . fv t) \<Longrightarrow> y \<notin> fst ` (set (xs @ [x]))"
  shows "subst_term (xs @ [x]) t = subst_term [x] (subst_term xs t)"
proof-
  have "subst_term (xs @ [x]) t = fold (\<lambda>single . subst_term [single]) (xs@[x]) t" 
    using assms subst_term_stepwise by blast
  also have "\<dots> = subst_term [x] (fold (\<lambda>single . subst_term [single]) xs t)"
    by simp
  also have "\<dots> = subst_term [x] (subst_term xs t)"
    using assms subst_term_stepwise by simp
  finally show ?thesis .
qed

corollary subst_type_term_stepwise:
  assumes "distinct (map fst instT)"
  assumes "\<And>x . x \<in> (\<Union>T \<in> snd ` (set instT) . tvsT T) \<Longrightarrow> x \<notin> fst ` (set instT)"
  assumes "distinct (map fst insts)"
  assumes "\<And>x . x \<in> (\<Union>t \<in> snd ` (set insts) . fv t) \<Longrightarrow> x \<notin> fst ` (set insts)"
  shows "subst_type_term instT insts t 
    = fold (\<lambda>single . subst_term [single]) insts (fold (\<lambda>single . subst_typ' [single]) instT t)"
  using assms subst_typ'_stepwise subst_term_stepwise subst_type_term_split_levels by auto

(* MOVE *)
lemma distinct_fst_imp_distinct: "distinct (map fst l) \<Longrightarrow> distinct l" by (induction l) auto
lemma distinct_kv_list: "distinct l \<Longrightarrow> distinct (map (\<lambda>x. (x, f x)) l)" by (induction l) auto

lemma subst_subst_term: 
  assumes "distinct l" and "fv t \<subseteq> set l"
  shows "subst t \<rho> = subst_term (map (\<lambda>x.(x, case_prod \<rho> x)) l) t"
using assms proof (induction t arbitrary: l)
  case (Fv idn T)
  then show ?case 
  proof (cases "(idn, T) \<in> set l")
    case True
    hence "((idn, T), \<rho> idn T) \<in> set (map (\<lambda>x.(x, case_prod \<rho> x)) l)" by auto
    moreover have "distinct (map fst (map (\<lambda>x.(x, case_prod \<rho> x)) l))" 
      using Fv(1) by (induction l) auto 
    ultimately have "(lookup (\<lambda>x. x = (idn, T)) (map (\<lambda>x. (x, case x of (x, xa) \<Rightarrow> \<rho> x xa)) l))
      = Some (\<rho> idn T)" using lookup_present_eq_key by fast
    then show ?thesis by simp
  next
    case False
    then show ?thesis using Fv by simp
  qed
qed auto


lemma subst_term_subst:
  assumes "distinct (map fst l)"
  shows "subst_term l t = subst t (fold (\<lambda>((idn, T), t) f x y. if x=idn \<and>y=T then t else f x y) l Fv)"
using assms proof (induction t)
  case (Fv idn T)
  then show ?case
  proof (cases "lookup (\<lambda>x. x = (idn, T)) l")
    case None
    hence "(idn, T) \<notin> set (map fst l)"
      by (metis (full_types) lookup_None_iff)
    
    hence "(fold (\<lambda>((idn, T), t) f x y. if x=idn \<and>y=T then t else f x y) l Fv) idn T = Fv idn T"
      by (induction l rule: rev_induct) (auto split: if_splits prod.splits) 
      
    then show ?thesis by (simp add: None)
  next
    case (Some a)

    have elem: "((idn, T), a) \<in> set l" 
      using Some lookup_present_eq_key'' Fv by fastforce
    from this obtain fs bs where split: "l = fs @ ((idn, T), a) # bs"
      by (meson split_list) 
    hence "(idn, T) \<notin> set (map fst fs)" and not_in_bs: "(idn, T) \<notin> set (map fst bs)" using Fv by simp_all

    hence "fst p ~= (idn, T)" if "p\<in>set fs" for p 
      using that by force
    hence fs_step: "(fold (\<lambda>((idn, T), t) f x y. if x=idn \<and>y=T then t else f x y) fs Fv) idn T = Fv idn T"
      by (induction fs rule: rev_induct) (fastforce split: if_splits prod.splits)+

    have bs_sub: "set bs \<subseteq> set l" using split by auto
    
    have "fst p ~= (idn, T)" if "p\<in>set bs" for p 
      using that not_in_bs by force
    hence bs_step: "(fold (\<lambda>((idn, T), t) f x y. if x=idn \<and>y=T then t else f x y) bs f) idn T = f idn T"
      for f
      by (induction bs rule: rev_induct) (fastforce split: if_splits prod.splits)+

    from fs_step bs_step split Some show ?thesis by simp
  qed
qed auto

lemma subst_typ_combine_single:
  assumes "fresh_idn \<notin> fst ` tvsT \<tau>"
  shows "subst_typ [((fresh_idn, S), \<tau>2)] (subst_typ [((idn, S), Tv fresh_idn S)] \<tau>)
    = subst_typ [((idn, S), \<tau>2)] \<tau>"
  using assms by (induction \<tau>) auto

lemma subst_typ_combine:
  assumes "length fresh_idns = length insts"
  assumes "distinct fresh_idns"
  assumes "distinct (map fst insts)"
  assumes "\<forall>idn \<in> set fresh_idns . idn \<notin> fst ` (tvsT \<tau> \<union> (\<Union>ty\<in>snd ` set insts . (tvsT ty)) 
    \<union> (fst ` set insts))"
  shows "subst_typ insts \<tau> 
    = subst_typ (zip (zip fresh_idns (map snd (map fst insts))) (map snd insts)) 
      (subst_typ (zip (map fst insts) (map2 Tv fresh_idns (map snd (map fst insts)))) \<tau>)"
  using assms proof (induction insts \<tau> arbitrary: fresh_idns rule: subst_typ.induct)
  case (1 inst a Ts)
  then show ?case by fastforce (* LOL, I wanted to do another induction *)
next
  case (2 inst idn S)
  show ?case
  proof (cases "lookup (\<lambda>x. x = (idn, S)) inst")
    case None
    hence "((idn, S)) \<notin> fst ` set inst"
      by (metis (mono_tags, lifting) list.set_map lookup_None_iff)
    hence 1: "(lookup (\<lambda>x. x = (idn, S)) 
      (zip (map fst inst) (map2 Tv fresh_idns (map (snd \<circ> fst) inst)))) = None" 
      using 2 by (simp add: lookup_eq_key_not_present)

    have "(idn, S) \<notin> set (zip fresh_idns (map (snd \<circ> fst) inst))"
      using 2 set_zip_leftD by fastforce 
    hence "(lookup (\<lambda>x. x = (idn, S)) 
      (zip (zip fresh_idns (map (snd \<circ> fst) inst)) (map snd inst))) = None"
      using 2 by (simp add: lookup_eq_key_not_present)

    then show ?thesis using None 1 by simp
  next
    case (Some ty)
    from this obtain idx where idx: "inst ! idx = ((idn, S), ty)" "idx < length inst"
    proof (induction inst)
      case Nil
      then show ?case 
        by simp
    next
      case (Cons a as) thm Cons.IH
      have "(\<And>idx. as ! idx = ((idn, S), ty) \<Longrightarrow> idx < length as \<Longrightarrow> thesis)"
        by (metis Cons.prems(1) in_set_conv_nth list.set_intros(2))
      then show ?case
        by (meson Cons.prems(1) Cons.prems(2) in_set_conv_nth lookup_present_eq_key')
    qed

    from this obtain fresh_idn where fresh_idn: "fresh_idns ! idx = fresh_idn" by simp

    from 2(1) idx fresh_idn have ren:
      "(zip (map fst inst) (map2 Tv fresh_idns (map (snd \<circ> fst) inst))) ! idx 
      = ((idn, S), Tv fresh_idn S) "
      by auto
    from this idx(2) have "((idn, S), Tv fresh_idn S) \<in> set
      (zip (map fst inst) (map2 Tv fresh_idns (map (snd \<circ> fst) inst)))"
      by (metis (no_types, hide_lams) "2.prems"(1) length_map map_fst_zip map_map map_snd_zip nth_mem)
    from this have 1: "(lookup (\<lambda>x. x = (idn, S)) 
      (zip (map fst inst) (map2 Tv fresh_idns (map (snd \<circ> fst) inst)))) = Some (Tv fresh_idn S)"
      by (simp add: "2.prems"(1) "2.prems"(3) lookup_present_eq_key'')

    from 2(1) idx fresh_idn 1 have "((fresh_idn, S), ty) 
      \<in> set (zip (zip fresh_idns (map (snd \<circ> fst) inst)) (map snd inst))"
      using in_set_conv_nth by fastforce
    hence 2: "(lookup (\<lambda>x. x = (fresh_idn, S)) 
      (zip (zip fresh_idns (map (snd \<circ> fst) inst)) (map snd inst))) = Some ty"
      by (simp add: "2.prems"(1) "2.prems"(2) distinct_zipI1 lookup_present_eq_key'')
    then show ?thesis using Some 1 2 by simp
  qed
qed

lemma subst_typ_combine':
  assumes "length fresh_idns = length insts"
  assumes "distinct fresh_idns"
  assumes "distinct (map fst insts)"
  assumes "\<forall>idn \<in> set fresh_idns . idn \<notin> fst ` (tvsT \<tau> \<union> (\<Union>ty\<in>snd ` set insts . (tvsT ty)) 
    \<union> (fst ` set insts))"
  shows "subst_typ insts \<tau> 
    = fold (\<lambda>single acc . subst_typ [single] acc) (zip (zip fresh_idns (map snd (map fst insts))) (map snd insts)) 
      (fold (\<lambda>single acc . subst_typ [single] acc) (zip (map fst insts) (map2 Tv fresh_idns (map snd (map fst insts)))) \<tau>)"
proof-
  have s1: "fst ` set (zip (map fst insts) (map2 Tv fresh_idns (map snd (map fst insts))))
    = fst ` set insts "
  proof-
    have "fst ` set (zip (map fst insts) (map2 Tv fresh_idns (map snd (map fst insts))))
      = set (map fst (zip (map fst insts) (map2 Tv fresh_idns (map snd (map fst insts)))))"
      by auto
    also have "\<dots> = set (map fst insts)" using map_fst_zip assms(1) by auto
    also have "\<dots> = fst ` set insts" by simp
    finally show ?thesis .
  qed

  have "snd ` set (zip (map fst insts) (map2 Tv fresh_idns (map snd (map fst insts))))
    = set (map2 Tv fresh_idns (map snd (map fst insts)))" using map_snd_zip assms(1)
    by (metis (no_types, lifting) image_set length_map)
  hence "(\<Union> (tvsT ` snd ` set (zip (map fst insts) (map2 Tv fresh_idns (map snd (map fst insts))))))
    = (\<Union> (tvsT ` set (map2 Tv fresh_idns (map snd (map fst insts)))))" 
    by simp
  from assms(1) this have s2:
    "(\<Union> (tvsT ` snd ` set (zip (map fst insts) (map2 Tv fresh_idns (map snd (map fst insts))))))
    = (set (zip fresh_idns (map snd (map fst insts))))"
    using assms(1) by (induction fresh_idns insts rule: list_induct2) auto
  hence s3: "\<Union> (tvsT ` snd ` set (zip (map fst insts)
                   (map2 Tv fresh_idns (map (snd \<circ> fst) insts))))
    = set (zip fresh_idns (map snd (map fst insts)))" by simp
  have "idn \<notin> fst ` fst ` set insts" if "idn \<in> set fresh_idns" for idn
    using that assms by auto
  hence I: "(idn, S) \<notin> fst ` set insts" if "idn \<in> set fresh_idns" for idn S
    using that assms by (metis fst_conv image_eqI)

  have u1: "(subst_typ (zip (map fst insts) (map2 Tv fresh_idns (map snd (map fst insts)))) \<tau>)
    = fold (\<lambda>single acc . subst_typ [single] acc) (zip (map fst insts) (map2 Tv fresh_idns (map snd (map fst insts)))) \<tau>"
    apply (rule subst_typ_stepwise)
    using assms apply simp 
    apply (simp only: s1 s2)  
     using assms I by (metis prod.collapse set_zip_leftD)

  moreover have u2: "subst_typ (zip (zip fresh_idns (map snd (map fst insts))) (map snd insts)) 
    (subst_typ (zip (map fst insts) (map2 Tv fresh_idns (map snd (map fst insts)))) \<tau>)
  = fold (\<lambda>single acc . subst_typ [single] acc) (zip (zip fresh_idns (map snd (map fst insts))) (map snd insts)) 
    (subst_typ (zip (map fst insts) (map2 Tv fresh_idns (map snd (map fst insts)))) \<tau>)"
   apply (rule subst_typ_stepwise)
   using assms apply (simp add: distinct_zipI1)
   using assms
   by (smt UnCI imageE image_eqI length_map map_snd_zip prod.collapse set_map set_zip_leftD)
  ultimately have unfold: "subst_typ (zip (zip fresh_idns (map snd (map fst insts))) (map snd insts)) 
    (subst_typ (zip (map fst insts) (map2 Tv fresh_idns (map snd (map fst insts)))) \<tau>)
   = fold (\<lambda>single acc . subst_typ [single] acc) (zip (zip fresh_idns (map snd (map fst insts))) (map snd insts)) 
        (fold (\<lambda>single acc . subst_typ [single] acc) (zip (map fst insts) (map2 Tv fresh_idns (map snd (map fst insts)))) \<tau>)"
     by simp
  show ?thesis using assms subst_typ_combine unfold by auto
qed

lemma subst_typ'_combine:
  assumes "length fresh_idns = length insts"
  assumes "distinct fresh_idns"
  assumes "distinct (map fst insts)"
  assumes "\<forall>idn \<in> set fresh_idns . idn \<notin> fst ` (tvs t \<union> (\<Union>ty\<in>snd ` set insts . (tvsT ty)) 
    \<union> (fst ` set insts))"
  shows "subst_typ' insts t
    = subst_typ' (zip (zip fresh_idns (map snd (map fst insts))) (map snd insts)) 
      (subst_typ' (zip (map fst insts) (map2 Tv fresh_idns (map snd (map fst insts)))) t)"
using assms proof (induction t arbitrary: fresh_idns insts)
  case (Abs T t)
  moreover have "tvs t \<subseteq> tvs (Abs T t) " by simp
  ultimately have "subst_typ' insts t =
    subst_typ' (zip (zip fresh_idns (map snd (map fst insts))) (map snd insts))
     (subst_typ' (zip (map fst insts) (map2 Tv fresh_idns (map snd (map fst insts)))) t)" 
    by blast
  moreover have "subst_typ insts T =
    subst_typ (zip (zip fresh_idns (map snd (map fst insts))) (map snd insts))
     (subst_typ (zip (map fst insts) (map2 Tv fresh_idns (map snd (map fst insts)))) T)"
    using subst_typ_combine Abs.prems by fastforce
  ultimately show ?case by simp 
next
  case (App t1 t2)
  moreover have "tvs t1 \<subseteq> tvs (t1 $ t2)" "tvs t2 \<subseteq> tvs (t1 $ t2)" by auto
  ultimately have "subst_typ' insts t1 =
    subst_typ' (zip (zip fresh_idns (map snd (map fst insts))) (map snd insts))
     (subst_typ' (zip (map fst insts) (map2 Tv fresh_idns (map snd (map fst insts)))) t1)" 
  and "subst_typ' insts t2 =
    subst_typ' (zip (zip fresh_idns (map snd (map fst insts))) (map snd insts))
     (subst_typ' (zip (map fst insts) (map2 Tv fresh_idns (map snd (map fst insts)))) t2)"
    by blast+
  then show ?case by simp
qed (use subst_typ_combine in auto)

(* Only interesting case is Fv, and that one is copied directly from subst_typ *)
lemma subst_term_combine:
  assumes "length fresh_idns = length insts"
  assumes "distinct fresh_idns"
  assumes "distinct (map fst insts)"
  assumes "\<forall>idn \<in> set fresh_idns . idn \<notin> fst ` (fv t \<union> (\<Union>t\<in>snd ` set insts . (fv t)) 
    \<union> (fst ` set insts))"
  shows "subst_term insts t
    = subst_term (zip (zip fresh_idns (map snd (map fst insts))) (map snd insts)) 
      (subst_term (zip (map fst insts) (map2 Fv fresh_idns (map snd (map fst insts)))) t)"
using assms proof (induction t arbitrary: fresh_idns insts)
  case (Fv idn ty)
  
  then show ?case
  proof (cases "lookup (\<lambda>x. x = (idn, ty)) insts")
    case None
    hence "((idn, ty)) \<notin> fst ` set insts"
      by (metis (mono_tags, lifting) list.set_map lookup_None_iff)
    hence 1: "(lookup (\<lambda>x. x = (idn, ty)) 
      (zip (map fst insts) (map2 Fv fresh_idns (map (snd \<circ> fst) insts)))) = None" 
      using Fv by (simp add: lookup_eq_key_not_present)

    have "(idn, ty) \<notin> set (zip fresh_idns (map (snd \<circ> fst) insts))"
      using Fv set_zip_leftD by fastforce 
    hence "(lookup (\<lambda>x. x = (idn, ty)) 
      (zip (zip fresh_idns (map (snd \<circ> fst) insts)) (map snd insts))) = None"
      using Fv by (simp add: lookup_eq_key_not_present)

    then show ?thesis using None 1 by simp
  next
    case (Some u)
    from this obtain idx where idx: "insts ! idx = ((idn, ty), u)" "idx < length insts"
    proof (induction insts)
      case Nil
      then show ?case
        by simp
    next
      case (Cons a as)
      have "(\<And>idx. as ! idx = ((idn, ty), u) \<Longrightarrow> idx < length as \<Longrightarrow> thesis)"
        by (metis Cons.prems(1) in_set_conv_nth insert_iff list.set(2))
      then show ?case 
        by (meson Cons.prems(1) Cons.prems(2) in_set_conv_nth lookup_present_eq_key')
    qed

    from this obtain fresh_idn where fresh_idn: "fresh_idns ! idx = fresh_idn" by simp

    from Fv(1) idx fresh_idn have ren:
      "(zip (map fst insts) (map2 Fv fresh_idns (map (snd \<circ> fst) insts))) ! idx 
      = ((idn, ty), Fv fresh_idn ty)"
      by auto
    from this idx(2) have "((idn, ty), Fv fresh_idn ty) \<in> set
      (zip (map fst insts) (map2 Fv fresh_idns (map (snd \<circ> fst) insts)))"
      by (metis (no_types, hide_lams) "Fv.prems"(1) length_map map_fst_zip map_map map_snd_zip nth_mem)
    from this have 1: "(lookup (\<lambda>x. x = (idn, ty)) 
      (zip (map fst insts) (map2 Fv fresh_idns (map (snd \<circ> fst) insts)))) = Some (Fv fresh_idn ty)"
      by (simp add: "Fv.prems"(1) "Fv.prems"(3) lookup_present_eq_key'')

    (* Feels doable with better simp setup *)
    from Fv(1) idx fresh_idn 1 have "((fresh_idn, ty), u) 
      \<in> set (zip (zip fresh_idns (map (snd \<circ> fst) insts)) (map snd insts))"
      using in_set_conv_nth by fastforce
    hence 2: "(lookup (\<lambda>x. x = (fresh_idn, ty)) 
      (zip (zip fresh_idns (map (snd \<circ> fst) insts)) (map snd insts))) = Some u"
      by (simp add: "Fv.prems"(1) "Fv.prems"(2) distinct_zipI1 lookup_present_eq_key'')
    then show ?thesis using Some 1 2 by simp
  qed
next
  case (App t1 t2)
  moreover have "fv t1 \<subseteq> fv (t1 $ t2)" "fv t2 \<subseteq> fv (t1 $ t2)" by simp_all
  ultimately have "subst_term insts t1 =
    subst_term (zip (zip fresh_idns (map snd (map fst insts))) (map snd insts))
     (subst_term (zip (map fst insts) (map2 Fv fresh_idns (map snd (map fst insts)))) t1)" 
  and "subst_term insts t2 =
    subst_term (zip (zip fresh_idns (map snd (map fst insts))) (map snd insts))
     (subst_term (zip (map fst insts) (map2 Fv fresh_idns (map snd (map fst insts)))) t2)" 
    by blast+
  then show ?case by simp
qed auto

corollary subst_term_combine':
  assumes "length fresh_idns = length insts"
  assumes "distinct fresh_idns"
  assumes "distinct (map fst insts)"
  assumes "\<forall>idn \<in> set fresh_idns . idn \<notin> fst ` (fv t \<union> (\<Union>t\<in>snd ` set insts . (fv t)) 
    \<union> (fst ` set insts))"
  shows "subst_term insts t
    = fold (\<lambda>single acc . subst_term [single] acc) (zip (zip fresh_idns (map snd (map fst insts))) (map snd insts)) 
      (fold (\<lambda>single acc . subst_term [single] acc) (zip (map fst insts) (map2 Fv fresh_idns (map snd (map fst insts)))) t)"
proof-
  have s1: "fst ` set (zip (map fst insts) (map2 Fv fresh_idns (map snd (map fst insts))))
    = fst ` set insts "
  proof-
    have "fst ` set (zip (map fst insts) (map2 Fv fresh_idns (map snd (map fst insts))))
      = set (map fst (zip (map fst insts) (map2 Fv fresh_idns (map snd (map fst insts)))))"
      by auto
    also have "\<dots> = set (map fst insts)" using map_fst_zip assms(1) by auto
    also have "\<dots> = fst ` set insts" by simp
    finally show ?thesis .
  qed

  have "snd ` set (zip (map fst insts) (map2 Fv fresh_idns (map snd (map fst insts))))
    = set (map2 Fv fresh_idns (map snd (map fst insts)))" using map_snd_zip assms(1)
    by (metis (no_types, lifting) image_set length_map)
  hence "(\<Union> (fv ` snd ` set (zip (map fst insts) (map2 Fv fresh_idns (map snd (map fst insts))))))
    = (\<Union> (fv ` set (map2 Fv fresh_idns (map snd (map fst insts)))))" 
    by simp
  from assms(1) this have s2:
    "(\<Union> (fv ` snd ` set (zip (map fst insts) (map2 Fv fresh_idns (map snd (map fst insts))))))
    = (set (zip fresh_idns (map snd (map fst insts))))"
    using assms(1) by (induction fresh_idns insts rule: list_induct2) auto
  hence s3: "\<Union> (fv ` snd ` set (zip (map fst insts)
                   (map2 Fv fresh_idns (map (snd \<circ> fst) insts))))
    = set (zip fresh_idns (map snd (map fst insts)))" by simp
  have "idn \<notin> fst ` fst ` set insts" if "idn \<in> set fresh_idns" for idn
    using that assms by auto
  hence I: "(idn, T) \<notin> fst ` set insts" if "idn \<in> set fresh_idns" for idn T
    using that assms by (metis fst_conv image_eqI)

  have u1: "(subst_term (zip (map fst insts) (map2 Fv fresh_idns (map snd (map fst insts)))) t)
    = fold (\<lambda>single acc . subst_term [single] acc) (zip (map fst insts) (map2 Fv fresh_idns (map snd (map fst insts)))) t"
    apply (rule subst_term_stepwise)
    using assms apply simp 
    apply (simp only: s1 s2)  
     using assms I by (metis prod.collapse set_zip_leftD)

  moreover have u2: "subst_term (zip (zip fresh_idns (map snd (map fst insts))) (map snd insts)) 
    (subst_term (zip (map fst insts) (map2 Fv fresh_idns (map snd (map fst insts)))) t)
  = fold (\<lambda>single acc . subst_term [single] acc) (zip (zip fresh_idns (map snd (map fst insts))) (map snd insts)) 
    (subst_term (zip (map fst insts) (map2 Fv fresh_idns (map snd (map fst insts)))) t)"
   apply (rule subst_term_stepwise)
   using assms apply (simp add: distinct_zipI1)
   using assms
   by (smt UnCI imageE image_eqI length_map map_snd_zip prod.collapse set_map set_zip_leftD)
  ultimately have unfold: "subst_term (zip (zip fresh_idns (map snd (map fst insts))) (map snd insts)) 
    (subst_term (zip (map fst insts) (map2 Fv fresh_idns (map snd (map fst insts)))) t)
   = fold (\<lambda>single acc . subst_term [single] acc) (zip (zip fresh_idns (map snd (map fst insts))) (map snd insts)) 
        (fold (\<lambda>single acc . subst_term [single] acc) (zip (map fst insts) (map2 Fv fresh_idns (map snd (map fst insts)))) t)"
     by simp
  show ?thesis using assms subst_term_combine unfold by auto
qed


lemma subst_term_not_loose_bvar:
  assumes "\<not> loose_bvar t n" "is_closed b" 
  shows "\<not> loose_bvar (subst_term [((idn,T),b)] t) n"
  using assms by (induction t arbitrary: n idn T b) (auto simp add: is_open_def loose_bvar_leq)
  
(* This seems a bit to weak, second premise probably needs to be more general *)
lemma bind_fv2_subst_bv1_eq_subst_term: 
  assumes "\<not>loose_bvar t n" "is_closed b"
  shows "subst_term [((idn,T),b)] t = subst_bv1 (bind_fv2 (idn, T) n t) n b"
  using assms by (induction t arbitrary: n idn T b) (auto simp add: is_open_def incr_boundvars_def)

corollary
  assumes "is_closed t" "is_closed b" 
  shows "subst_bv b (bind_fv (idn, T) t) = (subst_term [((idn, T),b)] t)"
  using assms bind_fv2_subst_bv1_eq_subst_term
  by (simp add: bind_fv_def subst_bv_def is_open_def)

corollary instantiate_var_same_typ:
  assumes typ_a: "typ_of a = Some \<tau>"
  assumes closed_B: "\<not> loose_bvar B lev"
  shows "subst_bv1 (bind_fv2 (x, \<tau>) lev B) lev a = subst_term [((x, \<tau>), a)] B"
  using bind_fv2_subst_bv1_eq_subst_term assms typ_of_imp_closed by metis

corollary instantiate_var_same_typ':
  assumes typ_a: "typ_of a = Some \<tau>"
  assumes closed_B: "is_closed B"
  shows "subst_bv a (bind_fv (x, \<tau>) B) = subst_term [((x, \<tau>), a)] B"
  using instantiate_var_same_typ bind_fv_def subst_bv_def is_open_def assms by auto

corollary instantiate_var_same_type'':
  assumes typ_a: "typ_of a = Some \<tau>"
  assumes closed_B: "is_closed B"
  shows "Abs \<tau> (bind_fv (x, \<tau>) B) \<bullet> a = subst_term [((x, \<tau>), a)] B"
  using assms instantiate_var_same_typ' by simp

lemma instantiate_vars_same_typ:
  assumes typs: "list_all (\<lambda>((idx, ty), t) . typ_of t = Some ty) insts"
  assumes closed_B: "\<not> loose_bvar B lev"
  shows "fold (\<lambda>((idx, ty), t) B . subst_bv1 (bind_fv2 (idx, ty) lev B) lev t) insts B
    = fold (\<lambda>single . subst_term [single]) insts B"
using assms proof (induction insts arbitrary: B lev)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)

  from this obtain idn ty t where x: "x = ((idn, ty), t)" by (metis prod.collapse)

  hence typ_a: "typ_of t = Some ty" using Cons.prems by simp
  have typs: "list_all (\<lambda>((idx, ty), t) . typ_of t = Some ty) xs" using Cons.prems by simp
  have not_loose: "\<not> loose_bvar (subst_term [((idn, ty), t)] B) lev" 
    using Cons.prems subst_term_not_loose_bvar typ_a typ_of_imp_closed by simp

  note single = instantiate_var_same_typ[OF typ_a Cons.prems(2), of idn]

  have "fold (\<lambda>((idx, ty), t) B . subst_bv1 (bind_fv2 (idx, ty) lev B) lev t) (x # xs) B
    = fold (\<lambda>((idx, ty), t) B. subst_bv1 (bind_fv2 (idx, ty) lev B) lev t) xs 
        (subst_bv1 (bind_fv2 (idn, ty) lev B) lev t)"
    by (simp add: x)
  also have "\<dots> = fold (\<lambda>((idx, ty), t) B. subst_bv1 (bind_fv2 (idx, ty) lev B) lev t) xs
    (subst_term [((idn, ty), t)] B)"
    using single by simp
  also have "\<dots> = fold (\<lambda>single. subst_term [single]) xs (subst_term [((idn, ty), t)] B)"
    using Cons.IH[where B = "subst_term [((idn, ty), t)] B", OF typs not_loose] Cons.prems by blast
  also have "\<dots> = fold (\<lambda>single. subst_term [single]) (x # xs) B" 
    by (simp add: x)
  finally show ?case .
qed

corollary instantiate_vars_same_typ':
  assumes typs: "list_all (\<lambda>((idx, ty), t) . typ_of t = Some ty) insts"
  assumes closed_B: "\<not> loose_bvar B lev"
  assumes distinct: "distinct (map fst insts)"
  assumes no_overlap: "\<And>x . x \<in> (\<Union>t \<in> snd ` (set insts) . fv t) \<Longrightarrow> x \<notin> fst ` (set insts)"
  shows "fold (\<lambda>((idx, ty), t) B . subst_bv1 (bind_fv2 (idx, ty) lev B) lev t) insts B
    = subst_term insts B"
  using instantiate_vars_same_typ subst_term_stepwise[symmetric] assms by simp  

end