section "Beta Normalization"

(* 
  Much of this material is directly copied and adapted from @{dir "~~/src/HOL/Proofs/Lambda"}

  Proofs are in a lot of cases very ugly as they were copied+fixed
*)

theory BetaNorm         
  imports Term
begin                             

inductive beta :: "term \<Rightarrow> term \<Rightarrow> bool"  (infixl "\<rightarrow>\<^sub>\<beta>" 50)
  where
    beta [simp, intro!]: "Abs T s $ t \<rightarrow>\<^sub>\<beta> subst_bv2 s 0 t"
  | appL [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> s $ u \<rightarrow>\<^sub>\<beta> t $ u"
  | appR [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> u $ s \<rightarrow>\<^sub>\<beta> u $ t"
  | abs [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> Abs T s \<rightarrow>\<^sub>\<beta> Abs T t"

abbreviation
  beta_reds :: "term \<Rightarrow> term \<Rightarrow> bool" (infixl "\<rightarrow>\<^sub>\<beta>\<^sup>*" 50) where
  "s \<rightarrow>\<^sub>\<beta>\<^sup>* t == beta\<^sup>*\<^sup>* s t"

inductive_cases beta_cases [elim!]:
  "Bv i \<rightarrow>\<^sub>\<beta> t"
  "Fv idn S \<rightarrow>\<^sub>\<beta> t"
  "Abs T r \<rightarrow>\<^sub>\<beta> s"
  "s $ t \<rightarrow>\<^sub>\<beta> u"

declare if_not_P [simp] not_less_eq [simp]

lemma rtrancl_beta_Abs [intro!]:
    "s \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<Longrightarrow> Abs T s \<rightarrow>\<^sub>\<beta>\<^sup>* Abs T s'"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_AppL:
    "s \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<Longrightarrow> s $ t \<rightarrow>\<^sub>\<beta>\<^sup>* s' $ t"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_AppR:
    "t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> s $ t \<rightarrow>\<^sub>\<beta>\<^sup>* s $ t'"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_App [intro]:
    "s \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<Longrightarrow> t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> s $ t \<rightarrow>\<^sub>\<beta>\<^sup>* s' $ t'"
  by (blast intro!: rtrancl_beta_AppL rtrancl_beta_AppR intro: rtranclp_trans)

theorem subst_bv2_preserves_beta [simp]:
    "r \<rightarrow>\<^sub>\<beta> s \<Longrightarrow> subst_bv2 r k u \<rightarrow>\<^sub>\<beta> subst_bv2 s k u"
  by (induct arbitrary: k u set: beta) (simp_all add: subst_bv2_subst_bv2[symmetric])

theorem subst_bv2_preserves_beta': "r \<rightarrow>\<^sub>\<beta>\<^sup>* s \<Longrightarrow> subst_bv2 r i t  \<rightarrow>\<^sub>\<beta>\<^sup>* subst_bv2 s i t"
  apply (induct set: rtranclp)
   apply (rule rtranclp.rtrancl_refl)
  apply (erule rtranclp.rtrancl_into_rtrancl)
  apply (erule subst_bv2_preserves_beta)
  done

theorem lift_preserves_beta [simp]:
    "r \<rightarrow>\<^sub>\<beta> s \<Longrightarrow> lift r i \<rightarrow>\<^sub>\<beta> lift s i"
proof (induction arbitrary: i set: beta)
  case (beta T s t)
  then show ?case
    using lift_subst by force
qed auto
theorem lift_preserves_beta': "r \<rightarrow>\<^sub>\<beta>\<^sup>* s \<Longrightarrow> lift r i \<rightarrow>\<^sub>\<beta>\<^sup>* lift s i"
  apply (induct set: rtranclp)
   apply (rule rtranclp.rtrancl_refl)
  apply (erule rtranclp.rtrancl_into_rtrancl)
  apply (erule lift_preserves_beta)
  done

theorem subst_bv2_preserves_beta2 [simp]: "r \<rightarrow>\<^sub>\<beta> s \<Longrightarrow> subst_bv2 t i r \<rightarrow>\<^sub>\<beta>\<^sup>* subst_bv2 t i s"
  apply (induct t arbitrary: r s i)
    apply (solves \<open>simp add: r_into_rtranclp\<close>)+
  using lift_preserves_beta by (auto simp add: rtrancl_beta_App)

theorem subst_bv2_preserves_beta2': "r \<rightarrow>\<^sub>\<beta>\<^sup>* s \<Longrightarrow> subst_bv2 t i r \<rightarrow>\<^sub>\<beta>\<^sup>* subst_bv2 t i s"
  apply (induct set: rtranclp) 
    apply (auto elim: rtranclp_trans subst_bv2_preserves_beta2)
  done

lemma beta_preserves_typ_of1: "typ_of1 Ts r = Some T \<Longrightarrow> r \<rightarrow>\<^sub>\<beta> s \<Longrightarrow> typ_of1 Ts s = Some T"
proof (induction Ts r arbitrary: s T rule: typ_of1.induct)
  case (4 Ts T body)
  then show ?case 
    by (smt beta_cases(3) typ_of1.simps(4) typ_of_Abs_body_typ')
next
  case (5 Ts f u)
  from this obtain argT where argT: "typ_of1 Ts u = Some argT" and "typ_of1 Ts f = Some (argT \<rightarrow> T)"
    by (meson typ_of1_split_App_obtains)
  
  from 5 show ?case  apply -
    apply (ind_cases "f $ u \<rightarrow>\<^sub>\<beta> s" for f u s)
    using \<open>typ_of1 Ts f = Some (argT \<rightarrow> T)\<close> argT typ_of1_subst_bv_gen' 
      typ_of_Abs_body_typ' by (fastforce simp add: substn_subst_n)+
qed (use beta.cases in \<open>blast+\<close>)

lemma beta_preserves_typ_of: "typ_of r = Some T \<Longrightarrow> r \<rightarrow>\<^sub>\<beta> s \<Longrightarrow> typ_of s = Some T"
  by (metis beta_preserves_typ_of1 typ_of_def)

lemma beta_star_preserves_typ_of1: "r \<rightarrow>\<^sub>\<beta>\<^sup>* s \<Longrightarrow> typ_of1 Ts r = Some T  \<Longrightarrow> typ_of1 Ts s = Some T"
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case 
    by simp
next
  case (rtrancl_into_rtrancl a b c)
  then show ?case 
    using beta_preserves_typ_of1 by blast
qed
(* 
  Convert beta_norm to the inductive predicates. Then later show that one beta step can be justified
  using proves
*)

lemma beta_reducible_imp_beta_step: "beta_reducible t \<Longrightarrow> \<exists>t'. t \<rightarrow>\<^sub>\<beta> t'" 
proof (induction t)
  case (App t1 t2)
  then show ?case using App by (cases t1) auto
qed auto 

lemma beta_step_imp_beta_reducible: "t \<rightarrow>\<^sub>\<beta> t' \<Longrightarrow> beta_reducible t" 
proof (induction t t' rule: beta.induct)
  case (beta T s t)
  then show ?case by simp
next
case (appL s t u)
  then show ?case by (cases s) auto
next
  case (appR s t u)
  then show ?case using beta_reducible.elims by blast
next
  case (abs s t T)
  then show ?case by simp
qed

lemma beta_norm_imp_beta_reds: assumes "beta_norm t = Some t'" shows "t \<rightarrow>\<^sub>\<beta>\<^sup>* t'"
  using assms proof (induction arbitrary: t t' rule: beta_norm.fixp_induct)
  case 1
  then show ?case 
    by (smt Option.is_none_def ccpo.admissibleI chain_fun flat_lub_def flat_ord_def fun_lub_def 
        insertCI is_none_code(2) mem_Collect_eq option.lub_upper subsetI)
next
  case 2
  then show ?case 
    by simp
next
  case (3 comp)
  then show ?case 
  proof(cases t)
  next
    case (App f u)
    note fu = App
    then show ?thesis 
    proof (cases "comp f")
      case None
      show ?thesis
      proof(cases f)
        case (Abs B b)
        then show ?thesis  
          by (metis (mono_tags, lifting) "3.IH" "3.prems" Core.subst_bv_def Core.term.simps(29) 
              Core.term.simps(30) beta fu rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl rtranclp_trans)
      qed (use 3 None in \<open>simp_all add: fu split: term.splits option.splits if_splits\<close>)
    next
      case (Some fo)
      then show ?thesis 
      proof(cases fo)
        case (Ct n T)
        then show ?thesis
        proof(cases f)
          case (Abs B b)
          then show ?thesis 
            by (metis (no_types, lifting) "3.IH" "3.prems" Core.subst_bv_def Core.term.simps(29)
                Core.term.simps(30) beta converse_rtranclp_into_rtranclp fu)
        qed (use 3 Some in \<open>auto simp add: fu split: term.splits option.splits if_split\<close>)
      next
        case (Fv n T)
        then show ?thesis 
        proof(cases f)
          case (Abs B b)
          then show ?thesis 
            by (metis (no_types, lifting) "3.IH" "3.prems" Core.subst_bv_def Core.term.simps(29)
                Core.term.simps(30) beta converse_rtranclp_into_rtranclp fu)
        qed (use 3 Some in \<open>auto simp add: fu split: term.splits option.splits if_split\<close>)
      next
      case (Bv n)
        then show ?thesis
        proof(cases f)
          case (Abs B b)
          then show ?thesis 
            by (metis (no_types, lifting) "3.IH" "3.prems" Core.subst_bv_def Core.term.simps(29)
                Core.term.simps(30) beta converse_rtranclp_into_rtranclp fu)
        qed (use 3 Some in \<open>auto simp add: fu split: term.splits option.splits if_split\<close>)
      next
        case (Abs T t)
        then show ?thesis 
        proof(cases f)
          case (Ct n C)
          show ?thesis
            by (metis "3.IH" Abs Core.term.simps(11) Ct Some beta_reducible.simps(7) 
                beta_step_imp_beta_reducible converse_rtranclpE)
        next
          case (Fv n C)
          then show ?thesis 
            by (metis "3.IH" Abs Fv Some beta_reducible.simps(1,4,8) beta_step_imp_beta_reducible 
                converse_rtranclpE)
        next
          case (Bv n)
          then show ?thesis 
            by (metis "3.IH" Abs Some beta_cases(1) converse_rtranclpE term.distinct(15))
        next
          case (Abs B b)
          then show ?thesis
            by (metis (no_types, lifting) "3.IH" "3.prems" Core.subst_bv_def Core.term.simps(29)
                Core.term.simps(30) beta converse_rtranclp_into_rtranclp fu)
        next
          case (App a b)
          then show ?thesis
            using 3 apply (simp add: fu Some split: term.splits option.splits if_splits; fast?)
            by (metis Core.subst_bv_def beta converse_rtranclp_into_rtranclp rtrancl_beta_AppL rtranclp_trans)
        qed
      next
        case AppO: (App f u)
        then show ?thesis 
        proof(cases f)
          case (Ct n C)
          show ?thesis 
            using 3 Some apply (simp add: Ct AppO fu split: term.splits option.splits if_split; fast?)
            by (metis Core.subst_bv_def beta converse_rtranclp_into_rtranclp)
        next
          case (Fv n C)
          then show ?thesis 
            using 3 Some apply (simp add: Fv AppO fu split: term.splits option.splits if_split; fast?)
            by (metis Core.subst_bv_def beta converse_rtranclp_into_rtranclp)
        next
          case (Bv n)
          then show ?thesis 
            using 3 Some apply (simp add: Bv AppO fu split: term.splits option.splits if_split; fast?)
            by (metis Core.subst_bv_def beta converse_rtranclp_into_rtranclp)
        next
          case (Abs B b)
          then show ?thesis 
            using 3 Some apply (simp add: Abs AppO fu split: term.splits option.splits if_split; fast?)
            by (metis Core.subst_bv_def beta converse_rtranclp_into_rtranclp)
        next
          case (App a b)
          then show ?thesis 
            using 3 Some apply (simp add: App AppO fu split: term.splits option.splits if_split; fast?)
            by (metis Core.subst_bv_def beta converse_rtranclp_into_rtranclp)
        qed
      qed
    qed 
  qed auto
qed

corollary "beta_norm t = Some t' \<Longrightarrow> typ_of1 Ts t = Some T \<Longrightarrow> typ_of1 Ts t' = Some T"
  using beta_norm_imp_beta_reds beta_star_preserves_typ_of1 by blast
  
lemma beta_imp_beta_norm: assumes "t \<rightarrow>\<^sub>\<beta> t'" "\<not> beta_reducible t'" shows "beta_norm t = Some t'"
  using assms proof (induction rule: beta.induct)
  case (beta T s t)
  then show ?case using not_beta_reducible_imp_beta_norm_unchanged by (auto simp add: subst_bv_def substn_subst_n) 
next
  case (appL s t u)
  hence t: "\<not> beta_reducible t" by (fastforce elim: beta_reducible.elims)
  hence IH: "beta_norm s = Some t" using appL.IH by simp 
  from appL have u: "\<not> beta_reducible u"
    using beta_reducible.elims by blast
  show ?case 
    apply (cases s; cases t) 
    using not_beta_reducible_imp_beta_norm_unchanged IH t u appL.prems by auto
next
  case (appR s t u)
  hence t: "\<not> beta_reducible t" 
    using beta_reducible.elims by blast
  hence IH: "beta_norm s = Some t" using appR.IH by simp 
  from appR have u: "\<not> beta_reducible u"
    using beta_reducible.elims by blast
  show ?case 
    apply (cases s; cases u)
    using not_beta_reducible_imp_beta_norm_unchanged IH t u appR.prems by auto
next
  case (abs s t T)
  then show ?case by auto
qed

lemma beta_subst_bv1: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> subst_bv1 s lev x \<rightarrow>\<^sub>\<beta> subst_bv1 t lev x"
proof (induction s t arbitrary: lev rule: beta.induct)
  case (beta T s t)
  then show ?case
    using beta.beta subst_bv2_preserves_beta substn_subst_n by presburger
qed (auto simp add: subst_bv_def)

lemma beta_subst_bv: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> subst_bv x s \<rightarrow>\<^sub>\<beta> subst_bv x t"
  by (simp add: substn_subst_0')

(* typ_of to exclude terms like Bv 0 $ Bv 0
  Probably can get rid of one typ_of somehow

  Problem: Not useable for subst_bv (at lev 0)
*)
lemma subst_bv1_beta:
  "subst_bv1 s (length (T#Ts)) x \<rightarrow>\<^sub>\<beta> subst_bv1 t (length (T#Ts)) x 
  \<Longrightarrow> typ_of1 Ts s = Some ty
  \<Longrightarrow> typ_of1 Ts t = Some ty
  \<Longrightarrow> s \<rightarrow>\<^sub>\<beta> t" 
proof (induction "subst_bv1 s (length (T#Ts)) x" "subst_bv1 t (length (T#Ts)) x"
    arbitrary: s t T T Ts ty rule: beta.induct)
  case (beta T s t)
  then show ?case
    by (metis beta.simps length_Cons loose_bvar_Suc no_loose_bvar_imp_no_subst_bv1 typ_of1_imp_no_loose_bvar)
next
  case (appL s t u)
  then show ?case 
    by (metis beta.appL length_Cons loose_bvar_Suc no_loose_bvar_imp_no_subst_bv1 typ_of1_imp_no_loose_bvar)
next
  case (appR s t u)
  then show ?case 
    by (metis beta.simps length_Cons loose_bvar_Suc no_loose_bvar_imp_no_subst_bv1 typ_of1_imp_no_loose_bvar)
next
  case (abs s t bT sa ta T Ts rT )
  obtain s' where "Abs bT s' = sa" 
    using abs.hyps(3) abs.prems loose_bvar_Suc no_loose_bvar_imp_no_subst_bv1 typ_of1_imp_no_loose_bvar 
    by (metis length_Cons)
  moreover obtain t' where "Abs bT t' = ta" 
    using abs.hyps(4) abs.prems loose_bvar_Suc no_loose_bvar_imp_no_subst_bv1 typ_of1_imp_no_loose_bvar 
    by (metis length_Cons)
  ultimately have "s' \<rightarrow>\<^sub>\<beta> t'" 
    by (metis abs.hyps(1) abs.hyps(3) abs.hyps(4) abs.prems(1) abs.prems(2) length_Cons 
        loose_bvar_Suc no_loose_bvar_imp_no_subst_bv1 term.inject(4) typ_of1_imp_no_loose_bvar)
  then show ?case
    using \<open>Abs bT s' = sa\<close> \<open>Abs bT t' = ta\<close> by blast
qed

(* Longterm: Move to Term and unify with subst_bv2, so far only used for beta reduction *)
fun subst_bvs1' :: "term \<Rightarrow> nat \<Rightarrow> term list \<Rightarrow> term" where
  "subst_bvs1' (Bv i) lev args = (if i < lev then Bv i
    else if i - lev < length args then (nth args (i-lev))
    else Bv (i - length args))" 
| "subst_bvs1' (Abs T body) lev args = Abs T (subst_bvs1' body (lev + 1) (map (\<lambda>t. lift t 0) args))"
| "subst_bvs1' (f $ t) lev u = subst_bvs1' f lev u $ subst_bvs1' t lev u"
| "subst_bvs1' t _ _ = t"

lemma subst_bvs1'_empty [simp]: "subst_bvs1' t lev [] = t"
  by (induction t lev "[]::term list" rule: subst_bvs1.induct)auto

lemma subst_bvs1'_eq [simp]: "args \<noteq> [] \<Longrightarrow> subst_bvs1' (Bv k) k args = args ! 0"
  by simp
lemma subst_bvs1'_eq' [simp]: "i < length args \<Longrightarrow> subst_bvs1' (Bv (k+i)) k args = args ! i"
  by auto

lemma subst_bvs1'_gt [simp]: 
  "i + length args < j \<Longrightarrow> subst_bvs1' (Bv j) i args = Bv (j - length args)"
  by auto

lemma subst_bv2_lt [simp]: "j < i \<Longrightarrow> subst_bvs1' (Bv j) i u = Bv j"
  by simp

lemma subst_bvs1'_App[simp]: "subst_bvs1' (s$t) k args
  = subst_bvs1' s k args $ subst_bvs1' t k args"
  by simp

lemma incr_bv_incr_bv:
    "i < k + 1 \<Longrightarrow> incr_bv inc2 (k+inc1) (incr_bv inc1 i t) = incr_bv inc1 i (incr_bv inc2 k t)"
proof (induction t arbitrary: i k)
  case (Abs T t)
  then show ?case
    by (metis Suc_eq_plus1 add_Suc add_mono1 incr_bv.simps(2))
qed auto

lemma subst_bvs1_subst_bvs1': "subst_bvs1 t n s = subst_bvs1' t n (map (incr_bv n 0) s)"
proof (induction t arbitrary: n)
  case (Abs T t)
  then show ?case 
    by (simp add: incr_boundvars_def incr_bv_combine) 
      (metis One_nat_def comp_apply incr_bv_combine plus_1_eq_Suc)
qed (auto simp add: incr_boundvars_def incr_bv_combine)

theorem subst_bvs1_subst_bvs1'_0: "subst_bvs1 t 0 s = subst_bvs1' t 0 s"
proof-
  have "subst_bvs1 t 0 s = subst_bvs1' t 0 (map (incr_bv 0 0) s)"
    using subst_bvs1_subst_bvs1' by blast
  moreover have "map (incr_bv 0 0) s = s" 
    by (induction s) auto
  ultimately show ?thesis
    by simp
qed

corollary subst_bvs_subst_bvs1': "subst_bvs s t = subst_bvs1' t 0 s"
  using subst_bvs_def subst_bvs1_subst_bvs1'_0 by simp

lemma no_loose_bvar_subst_bvs1'_unchanged: "\<not> loose_bvar t lev \<Longrightarrow> subst_bvs1' t lev args = t"
  by (induction t lev args rule: subst_bvs1'.induct) auto

(* This is enough when just substituting variables, however in the \<beta> case I will have to
  distribute subst_bvs through a single subst_bv(where the substituted term is not a var).
*)
lemma subst_bvs1'_step: "\<forall>x \<in> set (a#args) . is_closed x \<Longrightarrow>
  subst_bvs1' t lev (a#args) = subst_bvs1' (subst_bv2 t lev a) lev args"  
proof (induction t lev args rule: subst_bvs1'.induct)
  case (1 i lev args)
  then show ?case 
    using no_loose_bvar_subst_bvs1'_unchanged
    by (simp add: is_open_def) 
      (metis Suc_diff_Suc le_add1 le_add_same_cancel1 less_antisym loose_bvar_leq not_less_eq)
qed (auto simp add: is_open_def)

lemma not_loose_bvar_incr_bv: "\<not> loose_bvar a lev \<Longrightarrow> \<not> loose_bvar (incr_bv inc lev a) (lev+inc)"
  by (induction a lev rule: loose_bvar.induct) auto

lemma not_loose_bvar_incr_bv_less: 
  "i < j \<Longrightarrow> \<not> loose_bvar (incr_bv inc i a) (lev+inc) \<Longrightarrow> \<not> loose_bvar (incr_bv inc j a) (lev+inc)"
proof (induction inc i a arbitrary: lev j rule: incr_bv.induct)
  case (2 inc n T body)
  then show ?case
    by (metis Suc_eq_plus1 add_Suc add_mono1 incr_bv.simps(2) loose_bvar.simps(3))
qed (auto split: if_splits)

lemma subst_bvs1'_step_work: "\<forall>x \<in> set args . is_closed x \<Longrightarrow> \<not> loose_bvar (subst_bv2 t lev a) lev \<Longrightarrow>
  subst_bvs1' t lev (a#args) = subst_bvs1' (subst_bv2 t lev a) lev args"  
proof (induction t "lev" "args" arbitrary: a rule: subst_bvs1'.induct)
  case (1 i )
  then show ?case using no_loose_bvar_subst_bvs1'_unchanged
    by (auto simp add: is_open_def)
next
  case (2 T body lev args)
  then show ?case using no_loose_bvar_subst_bvs1'_unchanged
    by (auto simp add: is_open_def) 
next
  case (3 f t lev u)
  then show ?case using no_loose_bvar_subst_bvs1'_unchanged
    by (auto simp add: is_open_def)
next
  case ("4_1" v va uu uv)
  then show ?case using no_loose_bvar_subst_bvs1'_unchanged
    by (auto simp add: is_open_def)
next
  case ("4_2" v va uu uv)
  then show ?case using no_loose_bvar_subst_bvs1'_unchanged
    by (auto simp add: is_open_def)
qed

lemma is_closed_subst_bv2_unchanged: "is_closed t \<Longrightarrow> subst_bv2 t n u = t"
  by (metis is_open_def lift_def loose_bvar_Suc no_loose_bvar_no_incr subst_bv2_lift zero_induct)

(* This might do it, should be able to connect a new substitution to the pushed in one *)
lemma subst_bvs1'_step_extend_lower_level: "\<forall>x \<in> set (a#args) . is_closed x \<Longrightarrow>
  subst_bv2 (subst_bvs1' t (Suc lev) args) lev a
    = subst_bvs1' t lev (a#args)" 
proof (induction t lev "a#args" arbitrary: a args rule: subst_bvs1'.induct)
  case (1 i lev)
  have "subst_bv2 (subst_bvs1' (Bv i) (Suc lev) args) lev a =
    subst_bvs1' (Bv i) lev (a # args)"
    if "i < Suc lev"
    using that by auto
  moreover have "subst_bv2 (subst_bvs1' (Bv i) (Suc lev) args) lev a =
    subst_bvs1' (Bv i) lev (a # args)"
    if "i - Suc lev < length args" "\<not> i < Suc lev"
  proof-
    have "subst_bv2 (subst_bvs1' (Bv i) (Suc lev) args) lev a = subst_bv2 (args ! (i - Suc lev)) lev a" 
      using that by simp
    also have "\<dots> = args ! (i - Suc lev)" 
      using 1 that(1) by (auto simp add: is_closed_subst_bv2_unchanged)
    also have "subst_bvs1' (Bv i) lev (a # args) = args ! (i - Suc lev)" 
      using that by auto
    finally show ?thesis 
      by simp
  qed
  moreover have "subst_bv2(subst_bvs1' (Bv i) (Suc lev) args) lev a =
    subst_bvs1' (Bv i) lev (a # args)"
    if "i \<ge> Suc lev" "i - lev \<ge> length args" "\<not> i < Suc lev"
    using that 1 by (auto simp add: is_closed_subst_bv2_unchanged) 
  ultimately show ?case by (auto simp add: is_open_def split: if_splits)
qed (auto simp add: is_open_def)

corollary subst_bvs_extend_lower_level:
  "\<forall>x \<in> set (a#args) . is_closed x \<Longrightarrow>
  subst_bv a (subst_bvs1' t 1 args) = subst_bvs (a#args) t" 
  using subst_bvs1'_step_extend_lower_level 
  by (simp add: subst_bvs_subst_bvs1' substn_subst_0')

lemma subst_bvs1'_preserves_beta:
  "\<forall>x \<in> set u . is_closed x \<Longrightarrow> r \<rightarrow>\<^sub>\<beta> s \<Longrightarrow> subst_bvs1' r k u \<rightarrow>\<^sub>\<beta> subst_bvs1' s k u" 
proof (induction u arbitrary: r s )
  case Nil
  then show ?case by auto
next
  case (Cons a u)
  hence "subst_bv2 r k a \<rightarrow>\<^sub>\<beta> subst_bv2 s k a"
    by simp 
  hence "subst_bvs1' (subst_bv2 r k a) k u \<rightarrow>\<^sub>\<beta> subst_bvs1' (subst_bv2 s k a) k u"
    using Cons by simp 
  then show ?case 
    by (simp add: subst_bvs1'_step[symmetric] Cons.prems(1))
qed

lemma subst_bvs1'_fold: "\<forall>x \<in> set args . is_closed x \<Longrightarrow>
  subst_bvs1' t lev args = fold (\<lambda>arg t . subst_bv2 t lev arg) args t"  
  by (induction args arbitrary: t) (simp_all add: subst_bvs1'_step)

lemma subst_bvs1'_Abs[simp]: "\<forall>x \<in> set args . is_closed x \<Longrightarrow>
  subst_bvs1' (Abs T t) lev args = Abs T (subst_bvs1' t (Suc lev) args)"
  by (simp add: is_open_def map_idI)

lemma subst_bvs_Abs[simp]: "\<forall>x \<in> set args . is_closed x \<Longrightarrow>
  subst_bvs args (Abs T t) = Abs T (subst_bvs1' t 1 args)"
  using subst_bvs1'_Abs subst_bvs_subst_bvs1'  by auto

lemma subst_bvs1'_incr_bv [simp]:
    "subst_bvs1' (incr_bv (length ss) k t) k ss = t"
proof (induct t arbitrary: k ss)
  case (Abs T t)
  then show ?case
    by simp (metis length_map)
qed auto

lemma lift_subst_bvs1' [simp]:
    "j < i + 1 \<Longrightarrow> lift (subst_bvs1' t j ss) i 
    = subst_bvs1' (lift t (i + length ss)) j (map (\<lambda>s . lift s i) ss)"
proof (induct  t arbitrary: i j ss)
  case (Abs T t)
  hence I: "lift (subst_bvs1' t (Suc j) (map (\<lambda>t. lift t 0) ss)) (Suc i) =
    subst_bvs1' (lift t (Suc i + length (map (\<lambda>t. lift t 0) ss))) (Suc j) (map (\<lambda>a. lift a (Suc i)) (map (\<lambda>t. lift t 0) ss))"
    by auto

  have "lift (subst_bvs1' (Abs T t) j ss) i 
    = Abs T (lift (subst_bvs1' t (Suc j) (map (\<lambda>t. lift t 0) ss)) (Suc i))"
    by simp
  also have "\<dots> = Abs T
     (subst_bvs1' (lift t (Suc i + length (map (incr_bv 1 0) ss))) (Suc j)
       (map (incr_bv 1 (Suc i)) (map (incr_bv 1 0) ss)))" 
    using I by auto
  also have "\<dots> = Abs T
     (subst_bvs1' (lift t (Suc i + length (map (incr_bv 1 0) ss))) (Suc j)
       (map (\<lambda>t. lift t 0) (map (\<lambda>t. lift t i) ss)))" 
  proof-
    have "map (\<lambda>t . lift t (Suc i)) (map (\<lambda>t. lift t 0) ss) = map (\<lambda>t. lift t 0) (map (\<lambda>t. lift t i) ss)"
      using lift_lift by auto
    thus ?thesis unfolding lift_def
      by argo
  qed
  also have "\<dots> = subst_bvs1' (Abs T (lift t (Suc i + length (map (incr_bv 1 0) ss)))) j
       (map (\<lambda>t. lift t i) ss)"
    by auto
  finally show ?case
    by simp
qed (auto simp add: diff_Suc lift_lift split: nat.split)

lemma lift_subst_bvs1'_lt:
    "i < j + 1 \<Longrightarrow> lift (subst_bvs1' t j ss) i 
  = subst_bvs1' (lift t i) (j + 1) (map (\<lambda>s . lift s i) ss)"
proof (induct t arbitrary: i j ss)
  case (Abs T t)
  then show ?case using lift_lift 
    by simp (smt comp_apply map_eq_conv zero_less_Suc)
qed auto

lemma subst_bvs1'_subst_bv2:
  "i < j + 1 \<Longrightarrow> 
    subst_bv2(subst_bvs1' t (Suc j) (map (\<lambda>v. lift v i) vs)) i (subst_bvs1' u j vs) 
    = subst_bvs1' (subst_bv2 t i u) j vs"
proof(induction t arbitrary: i j u vs)
  case (Abs T t)
  then show ?case
    by simp (smt One_nat_def Suc_eq_plus1 Suc_less_eq comp_apply lift_lift lift_def
        lift_subst_bvs1'_lt map_eq_conv map_map zero_less_Suc)
qed (use subst_bv2_lift in auto)

lemma fv_subst_bv2_upper_bound: "fv (subst_bv2 t lev u) \<subseteq> fv t \<union> fv u"
  by (induction t lev u rule: subst_bv2.induct) auto
lemma beta_fv: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> fv t \<subseteq> fv s"
  by (induction rule: beta.induct) (use fv_subst_bv2_upper_bound in auto)

lemma loose_bvar1_subst_bvs1'_closeds: "\<not> loose_bvar1 t lev \<Longrightarrow> lev < k \<Longrightarrow> \<forall>x\<in>set us . is_closed x
  \<Longrightarrow> \<not> loose_bvar1 (subst_bvs1' t k us) lev"
  by (induction t k us arbitrary: lev rule: subst_bvs1'.induct)
    (use is_open_def loose_bvar_iff_exist_loose_bvar1 in \<open>auto simp add: is_open_def\<close>)

lemma is_closed_subst_bvs1'_closeds: "\<not> is_dependent t \<Longrightarrow> \<forall>x\<in>set us . is_closed x
  \<Longrightarrow> \<not> is_dependent (subst_bvs1' t (Suc k) us)"
  by (simp add: is_dependent_def loose_bvar1_subst_bvs1'_closeds)

end
