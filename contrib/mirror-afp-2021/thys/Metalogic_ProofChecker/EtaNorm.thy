section "Eta Normalization"

theory EtaNorm
  imports Term BetaNorm
begin
(* Again from Lambda calculus from @{dir "~~/src/HOL/Proofs/Lambda"} and modified*)

inductive
  eta :: "term \<Rightarrow> term \<Rightarrow> bool"  (infixl "\<rightarrow>\<^sub>\<eta>" 50)
where
    eta [simp, intro]: "\<not> is_dependent s \<Longrightarrow> Abs T (s $ Bv 0) \<rightarrow>\<^sub>\<eta> decr 0 s"
  | appL [simp, intro]: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> s $ u \<rightarrow>\<^sub>\<eta> t $ u"
  | appR [simp, intro]: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> u $ s \<rightarrow>\<^sub>\<eta> u $ t"
  | abs [simp, intro]: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> Abs T s \<rightarrow>\<^sub>\<eta> Abs T t"

abbreviation
  eta_reds :: "term \<Rightarrow> term \<Rightarrow> bool"   (infixl "\<rightarrow>\<^sub>\<eta>\<^sup>*" 50) where
  "s \<rightarrow>\<^sub>\<eta>\<^sup>* t \<equiv> eta\<^sup>*\<^sup>* s t"

abbreviation
  eta_red0 :: "term \<Rightarrow> term \<Rightarrow> bool"   (infixl "\<rightarrow>\<^sub>\<eta>\<^sup>=" 50) where
  "s \<rightarrow>\<^sub>\<eta>\<^sup>= t \<equiv> eta\<^sup>=\<^sup>= s t"

inductive_cases eta_cases [elim!]:
  "Abs T s \<rightarrow>\<^sub>\<eta> z"
  "s $ t \<rightarrow>\<^sub>\<eta> u"
  "Bv i \<rightarrow>\<^sub>\<eta> t"

lemma subst_bv2_not_free [simp]: "\<not> loose_bvar1 s i \<Longrightarrow> subst_bv2 s i t = subst_bv2 s i u"
  by (induction s arbitrary: i t u) (simp_all add:)

lemma free_lift [simp]:
    "loose_bvar1 (lift t k) i = (i < k \<and> loose_bvar1 t i \<or> k < i \<and> loose_bvar1 t (i - 1))"
  by (induct t arbitrary: i k) (auto cong: conj_cong)

lemma free_subst_bv2 [simp]:
    "loose_bvar1 (subst_bv2 s k t) i =
      (loose_bvar1 s k \<and> loose_bvar1 t i \<or> loose_bvar1 s (if i < k then i else i + 1))"
  apply (induct s arbitrary: i k t)
  using free_lift apply (simp_all add: diff_Suc split: nat.split) 
  by blast

lemma free_eta: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> loose_bvar1 t i = loose_bvar1 s i"
  apply (induct arbitrary: i set: eta) 
  apply (simp_all cong: conj_cong)
  using is_dependent_def loose_bvar1_decr''' loose_bvar1_decr'''' by blast

lemma not_free_eta:
    "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> \<not> loose_bvar1 s i \<Longrightarrow> \<not> loose_bvar1 t i"
  by (simp add: free_eta)

lemma no_loose_bvar1_subst_bv2_decr: "\<not> loose_bvar1 t i \<Longrightarrow> subst_bv2 t i x = decr i t"
  by (induction t i x rule: subst_bv2.induct) auto

lemma eta_subst_bv2 [simp]:
    "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> subst_bv2 s i u \<rightarrow>\<^sub>\<eta> subst_bv2 t i u"
proof (induction s t arbitrary: u i rule: eta.induct)
  case (eta s T)
  hence 1: "\<not> loose_bvar1 s 0" 
    using is_dependent_def by simp
  have "decr 0 s = subst_bv2 s 0 dummy" for dummy 
    using no_loose_bvar1_subst_bv2_decr[symmetric, OF 1, of dummy] .
  from this obtain dummy where dummy: "decr 0 s = subst_bv2 s 0 dummy"
    by simp

  show ?case 
    using 1 apply (simp add: dummy subst_bv2_subst_bv2 [symmetric])
    using free_lift is_dependent_def no_loose_bvar1_subst_bv2_decr by auto
qed auto

theorem lift_subst_bv2_dummy: "\<not> loose_bvar s i \<Longrightarrow> lift (decr i s) i = s"
  by (induct s arbitrary: i) simp_all

lemma decr_is_closed[simp]: "is_closed t \<Longrightarrow> decr lev t = t"
  by (metis is_open_def lift_subst_bv2_dummy lift_def loose_bvar_Suc loose_bvar_incr_bvar no_loose_bvar_no_incr zero_induct)

lemma eta_reducible_imp_eta_step: "eta_reducible t \<Longrightarrow> \<exists>t'. t \<rightarrow>\<^sub>\<eta> t'" 
  by (induction t rule: eta_reducible.induct) auto

lemma eta_step_imp_eta_reducible: "t \<rightarrow>\<^sub>\<eta> t' \<Longrightarrow> eta_reducible t" 
proof (induction t t' rule: eta.induct)
  case (abs s t T)
  show ?case
  proof(cases s)
    case (App u v)
    then show ?thesis by (cases v; use abs eta_reducible_Abs in metis)
  qed (use abs in auto)
qed auto

lemma eta_reds_appR: "s \<rightarrow>\<^sub>\<eta>\<^sup>* t \<Longrightarrow> u $ s \<rightarrow>\<^sub>\<eta>\<^sup>* u $ t"
  by (induction s t rule: rtranclp.induct) (auto simp add: rtranclp.rtrancl_into_rtrancl)
lemma eta_reds_appL: "s \<rightarrow>\<^sub>\<eta>\<^sup>* t \<Longrightarrow> s $ u \<rightarrow>\<^sub>\<eta>\<^sup>* t $ u"
  by (induction s t rule: rtranclp.induct) (auto simp add: rtranclp.rtrancl_into_rtrancl)
lemma eta_reds_abs: "s \<rightarrow>\<^sub>\<eta>\<^sup>* t \<Longrightarrow> Abs T s \<rightarrow>\<^sub>\<eta>\<^sup>* Abs T t"
  by (induction s t rule: rtranclp.induct) (auto simp add: rtranclp.rtrancl_into_rtrancl)

lemma eta_norm_imp_eta_reds: assumes "eta_norm t = t'" shows "t \<rightarrow>\<^sub>\<eta>\<^sup>* t'"
using assms proof (induction t arbitrary: t' rule: eta_norm.induct)
  case (1 T body)
  then show ?case
  proof (cases "eta_norm body")
    case (App f u)
    then show ?thesis
      using 1 apply (clarsimp simp add: is_dependent_def eta_reds_abs split: term.splits nat.splits if_splits)
      by (metis eta.eta eta_reds_abs eta_reducible.simps(11) is_dependent_def 
          not_eta_reducible_eta_norm not_eta_reducible_imp_eta_norm_no_change rtranclp.simps)
  qed (auto simp add: is_dependent_def eta_reds_abs split: term.splits nat.splits if_splits)
next
  case (2 f u)
  hence "f \<rightarrow>\<^sub>\<eta>\<^sup>* eta_norm f" "u \<rightarrow>\<^sub>\<eta>\<^sup>* eta_norm u"
    by simp_all
  then show ?case using 2
    by (metis eta_norm.simps(2) eta_reds_appL eta_reds_appR rtranclp_trans)
qed auto

lemma rtrancl_eta_App:
    "s \<rightarrow>\<^sub>\<eta>\<^sup>* s' \<Longrightarrow> t \<rightarrow>\<^sub>\<eta>\<^sup>* t' \<Longrightarrow> s $ t \<rightarrow>\<^sub>\<eta>\<^sup>* s' $ t'"
  by (blast intro!: eta_reds_appR eta_reds_appL intro: rtranclp_trans)

lemma eta_preserves_typ_of1: "t \<rightarrow>\<^sub>\<eta> t' \<Longrightarrow> typ_of1 Ts t = Some \<tau> \<Longrightarrow> typ_of1 Ts t' = Some \<tau>"
proof (induction Ts t arbitrary: \<tau> t' rule: typ_of1.induct)
  case (1 uu uv T)
  then show ?case
    using eta_step_imp_eta_reducible by fastforce
next
  case (2 Ts i)
  then show ?case 
    using eta_step_imp_eta_reducible by fastforce
next
  case (3 uw ux T)
  then show ?case 
    using eta_step_imp_eta_reducible by fastforce
next
  case (4 Ts T body)
  then show ?case 
  proof(cases body)
    case (Abs B b)
    then show ?thesis using 4
      by (metis eta_cases(1) term.distinct(19) typ_of1.simps(4) typ_of_Abs_body_typ')
  next
    case (App u v)
    note oApp = App
    then show ?thesis
    proof(cases "is_dependent u")
      case True
      then show ?thesis
        by (metis "4.IH" "4.prems"(1) "4.prems"(2) App eta_cases(1) term.inject(5) 
            typ_of1.simps(4) typ_of_Abs_body_typ')
    next
      case False
      then show ?thesis
      proof(cases v)
        case (Ct n T)
        then show ?thesis
          using 4 oApp False typ_of_Abs_body_typ'
          by (metis eta_cases(1) term.distinct(3) term.inject(5) typ_of1.simps(4))
      next
        case (Fv n T)
        then show ?thesis 
          using 4 oApp False typ_of_Abs_body_typ' 
          by (metis eta_cases(1) term.distinct(9) term.inject(5) typ_of1.simps(4))
      next
        case (Bv n)
        then show ?thesis 
        proof(cases n)
          case 0 thm 4
          show ?thesis
          proof(cases rule: eta_cases(1)[OF "4.prems"(1)])
            case (1 s)
            thm "4"(3)
            obtain rty where "typ_of1 (T#Ts) (s $ Bv 0) = Some (rty)"
              using typ_of_Abs_body_typ'[OF "4"(3)] "1"(3) "1"(1) by blast
            moreover have "\<tau> = T \<rightarrow> rty"
              by (metis "1"(1) "4.prems"(2) calculation option.inject typ_of_Abs_body_typ')
            ultimately have "typ_of1 (T#Ts) s = Some \<tau>"
              using typ_of1_arg_typ
              by (metis length_Cons nth_Cons_0 typ_of1.simps(2) zero_less_Suc)
            hence "typ_of1 Ts (decr 0 s) = Some \<tau>"
              by (metis "1"(3) append_Cons append_Nil is_dependent_def list.size(3) typ_of1_decr)
            then show ?thesis 
              using 1 oApp False typ_of_Abs_body_typ' Bv 0 by auto
          next
            case (2 t)
            then show ?thesis  
              using oApp False typ_of_Abs_body_typ' Bv 0
              by (metis "4.IH" "4.prems"(2) typ_of1.simps(4))
          qed
        next
          case (Suc nat)
          then show ?thesis 
            using 4 oApp False typ_of_Abs_body_typ' Bv 
            apply -
            apply (rule eta_cases(1)[of T body t'])
            apply blast
            apply blast
            apply (metis "4.IH" "4.prems"(2) typ_of1.simps(4))
            done
        qed
      next
        case (Abs T t)
        then show ?thesis 
          using 4 oApp False typ_of_Abs_body_typ'
          (* Help metis a bit *)
          apply -
          apply (erule eta.cases(1))
          by (metis term.distinct(15) term.distinct(19) term.inject(4) term.inject(5)
              typ_of1.simps(4))+
      next
        case (App f u)
        then show ?thesis 
          using 4 oApp False typ_of_Abs_body_typ'
          by (metis eta_cases(1) term.distinct(17) term.inject(5) typ_of1.simps(4))
      qed
    qed
  qed (use 4 in auto)
next
  case (5 Ts f u)
  then show ?case
    by (smt bind.bind_lunit eta_cases(2) typ_of1.simps(5) typ_of1_split_App_obtains)
qed

lemma eta_preserves_typ_of: "t \<rightarrow>\<^sub>\<eta> t' \<Longrightarrow> typ_of t = Some \<tau> \<Longrightarrow> typ_of t' = Some \<tau>"
  using eta_preserves_typ_of1 typ_of_def by simp


lemma eta_star_preserves_typ_of1: "r \<rightarrow>\<^sub>\<eta>\<^sup>* s \<Longrightarrow> typ_of1 Ts r = Some T  \<Longrightarrow> typ_of1 Ts s = Some T"
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case 
    by simp
next
  case (rtrancl_into_rtrancl a b c)
  then show ?case
    using eta_preserves_typ_of1 by blast
qed

lemma eta_star_preserves_typ_of: "r \<rightarrow>\<^sub>\<eta>\<^sup>* s \<Longrightarrow> typ_of r = Some T  \<Longrightarrow> typ_of s = Some T"
  using eta_star_preserves_typ_of1 typ_of_def by simp

lemma subst_bvs1'_decr: "\<forall>x\<in>set us. is_closed x  \<Longrightarrow> \<not> loose_bvar1 t k 
  \<Longrightarrow> subst_bvs1' (decr k t) k us = decr k (subst_bvs1' t (Suc k) us)"
  by (induction k t arbitrary: us rule: decr.induct) (auto simp add: is_open_def)

lemma subst_bvs_decr: "\<forall>x\<in>set us. is_closed x  \<Longrightarrow> \<not> is_dependent t
  \<Longrightarrow> subst_bvs us (decr 0 t) = decr 0 (subst_bvs1' t 1 us)"
  by (simp add: is_dependent_def subst_bvs1'_decr subst_bvs_subst_bvs1')

end
