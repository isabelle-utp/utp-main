section "Logic"

theory Logic            
  imports Theory Term_Subst SortConstants Name BetaNormProof EtaNormProof
begin

term proves

abbreviation "inst_ok \<Theta> insts \<equiv> 
    distinct (map fst insts) \<comment>\<open>No duplicates, makes stuff easier\<close>
  \<and> list_all (typ_ok \<Theta>) (map snd insts) \<comment>\<open>Stuff I substitute in is well typed\<close>
  \<and> list_all (\<lambda>((idn, S), T) . has_sort (osig (sig \<Theta>)) T S) insts" \<comment>\<open>Types "fit" in the Fviables\<close>

lemma inst_ok_imp_wf_inst: 
    "inst_ok \<Theta> insts \<Longrightarrow> wf_inst \<Theta> (\<lambda>idn S .the_default (Tv idn S) (lookup (\<lambda>x. x=(idn, S)) insts))"
  by (induction insts) (auto split: if_splits prod.splits)

lemma term_ok'_eta_norm: "term_ok' \<Sigma> t \<Longrightarrow> term_ok' \<Sigma> (eta_norm t)"
  by (induction t rule: eta_norm.induct)
    (auto split: term.splits nat.splits simp add: term_ok'_decr is_dependent_def)
corollary term_ok_eta_norm: "term_ok thy t \<Longrightarrow> term_ok thy (eta_norm t)"
  using wt_term_def typ_of_eta_norm term_ok'_eta_norm by auto

abbreviation "beta_eta_norm t \<equiv> map_option eta_norm (beta_norm t)"

lemma "beta_eta_norm t = Some t' \<Longrightarrow> \<not> eta_reducible t'"
  using not_eta_reducible_eta_norm by auto
lemma term_ok_beta_eta_norm: "term_ok thy t \<Longrightarrow> beta_eta_norm t = Some t' \<Longrightarrow> term_ok thy t'"
  using term_ok_eta_norm term_ok_beta_norm by blast
lemma typ_of_beta_eta_norm:
  "typ_of t = Some T \<Longrightarrow> beta_eta_norm t = Some t' \<Longrightarrow> typ_of t' = Some T"
  using beta_norm_imp_beta_reds beta_star_preserves_typ_of1 typ_of1_eta_norm typ_of_def by fastforce

lemma inst_ok_nil[simp]: "inst_ok \<Theta> []" by simp

lemma axiom_subst_typ': 
  assumes "wf_theory \<Theta>" "A\<in>axioms \<Theta>" "inst_ok \<Theta> insts"
  shows "\<Theta>, \<Gamma> \<turnstile> subst_typ' insts A"
proof-
  have "wf_inst \<Theta> (\<lambda>idn S . the_default (Tv idn S) (lookup (\<lambda>x. x=(idn, S)) insts))"
    using inst_ok_imp_wf_inst assms(3) by blast
  moreover have "subst_typ' insts A
    = tsubst A (\<lambda>idn S . the_default (Tv idn S) (lookup (\<lambda>x. x=(idn, S)) insts))"
    by (simp add: tsubst_simulates_subst_typ')
  ultimately show ?thesis
    using assms axiom by simp
qed

corollary axiom': "wf_theory \<Theta> \<Longrightarrow> A \<in> axioms \<Theta> \<Longrightarrow> \<Theta>, \<Gamma> \<turnstile> A"
  apply (subst subst_typ'_nil[symmetric])
  using axiom_subst_typ' inst_ok_nil by metis

lemma has_sort_Tv_refl: "wf_osig oss \<Longrightarrow> sort_ex (subclass oss) S \<Longrightarrow> has_sort oss (Tv v S) S"
  by (cases oss) (simp add: osig_subclass_loc wf_subclass_loc.intro has_sort_Tv wf_subclass_loc.sort_leq_refl)

lemma has_sort_Tv_refl': 
  "wf_theory \<Theta> \<Longrightarrow> typ_ok \<Theta> (Tv v S) \<Longrightarrow> has_sort (osig (sig \<Theta>)) (Tv v S) S"
  using has_sort_Tv_refl
  by (metis wf_sig.simps osig.elims wf_theory_imp_wf_sig typ_ok_def
      wf_type_imp_typ_ok_sig typ_ok_sig.simps(2) wf_sort_def)

lemma wf_inst_imp_inst_ok:
    "wf_theory \<Theta> \<Longrightarrow> distinct l \<Longrightarrow> \<forall>(v, S) \<in> set l . typ_ok \<Theta> (Tv v S) \<Longrightarrow> wf_inst \<Theta> \<rho> 
  \<Longrightarrow> inst_ok \<Theta> (map (\<lambda>(v, S) . ((v, S), \<rho> v S)) l)"
proof (induction l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  have I: "inst_ok \<Theta> (map (\<lambda>(v,S) . ((v, S), \<rho> v S)) l)"
    using Cons by fastforce

  have "a \<notin> set l"
    using Cons.prems(2) by auto
  hence "(a, case_prod \<rho> a) \<notin> set (map (\<lambda>(v,S) . ((v, S), \<rho> v S)) l)"
    by (simp add: image_iff prod.case_eq_if)
  moreover have "distinct (map (\<lambda>(v,S) . ((v, S), \<rho> v S)) l)"
      using I distinct_kv_list distinct_map by fast
  ultimately have "distinct (map (\<lambda>(v,S) . ((v, S), \<rho> v S)) (a#l))"
    by (auto split: prod.splits)

  moreover have "wf_type (sig \<Theta>) (case_prod \<rho> a)"
    using Cons.prems(3-4) by auto (metis typ_ok_Tv wf_type_imp_typ_ok_sig)
  moreover hence "typ_ok \<Theta> (case_prod \<rho> a)"
    by simp
  moreover hence "has_sort (osig (sig \<Theta>)) (case_prod \<rho> a) (snd a)"
    using Cons.prems by (metis (full_types) has_sort_Tv_refl' prod.case_eq_if wf_inst_def)

  ultimately show ?case
    using I by (auto simp del: typ_ok_def split: prod.splits)
qed

(* MOVE to term, also use for transfering proofs *)
lemma typs_of_fv_subset_Types: "snd ` fv t \<subseteq> Types t"
  by (induction t) auto
lemma osig_tvsT_subset_SortsT: "snd ` tvsT T \<subseteq> SortsT T"
  by (induction T) auto
lemma osig_tvs_subset_Sorts: "snd ` tvs t \<subseteq> Sorts t"
  by (induction t) (use osig_tvsT_subset_SortsT in \<open>auto simp add: image_subset_iff\<close>)
  
lemma term_ok_Types_imp_typ_ok_pre:
  "is_std_sig \<Sigma> \<Longrightarrow> term_ok' \<Sigma> t \<Longrightarrow> \<tau> \<in> Types t \<Longrightarrow> typ_ok_sig \<Sigma> \<tau>"
  by (induction t arbitrary: \<tau>) (auto split: option.splits)

lemma term_ok_Types_typ_ok: "wf_theory \<Theta> \<Longrightarrow> term_ok \<Theta> t \<Longrightarrow> \<tau> \<in> Types t \<Longrightarrow> typ_ok \<Theta> \<tau>"
  by (cases \<Theta> rule: theory_full_exhaust) (fastforce simp add: wt_term_def 
      intro: term_ok_Types_imp_typ_ok_pre)

lemma term_ok_fv_imp_typ_ok_pre:
  "is_std_sig \<Sigma> \<Longrightarrow> term_ok' \<Sigma> t \<Longrightarrow> (x,\<tau>) \<in> fv t \<Longrightarrow> typ_ok_sig \<Sigma> \<tau>"
  using typs_of_fv_subset_Types term_ok_Types_imp_typ_ok_pre
  by (metis image_subset_iff snd_conv)

lemma term_ok_vars_typ_ok: "wf_theory \<Theta> \<Longrightarrow> term_ok \<Theta> t \<Longrightarrow> (x, \<tau>) \<in> fv t \<Longrightarrow> typ_ok \<Theta> \<tau>"
   using term_ok_Types_typ_ok typs_of_fv_subset_Types by (metis image_subset_iff snd_conv) 

lemma typ_ok_TFreesT_imp_sort_ok_pre:
  "is_std_sig \<Sigma> \<Longrightarrow> typ_ok_sig \<Sigma> T \<Longrightarrow> (x, S) \<in> tvsT T \<Longrightarrow> wf_sort (subclass (osig \<Sigma>)) S"
proof (induction T)
  case (Ty n Ts)
  then show ?case by (induction Ts) (fastforce dest: split_list split: option.split_asm)+
qed (auto simp add: wf_sort_def) 

lemma term_ok_TFrees_imp_sort_ok_pre:
  "is_std_sig \<Sigma> \<Longrightarrow> term_ok' \<Sigma> t \<Longrightarrow> (x, S) \<in> tvs t \<Longrightarrow> wf_sort (subclass (osig \<Sigma>)) S"
proof (induction t arbitrary: S)
  case (Ct n T)
  then show ?case
    apply (clarsimp split: option.splits)
    by (use typ_ok_TFreesT_imp_sort_ok_pre wf_sort_def in auto)
next
  case (Fv n T)
  then show ?case 
    apply (clarsimp split: option.splits)
    by (use typ_ok_TFreesT_imp_sort_ok_pre wf_sort_def in auto)
next
  case (Bv n)
  then show ?case 
    by (clarsimp split: option.splits)
next
  case (Abs T t)
  then show ?case 
    apply simp
    using typ_ok_TFreesT_imp_sort_ok_pre wf_sort_def
    by meson
next
  case (App t1 t2)
  then show ?case
    by auto
qed 
  
lemma typ_ok_tvsT_imp_sort_ok_pre:
  "is_std_sig \<Sigma> \<Longrightarrow> typ_ok_sig \<Sigma> T \<Longrightarrow> (x,S) \<in> tvsT T \<Longrightarrow> wf_sort (subclass (osig \<Sigma>)) S"
proof (induction T)
  case (Ty n Ts)
  then show ?case by (induction Ts) (fastforce dest: split_list split: option.split_asm)+
qed (auto simp add: wf_sort_def) 

lemma term_ok_tvars_sort_ok:
  assumes "wf_theory \<Theta>" "term_ok \<Theta> t" "(x, S) \<in> tvs t"
  shows "wf_sort (subclass (osig (sig \<Theta>))) S"
proof-
  have "term_ok' (sig \<Theta>) t"
    using assms(2) by (simp add: wt_term_def)
  moreover have "is_std_sig (sig \<Theta>)" 
    using assms by (cases \<Theta> rule: theory_full_exhaust) simp
  ultimately show ?thesis
    using assms(3) term_ok_TFrees_imp_sort_ok_pre by simp
qed

lemma term_ok'_bind_fv2:
  assumes "term_ok' \<Sigma> t"
  shows "term_ok' \<Sigma> (bind_fv2 (v,T) lev t)"
  using assms by (induction "(v,T)" lev t rule: bind_fv2.induct) auto

lemma term_ok'_bind_fv:
  assumes "term_ok' \<Sigma> t"
  shows "term_ok' \<Sigma> (bind_fv (v,\<tau>) t)"
  using term_ok'_bind_fv2 bind_fv_def assms by metis

lemma term_ok'_Abs_fv:
  assumes "term_ok' \<Sigma> t" "typ_ok_sig \<Sigma> \<tau>"
  shows "term_ok' \<Sigma> (Abs \<tau> (bind_fv (v,\<tau>) t))"
  using term_ok'_bind_fv assms by simp

lemma term_ok'_mk_all:
  assumes "wf_theory \<Theta>" and "term_ok' (sig \<Theta>) B" and "typ_of B = Some propT" 
    and "typ_ok \<Theta> \<tau>"
  shows "term_ok' (sig \<Theta>) (mk_all x \<tau> B)"
  using assms term_ok'_bind_fv 
  by (cases \<Theta> rule: wf_theory.cases) (auto simp add: typ_of_def tinstT_def)

lemma term_ok_mk_all:
  assumes "wf_theory \<Theta>" and "term_ok' (sig \<Theta>) B" and "typ_of B = Some propT" and "typ_ok \<Theta> \<tau>"
  shows "term_ok \<Theta> (mk_all x \<tau> B)"
  using typ_of_mk_all term_ok'_mk_all assms by (auto simp add: wt_term_def)

lemma term_ok'_incr_boundvars: 
  "term_ok' (sig \<Theta>) t \<Longrightarrow> term_ok' (sig \<Theta>) (incr_boundvars lev t)"
  using term_ok'_incr_bv incr_boundvars_def by simp

lemma term_ok'_subst_bv1:
  assumes "term_ok' (sig \<Theta>) f" and "term_ok' (sig \<Theta>) u"
  shows "term_ok' (sig \<Theta>) (subst_bv1 f lev u)" 
  using assms by (induction f lev u rule: subst_bv1.induct) (use term_ok'_incr_boundvars in auto) 

lemma term_ok'_subst_bv:
  assumes "term_ok' (sig \<Theta>) f" and "term_ok' (sig \<Theta>) u"
  shows "term_ok' (sig \<Theta>) (subst_bv f u)" 
  using assms term_ok'_subst_bv1 subst_bv_def by simp

lemma term_ok'_betapply:
  assumes "term_ok' (sig \<Theta>) f" "term_ok' (sig \<Theta>) u"
  shows "term_ok' (sig \<Theta>) (f \<bullet> u)"
proof(cases "f")
  case (Abs T t)
  then show ?thesis 
    using assms term_ok'_subst_bv1 by (simp add: subst_bv_def)
qed (use assms in auto)

lemma term_ok_betapply:
  assumes "term_ok \<Theta> f" "term_ok \<Theta> u" 
  assumes "typ_of f = Some (uty \<rightarrow> tty)" "typ_of u = Some uty"
  shows "term_ok \<Theta> (f \<bullet> u)"
  using assms term_ok'_betapply wt_term_def typ_of_betaply assms by auto 

lemma typ_ok_sig_subst_typ:
  assumes "is_std_sig \<Sigma>" and "typ_ok_sig \<Sigma> ty" and "distinct (map fst insts)" 
    and "list_all (typ_ok_sig \<Sigma>) (map snd insts)"
  shows "typ_ok_sig \<Sigma> (subst_typ insts ty)"
using assms proof (induction insts ty rule: subst_typ.induct)
  case (1 inst a Ts)
  have "typ_ok_sig \<Sigma> (subst_typ inst ty)" if "ty \<in> set Ts" for ty 
    using that 1 by (auto simp add: list_all_iff split: option.splits)

  hence "\<forall>ty \<in> set (map (subst_typ inst) Ts) . typ_ok_sig \<Sigma> ty" 
    by simp
  hence "list_all (typ_ok_sig \<Sigma>) (map (subst_typ inst) Ts)" 
    using list_all_iff by blast
  moreover have "length (map (subst_typ inst) Ts) = length Ts" by simp
  ultimately show ?case using "1.prems" by (auto split: option.splits)
next
  case (2 inst idn S)
  then show ?case
  proof(cases "lookup (\<lambda>x. x = (idn, S)) inst \<noteq> None")
    case True
    from this 2 obtain res where res: "lookup (\<lambda>x. x = (idn, S)) inst = Some res" by auto
    have "res \<in> set (map snd inst)" using 2 res by (induction inst) (auto split: if_splits)
    hence "typ_ok_sig \<Sigma> res" using 2(4) res 
      by (induction inst) (auto split: if_splits simp add: rev_image_eqI)  
    then show ?thesis using res by simp
  next
    case False
    hence rewr: "subst_typ inst (Tv idn S) = Tv idn S" by auto
    then show ?thesis using "2.prems"(2) by simp
  qed
qed

(* MOVE *)
corollary subst_typ_tinstT: "tinstT (subst_typ insts ty) ty"
  unfolding tinstT_def using tsubstT_simulates_subst_typ by fastforce

lemma tsubstT_trans: "tsubstT ty \<rho>1 = ty1 \<Longrightarrow> tsubstT ty1 \<rho>2 = ty2 
  \<Longrightarrow> tsubstT ty (\<lambda>idx s . case \<rho>1 idx s of Tv idx' s' \<Rightarrow> \<rho>2 idx' s' 
  | Ty s Ts \<Rightarrow> Ty s (map (\<lambda>T. tsubstT T \<rho>2) Ts)) = ty2"
unfolding tinstT_def proof (induction ty arbitrary: ty1 ty2)
  case (Tv idx s)
  then show ?case by (cases "\<rho>1 idx s") auto
qed auto

corollary tinstT_trans: "tinstT ty1 ty \<Longrightarrow> tinstT ty2 ty1 \<Longrightarrow> tinstT ty2 ty"
  unfolding tinstT_def using tsubstT_trans by blast

lemma term_ok'_subst_typ':
  assumes "is_std_sig \<Sigma>" and "term_ok' \<Sigma> t" and "distinct (map fst insts)" 
    and "list_all (typ_ok_sig \<Sigma>) (map snd insts)"
  shows "term_ok' \<Sigma> (subst_typ' insts t)"
  using assms by (induction t) 
    (use typ_ok_sig_subst_typ subst_typ_tinstT tinstT_trans in \<open>auto split: option.splits\<close>)

(* This is a bit suspect, as I am disregarding abstractions... *)
lemma 
  term_ok'_occs:
  "is_std_sig \<Sigma> \<Longrightarrow> term_ok' \<Sigma> t \<Longrightarrow> occs u t \<Longrightarrow> term_ok' \<Sigma> u"
  by (induction t) auto
                                                
lemma typ_of1_tsubst:
  "typ_of1 Ts t = Some ty \<Longrightarrow> typ_of1 (map (\<lambda>T . tsubstT T \<rho>) Ts) (tsubst t \<rho>) = Some (tsubstT ty \<rho>)"
proof (induction Ts t arbitrary: ty rule: typ_of1.induct)
  case (2 Ts i)
  then show ?case by (auto split: if_splits) 
next
  case (4 Ts T body)
  then show ?case by (auto simp add: bind_eq_Some_conv) 
next
  case (5 Ts f u)
  from "5.prems" obtain u_ty where u_ty: "typ_of1 Ts u = Some u_ty" by (auto simp add: bind_eq_Some_conv)
  from this "5.prems" have f_ty: "typ_of1 Ts f = Some (u_ty \<rightarrow> ty)" 
    by (auto simp add: bind_eq_Some_conv typ_of1_arg_typ[OF "5.prems"(1)] 
        split: if_splits typ.splits option.splits)

  from u_ty "5.IH"(1) have "typ_of1 (map (\<lambda>T. tsubstT T \<rho>) Ts) (tsubst u \<rho>) = Some (tsubstT u_ty \<rho>)" 
    by simp
  moreover from u_ty f_ty "5.IH"(2) have "typ_of1 (map (\<lambda>T. tsubstT T \<rho>) Ts) (tsubst f \<rho>) 
    = Some (tsubstT (u_ty \<rightarrow> ty) \<rho>)" 
    by simp
  ultimately show ?case by simp
qed auto

corollary typ_of1_tsubst_weak:
  assumes "typ_of1 Ts t = Some ty"
  assumes "typ_of1 (map (\<lambda>T . tsubstT T \<rho>) Ts) (tsubst t \<rho>) = Some ty'"
  shows "tsubstT ty \<rho> = ty'"
  using assms typ_of1_tsubst by auto

lemma tsubstT_no_change[simp]: "tsubstT T Tv = T"
  by (induction T) (auto simp add: map_idI)

lemma term_ok_mk_eq_same_typ:
  assumes "wf_theory \<Theta>"
  assumes "term_ok \<Theta> (mk_eq s t)"
  shows "typ_of s = typ_of t"
  using assms by (cases \<Theta> rule: theory_full_exhaust)
   (fastforce simp add: wt_term_def typ_of_def bind_eq_Some_conv tinstT_def)

lemma typ_of_eta_expand: "typ_of f = Some (\<tau> \<rightarrow> \<tau>') \<Longrightarrow> typ_of (Abs \<tau> (f $ Bv 0)) = Some (\<tau> \<rightarrow> \<tau>')"
  using typ_of1_weaken by (fastforce simp add: bind_eq_Some_conv typ_of_def)

lemma term_okI: "term_ok' (sig \<Theta>) t \<Longrightarrow> typ_of t \<noteq> None \<Longrightarrow> term_ok \<Theta> t"
  by (simp add: wt_term_def)
lemma term_okD1: "term_ok \<Theta> t \<Longrightarrow> term_ok' (sig \<Theta>) t"
  by (simp add: wt_term_def)
lemma term_okD2: "term_ok \<Theta> t \<Longrightarrow> typ_of t \<noteq> None"
  by (simp add: wt_term_def)

lemma term_ok_imp_typ_ok': assumes "wf_theory \<Theta>" "term_ok \<Theta> t" shows "typ_ok \<Theta> (the (typ_of t))"
proof-
  obtain ty where ty: "typ_of t = Some ty"
    by (meson assms option.exhaust term_okD2)
  hence "typ_ok \<Theta> ty"
    using term_ok_imp_typ_ok assms by blast
  thus ?thesis using ty by simp
qed

lemma term_ok_mk_eqI:
  assumes "wf_theory \<Theta>" "term_ok \<Theta> s" "term_ok \<Theta> t" "typ_of s = typ_of t" 
  shows"term_ok \<Theta> (mk_eq s t)"
proof (rule term_okI)
  have "typ_ok \<Theta> (the (typ_of t))"
    using assms(1) assms(3) term_ok_imp_typ_ok' by blast
  hence "typ_ok_sig (sig \<Theta>) (the (typ_of t))"
    by simp
  then show "term_ok' (sig \<Theta>) (mk_eq s t)"
    using assms apply -
    apply (drule term_okD1)+
    apply (cases \<Theta> rule: theory_full_exhaust) 
    by (auto split: option.splits simp add: tinstT_def) 
next
  show "typ_of (mk_eq s t) \<noteq> None"
    using assms typ_of_def by (auto dest: term_okD2 simp add: wt_term_def)
qed

lemma typ_of1_decr': "\<not> loose_bvar1 t 0 \<Longrightarrow> typ_of1 (T#Ts) t = Some \<tau> \<Longrightarrow> typ_of1 Ts (decr 0 t) = Some \<tau>"
proof (induction Ts t arbitrary: T \<tau> rule: typ_of1.induct)
  case (4 Ts B body)
  then show ?case 
    using typ_of1_decr_gen
    apply (simp add: bind_eq_Some_conv split: if_splits option.splits)
    by (metis append_Cons append_Nil length_Cons list.size(3) typ_of1_decr_gen)
next
  case (5 Ts f u)
  then show ?case apply (simp add: bind_eq_Some_conv split: if_splits option.splits)
    by (smt no_loose_bvar1_subst_bv2_decr subst_bv_def substn_subst_0' typ_of1.simps(3) typ_of1_subst_bv_gen')
qed (auto simp add: bind_eq_Some_conv split: if_splits option.splits)
  
lemma typ_of1_eta_red_step_pre: "\<not> loose_bvar1 t 0 \<Longrightarrow> 
  typ_of1 Ts (Abs \<tau> (t $ Bv 0)) = Some (\<tau> \<rightarrow> \<tau>') \<Longrightarrow> typ_of1 Ts (decr 0 t) = Some (\<tau> \<rightarrow> \<tau>')"
  using typ_of1_decr'
  by (smt length_Cons nth_Cons_0 typ_of1.simps(2) typ_of1_arg_typ typ_of_Abs_body_typ' zero_less_Suc)

lemma typ_of1_eta_red_step: "\<not> is_dependent t \<Longrightarrow> 
  typ_of (Abs \<tau> (t $ Bv 0)) = Some (\<tau> \<rightarrow> \<tau>') \<Longrightarrow> typ_of (decr 0 t) = Some (\<tau> \<rightarrow> \<tau>')"
  using typ_of_def is_dependent_def typ_of1_eta_red_step_pre by simp

(* MOVE *)
lemma distinct_add_vars': "distinct acc \<Longrightarrow> distinct (add_vars' t acc)"
  unfolding add_vars'_def
  by (induction t arbitrary: acc) auto
  
lemma distinct_add_tvarsT': "distinct acc \<Longrightarrow> distinct (add_tvarsT' T acc)"
proof (induction T arbitrary: acc)
  case (Ty n Ts)
  then show ?case
    by (induction Ts rule: rev_induct) (auto simp add: add_tvarsT'_def)
qed (simp add: add_tvarsT'_def) 

lemma distinct_add_tvars': "distinct acc \<Longrightarrow> distinct (add_tvars' t acc)"
  by (induction t arbitrary: acc) (simp_all add: add_tvars'_def fold_types_def distinct_add_tvarsT')

(* Figure out better syntax for goal *)
lemma proved_terms_well_formed_pre: "\<Theta>, \<Gamma> \<turnstile> p \<Longrightarrow> typ_of p = Some propT \<and> term_ok \<Theta> p"
proof (induction \<Gamma> p rule: proves.induct)
  case (axiom A \<rho>)           

  from axiom have ty: "typ_of1 [] A = Some propT"
    by (cases \<Theta> rule: theory_full_exhaust) (simp add: wt_term_def typ_of_def) 
  let ?l = "add_tvars' A []"
  let ?l' = "map (\<lambda>(v, S) . ((v, S), \<rho> v S)) ?l"
  have dist: "distinct ?l" 
    using distinct_add_tvars' by simp
  moreover have "\<forall>(v, S) \<in> set ?l . typ_ok \<Theta> (Tv v S)"
  proof-
    have "typ_ok \<Theta> (Tv v T)" if "(v, T) \<in> tvs A" for v T
      using axiom.hyps(1) axiom.hyps(2) axioms_terms_ok
        term_ok_tvars_sort_ok that typ_ok_def typ_ok_Tv
      by (meson wf_sort_def)
    moreover have "set ?l = tvs A"
      by auto
    ultimately show ?thesis
      by auto
  qed
  moreover hence "\<forall>(v, S) \<in> set ?l . has_sort (osig (sig \<Theta>)) (Tv v S) S"
    using axiom.hyps(1) has_sort_Tv_refl' by blast

  ultimately have "inst_ok \<Theta> ?l'"
    apply - apply (rule wf_inst_imp_inst_ok)
    using axiom.hyps(1) axiom.hyps(3) by blast+

  have simp: "tsubst A \<rho> = subst_typ' ?l' A"
    using dist subst_typ'_simulates_tsubst_gen' by auto

  have "typ_of1 [] (tsubst A \<rho>) = Some propT"
    using tsubst_simulates_subst_typ' axioms_typ_of_propT typ_of1_tsubst ty by fastforce
  hence 1: "typ_of1 [] (subst_typ' ?l' A) = Some propT"
    using simp by simp

  from axiom have "term_ok' (sig \<Theta>) A" 
    by (cases \<Theta> rule: theory_full_exhaust) (simp add: wt_term_def) 
  hence 2: "term_ok' (sig \<Theta>) (subst_typ' ?l' A)"
    using axiom term_ok'_subst_typ' apply (cases \<Theta> rule: theory_full_exhaust)
    apply (simp add: list_all_iff wt_term_def typ_of_def)
    by (metis (no_types, lifting) \<open>inst_ok \<Theta> (map (\<lambda>(v, S). ((v, S), \<rho> v S)) (add_tvars' A []))\<close> 
        axiom.hyps(1) list.pred_mono_strong sig.simps term_ok'_subst_typ' wf_theory.simps
        typ_ok_def wf_type_imp_typ_ok_sig)
  from 1 2 show ?case using simp by (simp add: wt_term_def typ_of_def)
next
  case ("assume" A)
  then show ?case by (simp add: wt_term_def)
next
  (*Same as case above*)
  case (forall_intro \<Gamma> B x \<tau>)
  hence "term_ok' (sig \<Theta>) B" and "typ_of B = Some propT" 
    by (simp_all add: wt_term_def)
  show ?case using typ_of_mk_all forall_intro
      term_ok_mk_all[OF \<open>wf_theory \<Theta>\<close> \<open>term_ok' (sig \<Theta>) B\<close> 
        \<open>typ_of B = Some propT\<close> _, of _ x] \<open>wf_type (sig \<Theta>) \<tau>\<close>
    by auto 
next
  case (forall_elim \<Gamma> \<tau> B a)
  thus ?case using term_ok'_subst_bv1
    by (auto simp add: typ_of_def term_ok'_subst_bv tinstT_def 
        wt_term_def bind_eq_Some_conv subst_bv_def typ_of1_subst_bv_gen' 
        split: if_splits option.splits)
next
  case (implies_intro \<Gamma> B A)
  then show ?case 
    by (cases \<Theta> rule: wf_theory.cases) (auto simp add: typ_of_def wt_term_def tinstT_def)
next
  case (implies_elim \<Gamma>\<^sub>1 A B \<Gamma>\<^sub>2)
  
  then show ?case 
    by (auto simp add: bind_eq_Some_conv typ_of_def wt_term_def tinstT_def 
        split: option.splits if_splits)
next
  case (of_class c iT T)

  then show ?case
    by (cases \<Theta> rule: theory_full_exhaust)  
      (auto simp add: bind_eq_Some_conv typ_of_def wt_term_def 
        tinstT_def mk_of_class_def mk_type_def) 
next
  case (\<beta>_conversion T t x)
  hence 1: "typ_of (mk_eq (Abs T t $ x) (subst_bv x t)) = Some propT"
    by (auto simp add: typ_of_def wt_term_def subst_bv_def bind_eq_Some_conv 
        typ_of1_subst_bv_gen')
  moreover have "term_ok \<Theta> (mk_eq (Abs T t $ x) (subst_bv x t))"
  proof- 
    have "typ_of (mk_eq (Abs T t $ x) (subst_bv x t)) \<noteq> None"
      using 1 by simp
    (* This needs to be moved out *)
    moreover have "term_ok' (sig \<Theta>) (mk_eq (Abs T t $ x) (subst_bv x t))"
    proof-
      have "term_ok' (sig \<Theta>) (Abs T t $ x)"
        using \<beta>_conversion.hyps(2) \<beta>_conversion.hyps(3) term_ok'.simps(4) wt_term_def term_ok_def by blast
      moreover hence "term_ok' (sig \<Theta>) (subst_bv x t)"
        using subst_bv_def term_ok'_subst_bv1 by auto
      moreover have "const_type (sig \<Theta>) STR ''Pure.eq''
        = Some ((Tv (Var (STR '''a'', 0)) full_sort) \<rightarrow> ((Tv (Var (STR '''a'', 0)) full_sort) \<rightarrow> propT))" 
        using \<beta>_conversion.hyps(1) by (cases \<Theta>) fastforce
      moreover obtain t' where "typ_of (Abs T t $ x) = Some t'"
        by (smt "1" typ_of1_split_App typ_of_def) 
      moreover hence "typ_of (subst_bv x t) = Some t'" 
        by (smt list.simps(1) subst_bv_def typ.simps(1) typ_of1_split_App typ_of1_subst_bv_gen' typ_of_Abs_body_typ' typ_of_def)
      moreover have "typ_ok_sig (sig \<Theta>) t'"
        using \<beta>_conversion.hyps(1) calculation(2) calculation(5) wt_term_def term_ok_imp_typ_ok typ_ok_def by auto
      moreover hence "typ_ok_sig (sig \<Theta>) (t' \<rightarrow> propT) "
        using \<open>wf_theory \<Theta>\<close> by (cases \<Theta> rule: theory_full_exhaust) auto
      moreover have "tinstT (T \<rightarrow> (T \<rightarrow> propT)) ((Tv (Var (STR '''a'', 0)) full_sort) \<rightarrow> ((Tv (Var (STR '''a'', 0)) full_sort) \<rightarrow> propT))"
        unfolding tinstT_def by auto
      moreover have "tinstT (t' \<rightarrow> (t' \<rightarrow> propT)) ((Tv (Var (STR '''a'', 0)) full_sort) \<rightarrow> ((Tv (Var (STR '''a'', 0)) full_sort) \<rightarrow> propT))"
        unfolding tinstT_def by auto
      ultimately show ?thesis using \<open>wf_theory \<Theta>\<close> by (cases \<Theta> rule: theory_full_exhaust) auto
    qed
    ultimately show ?thesis using wt_term_def by simp
  qed
  ultimately show ?case by simp
next
  case (eta t \<tau> \<tau>')
  hence tyeta: "typ_of (Abs \<tau> (t $ Bv 0)) = Some (\<tau> \<rightarrow> \<tau>')"
    using typ_of_eta_expand by auto
  moreover have "\<not> is_dependent t"
  proof-
    have "is_closed t"
      using eta.hyps(3) typ_of_imp_closed by blast
    thus ?thesis
      using is_dependent_def is_open_def loose_bvar1_imp_loose_bvar by blast
  qed
  ultimately have ty_decr: "typ_of (decr 0 t) = Some (\<tau> \<rightarrow> \<tau>')"
    using typ_of1_eta_red_step by blast

  hence 1: "typ_of (mk_eq (Abs \<tau> (t $ Bv 0)) (decr 0 t)) = Some propT"
    using eta tyeta by (auto simp add: typ_of_def)

  have "typ_ok \<Theta> (\<tau> \<rightarrow> \<tau>')" 
    using eta term_ok_imp_typ_ok by (simp add: wt_term_def del: typ_ok_def)
  hence tyok: "typ_ok \<Theta> \<tau>" "typ_ok \<Theta> \<tau>'"
    unfolding typ_ok_def by (auto split: option.splits)
  hence "term_ok \<Theta> (Abs \<tau> (t $ Bv 0))" 
    using eta(2) tyeta by (simp add: wt_term_def)
  moreover have "term_ok \<Theta> (decr 0 t)"
    using eta term_ok'_decr tyeta ty_decr wt_term_def typ_ok_def tyok 
    by (cases \<Theta> rule: theory_full_exhaust) (auto split: option.splits simp add: tinstT_def)
  ultimately have "term_ok \<Theta> (mk_eq (Abs \<tau> (t $ Bv 0)) (decr 0 t))" 
    using eta.hyps ty_decr tyeta tyok 1 term_ok_mk_eqI
    by metis
  then show ?case using 1
    using eta.hyps(2) eta.hyps(3) has_typ_imp_closed term_ok_subst_bv_no_change
      closed_subst_bv_no_change by auto
qed

corollary proved_terms_well_formed: 
  assumes "\<Theta>, \<Gamma> \<turnstile> p"
  shows "typ_of p = Some propT" "term_ok \<Theta> p"
  using assms proved_terms_well_formed_pre by auto

lemma forall_intros: 
  "wf_theory \<Theta> \<Longrightarrow> \<Theta>,\<Gamma> \<turnstile> B \<Longrightarrow> \<forall>(x, \<tau>)\<in>set frees . (x,\<tau>) \<notin> FV \<Gamma> \<and> typ_ok \<Theta> \<tau> 
    \<Longrightarrow> \<Theta>,\<Gamma> \<turnstile> mk_all_list frees B"
by (induction frees arbitrary: B)
   (auto intro: proves.forall_intro simp add: mk_all_list_def simp del: FV_def split: prod.splits)

(* MOVE *)
lemma term_ok_var[simp]: "term_ok \<Theta> (Fv idn \<tau>) = typ_ok \<Theta> \<tau>"
  by (simp add: wt_term_def typ_of_def)
lemma typ_of_var[simp]: "typ_of (Fv idn \<tau>) = Some \<tau>"
  by (simp add: typ_of_def)

(* Is this a simp rule? *)
lemma is_closed_Fv[simp]: "is_closed (Fv idn \<tau>)" by (simp add: is_open_def)

corollary proved_terms_closed: "\<Theta>, \<Gamma> \<turnstile> B \<Longrightarrow> is_closed B"
  by (simp add: proved_terms_well_formed(1) typ_of_imp_closed)

lemma not_loose_bvar_bind_fv2: 
  "\<not> loose_bvar t lev \<Longrightarrow> \<not> loose_bvar (bind_fv2 v lev t) (Suc lev)"
  by (induction t arbitrary: lev) auto
lemma not_loose_bvar_bind_fv2_: 
  "\<not> loose_bvar (bind_fv2 v lev t) lev \<Longrightarrow> \<not> loose_bvar t lev"
  by (induction t arbitrary: lev) (auto split: if_splits)

lemma fold_add_vars'_FV_pre: "set (fold add_vars' Hs acc) = set acc \<union> FV (set Hs)"
  by (induction Hs arbitrary: acc) (auto simp add: add_vars'_fv_pre)
corollary fold_add_vars'_FV[simp]: "set (fold (add_vars') Hs []) = FV (set Hs)"
  using fold_add_vars'_FV_pre by simp

lemma forall_intro_vars:
  assumes "wf_theory \<Theta>" "\<Theta>, set Hs \<turnstile> B" 
  shows "\<Theta>, set Hs \<turnstile> forall_intro_vars B Hs"
  apply (rule forall_intros)
  using assms apply simp_all apply clarsimp
  using add_vars'_fv proved_terms_well_formed_pre term_ok_vars_typ_ok 
  by (metis term_ok_vars_typ_ok typ_ok_def wf_type_imp_typ_ok_sig)

(* MOVE *)
lemma mk_all_list'_preserves_term_ok_typ_of:
  assumes "wf_theory \<Theta>" "term_ok \<Theta> B" "typ_of B = Some propT" "\<forall>(idn,ty)\<in>set vs . typ_ok \<Theta> ty"
  shows "term_ok \<Theta> (mk_all_list vs B) \<and> typ_of (mk_all_list vs B) = Some propT"
using assms proof (induction vs rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc v vs)
  hence I: "term_ok \<Theta> (mk_all_list vs B)" "typ_of (mk_all_list vs B) = Some propT" by simp_all
  obtain idn ty where v: "v=(idn,ty)" by fastforce
  hence s: "(mk_all_list (vs @ [v]) B) = mk_all idn ty (mk_all_list (vs) B)"
    by (simp add: mk_all_list_def)
  have "typ_ok \<Theta> ty" using v snoc.prems by simp
  then show ?case using I s term_ok_mk_all snoc.prems(1) wt_term_def typ_of_mk_all by auto 
qed

corollary forall_intro_vars_preserves_term_ok_typ_of:
  assumes "wf_theory \<Theta>" "term_ok \<Theta> B" "typ_of B = Some propT" 
  shows "term_ok \<Theta> (forall_intro_vars B Hs) \<and> typ_of (forall_intro_vars B Hs) = Some propT"
proof-                                              
  have 1: "\<forall>(idn,ty)\<in>set (add_vars' B []) . typ_ok \<Theta> ty"
    using add_vars'_fv assms(1) assms(2) term_ok_vars_typ_ok by blast
  thus ?thesis using assms mk_all_list'_preserves_term_ok_typ_of by simp
qed

(* MOVE and rename *)
lemma bind_fv_remove_var_from_fv: "fv (bind_fv (idn, \<tau>) t) = fv t - {(idn, \<tau>)}"
  using bind_fv2_Fv_fv bind_fv_def by simp

lemma forall_intro_vars_remove_fv[simp]: "fv (forall_intro_vars t []) = {}"
  using mk_all_list_fv_unchanged add_vars'_fv by simp

lemma term_ok_mk_all_list:
  assumes "wf_theory \<Theta>"
  assumes "term_ok \<Theta> B" 
  assumes "typ_of B = Some propT"
  assumes "\<forall>(idn, \<tau>) \<in> set l . typ_ok \<Theta> \<tau>"
  shows "term_ok \<Theta> (mk_all_list l B) \<and> typ_of (mk_all_list l B) = Some propT"
using assms proof(induction l rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc v vs)
  obtain idn \<tau> where v: "v = (idn, \<tau>)" by fastforce
  hence simp: "mk_all_list (vs@[v]) B = mk_all idn \<tau> (mk_all_list vs B)" 
    by (auto simp add: mk_all_list_def)
  have I: "term_ok \<Theta> (mk_all_list vs B)" "typ_of (mk_all_list vs B) = Some propT"
    using snoc by auto
  have "term_ok \<Theta> (mk_all idn \<tau> (mk_all_list vs B))"
    using term_ok_mk_all snoc.prems I v by (auto simp add: wt_term_def)
  moreover have "typ_of (mk_all idn \<tau> (mk_all_list vs B)) = Some propT"
    using I(2) v typ_of_mk_all by simp
  ultimately show ?case by (simp add: simp)
qed

(* Move, also see if these are not subsumed *)
lemma tvs_bind_fv2: "tvs (bind_fv2 (v, T) lev t) \<union> tvsT T = tvs t \<union> tvsT T"
  by (induction "(v, T)" lev t rule: bind_fv2.induct) auto
lemma tvs_bind_fv: "tvs (bind_fv (v,T) t) \<union> tvsT T = tvs t \<union> tvsT T"
  using tvs_bind_fv2 bind_fv_def by simp  

lemma tvs_mk_all': "tvs (mk_all idn ty B) = tvs B \<union> tvsT ty"
  using tvs_bind_fv typ_of_def is_variable.simps(2) by fastforce

lemma tvs_mk_all_list: 
  "tvs (mk_all_list vs B) = tvs B \<union> tvsT_Set (snd ` set vs)"
proof(induction vs rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc v vs)
  obtain idn \<tau> where v: "v = (idn, \<tau>)" by fastforce
  show ?case using snoc v tvs_mk_all' by (auto simp add: mk_all_list_def)
qed

lemma tvs_occs: "occs v t \<Longrightarrow> tvs v \<subseteq> tvs t"
  by (induction t) auto

lemma tvs_forall_intro_vars: "tvs (forall_intro_vars B Hs) = tvs B"
proof-
  have "\<forall>(idn, ty)\<in>fv B . occs (Fv idn ty) B" 
    using fv_occs by blast
  hence "\<forall>(idn, ty)\<in>fv B . tvs (Fv idn ty) \<subseteq> tvs B"
    using tvs_occs by blast
  hence "\<forall>(idn, ty)\<in>fv B . tvsT ty \<subseteq> tvs B" 
    by simp
  hence "tvsT_Set (snd ` fv B) \<subseteq> tvs B" 
    by fastforce
  hence "tvsT_Set (snd ` set (add_vars' B [])) \<subseteq> tvs B"
    by (simp add: add_vars'_fv)
  thus ?thesis using tvs_mk_all_list by auto
qed

lemma "strip_all_single_var B = Some \<tau> \<Longrightarrow> strip_all_single_body B \<noteq> B"
  using strip_all_vars_step by fastforce

lemma strip_all_body_unchanged_iff_strip_all_single_body_unchanged: 
  "strip_all_body B = B \<longleftrightarrow> strip_all_single_body B = B"
  by (metis not_Cons_self2 not_None_eq not_is_all_imp_strip_all_body_unchanged 
      strip_all_body_single_simp' strip_all_single_var_is_all strip_all_vars_step)

lemma strip_all_body_unchanged_imp_strip_all_vars_no: 
  assumes "strip_all_body B = B"
  shows "strip_all_vars B = []"
  by (smt assms not_Cons_self2 strip_all_body_single_simp' strip_all_single_body.simps(1) strip_all_vars.elims)

lemma strip_all_body_unchanged_imp_strip_all_single_body_unchanged: 
  "strip_all_body B = B \<Longrightarrow> strip_all_single_body B = B"
  by (smt (z3) not_Cons_self2 strip_all_body_single_simp' strip_all_single_body.simps(1) strip_all_vars.simps(1))

lemma strip_all_single_body_unchanged_imp_strip_all_body_unchanged: 
  "strip_all_single_body B = B \<Longrightarrow> strip_all_body B = B"
  by (auto elim!: strip_all_single_body.elims)

lemma strip_all_single_var_np_imp_strip_all_body_single_unchanged: 
  "strip_all_single_var B = None \<Longrightarrow> strip_all_single_body B = B"
  by (auto elim!: strip_all_single_var.elims)

lemma strip_all_single_form: "strip_all_single_var B = Some \<tau>
  \<Longrightarrow> Ct STR ''Pure.all'' ((\<tau> \<rightarrow> propT) \<rightarrow> propT) $ Abs \<tau> (strip_all_single_body B) = B"
  by (auto elim!: strip_all_single_var.elims split: if_splits)

lemma proves_strip_all_single:
  assumes "\<Theta>, \<Gamma> \<turnstile> B" "strip_all_single_var B = Some \<tau>"
    "typ_of t = Some \<tau>" "term_ok \<Theta> t"
  shows "\<Theta>, \<Gamma> \<turnstile> subst_bv t (strip_all_single_body B)"
proof-
  have 1: "Ct STR ''Pure.all'' ((\<tau> \<rightarrow> propT) \<rightarrow> propT) $ Abs \<tau> (strip_all_single_body B) = B"
    using assms(2) strip_all_single_form by blast
  hence "\<Theta>, \<Gamma> \<turnstile> Abs \<tau> (strip_all_single_body B) \<bullet> t"
    using assms forall_elim
  proof -
    have "has_typ t \<tau>"
      by (meson \<open>typ_of t = Some \<tau>\<close> has_typ_iff_typ_of)
    then show ?thesis
      by (metis "1" assms(1) assms(4) betapply.simps(1) forall_elim term_ok_def wt_term_def)
  qed
  thus ?thesis by simp
qed

corollary proves_strip_all_single_Fv:
  assumes "\<Theta>, \<Gamma> \<turnstile> B" "strip_all_single_var B = Some \<tau>"
  shows "\<Theta>, \<Gamma> \<turnstile> subst_bv (Fv x \<tau>) (strip_all_single_body B)"
proof -
  have ok: "term_ok \<Theta> B"
    using assms(1) proved_terms_well_formed(2) by auto
  thm strip_all_single_form 
      wt_term_def term_ok_var typ_of_var typ_ok_def proves_strip_all_single 
      strip_all_single_form
  have s: "B = Ct STR ''Pure.all'' ((\<tau> \<rightarrow> propT) \<rightarrow> propT) $ Abs \<tau> (strip_all_single_body B)"
    using assms(2) strip_all_single_form[symmetric] by simp
  have "\<tau> \<in> Types B"
    by (subst s, simp)
  hence "typ_ok \<Theta> \<tau>"
    by (metis ok s term_ok'.simps(4) term_ok'.simps(5) term_okD1 typ_ok_def typ_ok_sig_imp_wf_type)
  hence "term_ok \<Theta> (Fv x \<tau>)"
    using term_ok_var by blast
  then show ?thesis 
    using assms proves_strip_all_single[where \<tau>=\<tau>] by auto
qed

lemma strip_all_vars_no_strip_all_body_unchanged[simp]: 
  "strip_all_vars B = [] \<Longrightarrow> strip_all_body B = B"
  by (auto elim!: strip_all_vars.elims)

lemma "strip_all_vars B = (\<tau>s@[\<tau>]) \<Longrightarrow> strip_all_body B 
  = strip_all_single_body (Ct STR ''Pure.all'' ((\<tau> \<rightarrow> propT) \<rightarrow> propT) $ Abs \<tau> (strip_all_body B))"
  by simp

lemma strip_all_vars_incr_bv: "strip_all_vars (incr_bv inc lev t) = strip_all_vars t"
  by (induction t arbitrary: lev rule: strip_all_vars.induct) auto
lemma strip_all_vars_incr_boundvars: "strip_all_vars (incr_boundvars inc t) = strip_all_vars t"
  using incr_boundvars_def strip_all_vars_incr_bv by simp

lemma strip_all_vars_subst_bv1_Fv:
  "strip_all_vars (subst_bv1 B lev (Fv x \<tau>)) = strip_all_vars B"
  by (induction B arbitrary: lev rule: strip_all_vars.induct) (auto simp add: incr_boundvars_def)
lemma strip_all_vars_subst_bv_Fv:
  "strip_all_vars (subst_bv (Fv x \<tau>) B) = strip_all_vars B"
  by (simp add: strip_all_vars_subst_bv1_Fv subst_bv_def)
  
lemma "strip_all_single_var B = Some \<tau>
  \<Longrightarrow> strip_all_vars (subst_bv (Fv x \<tau>) (strip_all_single_body B)) = tl (strip_all_vars B)"
  by (metis list.sel(3) strip_all_vars_step strip_all_vars_subst_bv_Fv)

(* Allowing general terms instead of just vars here is more difficult as one could create new leading
  \<And>s *)
corollary proves_strip_all_vars_Fv:
  assumes "length xs = length (strip_all_vars B)" "\<Theta>, \<Gamma> \<turnstile> B"
  shows "\<Theta>, \<Gamma> \<turnstile> fold (\<lambda>(x,\<tau>). subst_bv (Fv x \<tau>) o strip_all_single_body)
    (zip xs (strip_all_vars B)) B"
using assms proof (induction xs "strip_all_vars B" arbitrary: B rule: list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons x xs \<tau> \<tau>s)
  have st: "strip_all_single_var B = Some \<tau>" 
    by (metis Cons.hyps(3) is_all_iff_strip_all_vars_not_empty list.distinct(1) list.inject 
        option.exhaust strip_all_single_var_is_all strip_all_vars_step)
  moreover have "term_ok \<Theta> (Fv x \<tau>)" 
  proof-
    obtain B' where "Ct STR ''Pure.all'' ((\<tau> \<rightarrow> propT) \<rightarrow> propT) $ Abs \<tau> B' = B"
      using st strip_all_single_form by blast
    moreover have "term_ok \<Theta> B" 
      using Cons.prems proved_terms_well_formed(2) by auto
    ultimately have "typ_ok \<Theta> \<tau>"
      using term_ok'.simps(5) term_ok'.simps(4) term_ok_def wt_term_def typ_ok_def by blast
    thus ?thesis unfolding term_ok_def wt_term_def typ_ok_def by simp
  qed
  ultimately have 1: "\<Theta>,\<Gamma> \<turnstile> subst_bv (Fv x \<tau>) (strip_all_single_body B)"
    using proves_strip_all_single
    by (simp add: Cons.prems proves_strip_all_single_Fv)
  have "\<Theta>,\<Gamma> \<turnstile> fold (\<lambda>(x, \<tau>). subst_bv (Fv x \<tau>) \<circ> strip_all_single_body)
    (zip xs (strip_all_vars (subst_bv (Fv x \<tau>) (strip_all_single_body B)))) 
      (subst_bv (Fv x \<tau>) (strip_all_single_body B))"
    apply (rule Cons.hyps)
    apply (metis Cons.hyps(3) list.inject st strip_all_vars_step strip_all_vars_subst_bv_Fv)
    using 1 by simp
  moreover have "strip_all_vars B = \<tau> # \<tau>s"
    using Cons.hyps(3) by auto
  ultimately show ?case
    using st strip_all_vars_step strip_all_vars_subst_bv_Fv by fastforce
qed


lemma trivial_pre_depr: "term_ok \<Theta> c \<Longrightarrow> typ_of c = Some propT \<Longrightarrow> \<Theta>, {c} \<turnstile> c"
  by (rule "assume") (simp_all add: wt_term_def)

lemma trivial_pre:
  assumes "wf_theory \<Theta>" "term_ok \<Theta> c" "typ_of c = Some propT"
  shows "\<Theta>, {} \<turnstile> c \<longmapsto> c"
proof-
  have s: "{} = {c} - {c}" by simp
  show ?thesis
    apply (subst s)
    apply (rule "implies_intro")
    using assms by (auto simp add: wt_term_def intro: "assume")
qed

lemma inst_var: 
  assumes wf_theory: "wf_theory \<Theta>"
  assumes B: "\<Theta>, \<Gamma> \<turnstile> B"
  assumes a_ok: "term_ok \<Theta> a" 
  assumes typ_a: "typ_of a = Some \<tau>"
  assumes free: "(x,\<tau>) \<notin> FV \<Gamma>"
  shows "\<Theta>, \<Gamma> \<turnstile> subst_term [((x, \<tau>), a)] B"
proof-
  have s1: "mk_all x \<tau> B = Ct STR ''Pure.all'' ((\<tau> \<rightarrow> propT) \<rightarrow> propT) $ 
    Abs \<tau> (bind_fv (x, \<tau>) B)"
    by (simp add: typ_of_def)                
  have closed_B: "is_closed B" using B proved_terms_well_formed_pre
    using typ_of_imp_closed by blast
  have "typ_ok \<Theta> \<tau>" using wt_term_def typ_ok_def term_ok_imp_typ_ok
    using a_ok wf_theory typ_a by blast
  hence p1: "\<Theta>, \<Gamma> \<turnstile> mk_all x \<tau> B" 
    using forall_intro[OF wf_theory B] B typ_a wt_term_def wf_theory 
        term_ok_imp_typ_ok free by simp
  have "\<Theta>, \<Gamma> \<turnstile> subst_bv a (bind_fv (x, \<tau>) B)"
    using forall_elim[of _ _ \<tau>] p1 typ_a a_ok proves_strip_all_single
    by (meson has_typ_iff_typ_of term_ok_def wt_term_def)
  have "\<Theta>, \<Gamma> \<turnstile> subst_bv a ((bind_fv (x, \<tau>) B))"
    using forall_elim[of _ _ \<tau>] p1 typ_a a_ok proves_strip_all_single
    by (meson has_typ_iff_typ_of term_ok_def wt_term_def)
  thus "\<Theta>, \<Gamma> \<turnstile> subst_term [((x, \<tau>), a)] B"
    using instantiate_var_same_type'' assms closed_B by simp
qed

(* MOVE *)
lemma subst_term_single_no_change[simp]:
  assumes nvar: "(x,\<tau>)\<notin>fv B"
  shows "subst_term [((x,\<tau>), t)] B = B"
  using assms by (induction B) auto

lemma fv_subst_term_single:
  assumes var: "(x,\<tau>)\<in>fv B"
  assumes "\<And>p . p \<in> fv t \<Longrightarrow> p ~= (x,\<tau>)"
  shows "fv (subst_term [((x,\<tau>), t)] B) = fv B - {(x,\<tau>)} \<union> fv t"
using assms proof (induction B)
  case (App B1 B2)
  then show ?case 
    by (cases "(x,\<tau>)\<in>fv B1"; cases "(x,\<tau>)\<in>fv B2") auto
qed simp_all

(* TODO: Get rid of distinctness and non_overlap by performing standard single to parallel substitution
  construction: Rename variables, then substitute the now non problematic terms

  TODO: Check assms for useless ones, improve syntax
*)
lemma inst_vars_pre: 
  assumes wf_theory: "wf_theory \<Theta>"
  assumes B: "\<Theta>, \<Gamma> \<turnstile> B"
  (*assumes vars: "set (map fst insts) \<subseteq> fv B"*)
  assumes vars_ok: "list_all (term_ok \<Theta>) (map snd insts)"
  assumes typs_ok: "list_all (\<lambda>((idx, ty), t) . typ_of t = Some ty) insts"
  assumes free: "list_all (\<lambda>((idx, ty), t) . (idx, ty) \<notin> FV \<Gamma>) insts"
  assumes typ_a: "typ_of a = Some \<tau>"
  assumes distinct: "distinct (map fst insts)"
  assumes no_overlap: "\<And>x . x \<in> (\<Union>t \<in> snd ` (set insts) . fv t) \<Longrightarrow> x \<notin> fst ` (set insts)"
  shows "\<Theta>, \<Gamma> \<turnstile> fold (\<lambda>single. subst_term [single]) insts B"
using assms proof(induction insts arbitrary: B)
  case Nil
  then show ?case using B by simp
next
  case (Cons x xs)

  from this obtain idn ty t where x: "x = ((idn, ty), t)" by (metis prod.collapse)

  have "\<Theta>, \<Gamma> \<turnstile> fold (\<lambda>single. subst_term [single]) (x # xs) B
    \<longleftrightarrow> \<Theta>, \<Gamma> \<turnstile> fold (\<lambda>single. subst_term [single]) xs (subst_term [x] B)"
    by simp
  moreover have "\<Theta>, \<Gamma> \<turnstile> fold (\<lambda>single. subst_term [single]) xs (subst_term [x] B)"
  proof-
    have single: "\<Theta>, \<Gamma> \<turnstile> (subst_term [x] B)" using inst_var Cons by (simp add: x)
    show ?thesis using Cons single by simp
  qed
  ultimately show ?case by simp
qed

(* MOVE *)
lemma subterm_term_ok': 
  "is_std_sig \<Sigma> \<Longrightarrow> term_ok' \<Sigma> t \<Longrightarrow> is_closed st \<Longrightarrow> occs st t \<Longrightarrow> term_ok' \<Sigma> st"
proof (induction t arbitrary: st)
  case (Abs T t)
  then show ?case by (auto simp add: is_open_def)
next
  case (App t1 t2)
  then show ?case using term_ok'_occs by blast
qed auto

(* MOVE *)
lemma infinite_fv_UNIV: "infinite (UNIV :: (indexname \<times> typ) set)" 
  by (simp add: finite_prod)


lemma implies_intro'_pre:
  assumes "wf_theory \<Theta>" "\<Theta>, \<Gamma> \<turnstile> B" "term_ok \<Theta> A" "typ_of A = Some propT" "A \<notin> \<Gamma>"
  shows "\<Theta>, \<Gamma> \<turnstile> A \<longmapsto> B"
  using assms proves.implies_intro apply (simp add: wt_term_def)
  by (metis Diff_empty Diff_insert0)

lemma implies_intro'_pre2:
  assumes "wf_theory \<Theta>" "\<Theta>, \<Gamma> \<turnstile> B" "term_ok \<Theta> A" "typ_of A = Some propT" "A \<in> \<Gamma>"
  shows "\<Theta>, \<Gamma> \<turnstile> A \<longmapsto> B"
proof-
  have 1: "\<Theta>, \<Gamma> - {A} \<turnstile> A \<longmapsto> B"
    using assms proves.implies_intro by (simp add: wt_term_def)
  have "\<Theta>, \<Gamma> - {A} - {A} \<turnstile> A \<longmapsto> (A \<longmapsto> B)"
    using assms proves.implies_intro 
    by (simp add: 1 implies_intro'_pre) 
  moreover have "\<Theta>, {A} \<turnstile> A"
    using proves.assume assms
    by (simp add: trivial_pre_depr)
  moreover have "\<Gamma> = (\<Gamma> - {A} - {A}) \<union> {A}"
    using assms by auto
  ultimately show ?thesis using proves.implies_elim by metis
qed

(* Names are suspect, change *)
lemma subst_term_preserves_typ_of1[simp]: 
  "typ_of1 Ts (subst_term [((x, \<tau>), Fv y \<tau>)] t) = typ_of1 Ts t"
  by (induction Ts t rule: typ_of1.induct) (fastforce)+

lemma subst_term_preserves_typ_of[simp]:
  "typ_of (subst_term [((x, \<tau>), Fv y \<tau>)] t) = typ_of t"
  using typ_of_def by simp

lemma subst_term_preserves_term_ok'[simp]: 
  "term_ok' \<Sigma> (subst_term [((x, \<tau>), Fv y \<tau>)] t) \<longleftrightarrow> term_ok' \<Sigma> t"
  by (induction t) auto

lemma subst_term_preserves_term_ok[simp]:
  "term_ok \<Theta> (subst_term [((x, \<tau>), Fv y \<tau>)] A) \<longleftrightarrow> term_ok \<Theta> A"
  by (simp add: wt_term_def)

lemma not_in_FV_in_fv_not_in: "(x,\<tau>) \<notin> FV \<Gamma> \<Longrightarrow> (x,\<tau>) \<in> fv t \<Longrightarrow> t \<notin> \<Gamma>"
  by auto

lemma subst_term_fv: "fv (subst_term [((x, \<tau>), Fv y \<tau>)] t) 
  = (if (x,\<tau>) \<in> fv t then insert (y,\<tau>) else id) (fv t - {(x,\<tau>)})"
  by (induction t) auto

lemma rename_free: 
  assumes wf_theory: "wf_theory \<Theta>"
  assumes B: "\<Theta>, \<Gamma> \<turnstile> B"
  assumes free: "(x,\<tau>)\<notin> FV \<Gamma>"
  shows "\<Theta>, \<Gamma> \<turnstile> subst_term [((x, \<tau>), Fv y \<tau>)] B"
  by (metis B free inst_var proved_terms_well_formed(2) subst_term_single_no_change
      term_ok_vars_typ_ok term_ok_var wf_theory typ_of_var)

lemma tvs_subst_term_single[simp]: "tvs (subst_term [((x, \<tau>), Fv y \<tau>)] A) = tvs A"
  by (induction A) auto

(* Conditions are a bit random, clear up *)
lemma weaken_proves': "\<Theta>, \<Gamma> \<turnstile> B \<Longrightarrow> term_ok \<Theta> A \<Longrightarrow> typ_of A = Some propT \<Longrightarrow> A \<notin> \<Gamma>
  \<Longrightarrow> finite \<Gamma> 
  \<Longrightarrow> \<Theta>, insert A \<Gamma> \<turnstile> B"
proof (induction \<Gamma> B arbitrary: A rule: proves.induct)
  case (axiom A insts \<Gamma> A')
  then show ?case using proves.axiom axiom by metis
next
  case ("assume" A \<Gamma> A')
  then show ?case using proves.intros by blast
next
  case (forall_intro \<Gamma> B x \<tau>) 

  have "\<exists>y . y\<notin>fst ` (fv A \<union> fv B \<union> FV \<Gamma>)"
  proof-
    have "finite (FV \<Gamma>)" 
      using finite_fv forall_intro.prems by auto
    hence "finite (fv A \<union> fv B \<union> FV \<Gamma>)" by simp
    hence "finite (fst ` (fv A \<union> fv B \<union> FV \<Gamma>))" by simp
    
    thus ?thesis using variant_variable_fresh by blast 
  qed
  from this obtain y where "y\<notin>fst ` (fv A \<union> fv B \<union> FV \<Gamma>)" by auto
  
  have not_in_ren: "subst_term [((x, \<tau>), Fv y \<tau>)] A \<notin> \<Gamma>"
  proof(cases "(x, \<tau>) \<in> fv A")
    case True
    show ?thesis 
    apply (rule not_in_FV_in_fv_not_in[of y \<tau>])
     apply (metis (full_types) Un_iff \<open>y \<notin> fst ` (fv A \<union> fv B \<union> FV \<Gamma>)\<close> fst_conv image_eqI)
    using True subst_term_fv by auto
  next
    case False
    hence "subst_term [((x, \<tau>), Fv y \<tau>)] A = A"
      by simp
    then show ?thesis
      by (simp add: forall_intro.prems(3))
  qed
  have term_ok_ren: "term_ok \<Theta> (subst_term [((x, \<tau>), Fv y \<tau>)] A)"
    using forall_intro.prems(1) subst_term_preserves_term_ok by blast
  have typ_of_ren: "typ_of (subst_term [((x, \<tau>), Fv y \<tau>)] A) = Some propT"
    using forall_intro.prems by auto

  hence "\<Theta>, insert (subst_term [((x, \<tau>), Fv y \<tau>)] A) \<Gamma> \<turnstile> B"
    using forall_intro.IH forall_intro.prems(3) forall_intro.prems(4) 
      not_in_ren term_ok_ren typ_of_ren by blast
  have "\<Theta>, insert (subst_term [((x, \<tau>), Fv y \<tau>)] A) \<Gamma> \<turnstile> mk_all x \<tau> B"
    apply (rule proves.forall_intro)
       apply (simp add: forall_intro.hyps(1)) 
    using \<open>\<Theta>, insert (subst_term [((x, \<tau>), Fv y \<tau>)] A) \<Gamma> \<turnstile> B\<close> apply blast
    subgoal using subst_term_fv \<open>(x, \<tau>) \<notin> FV \<Gamma>\<close> apply simp
      by (metis Un_iff \<open>y \<notin> fst ` (fv A \<union> fv B \<union> FV \<Gamma>)\<close> fst_conv image_eqI)
    using forall_intro.hyps(4) by blast
  hence "\<Theta>, \<Gamma> \<turnstile> subst_term [((x, \<tau>), Fv y \<tau>)] A \<longmapsto> mk_all x \<tau> B"
    using forall_intro.hyps(1) forall_intro.hyps(2) forall_intro.hyps(4)
      forall_intro.prems(1) forall_intro.prems(3) 
      implies_intro'_pre local.forall_intro not_in_ren proves.forall_intro 
      subst_term_preserves_typ_of term_ok_ren by auto
  hence "\<Theta>, \<Gamma> \<turnstile> subst_term [((y, \<tau>), Fv x \<tau>)] 
    (subst_term [((x, \<tau>), Fv y \<tau>)] A \<longmapsto> mk_all x \<tau> B)" 
    by (smt Un_iff \<open>y \<notin> fst ` (fv A \<union> fv B \<union> FV \<Gamma>)\<close> forall_intro.hyps(1) 
        fst_conv image_eqI rename_free)
  hence "\<Theta>, \<Gamma> \<turnstile> A \<longmapsto> mk_all x \<tau> B"
    using forall_intro proves.forall_intro implies_intro'_pre by auto
  moreover have "\<Theta>, {A} \<turnstile> A"
    using forall_intro.prems(1) local.forall_intro(7) trivial_pre_depr by blast
  ultimately show ?case 
    using implies_elim by fastforce
next
  case (forall_elim \<Gamma> \<tau> B a)
  then show ?case using proves.forall_elim by blast
next
  case (implies_intro \<Gamma> B N)
  then show ?case
  proof (cases "A=N")
    case True
    (* Do this less automatic probably, for speed reasons*)
    hence "\<Theta>,\<Gamma> - {N} \<turnstile> N \<longmapsto> B" 
      
      using implies_intro.hyps(1) implies_intro.hyps(2) implies_intro.hyps(3) 
          implies_intro.hyps(4) proves.implies_intro by blast
    hence "\<Theta>,\<Gamma> - {N} \<turnstile> A \<longmapsto> N \<longmapsto> B"
      using True implies_intro'_pre implies_intro.hyps(1) implies_intro.hyps(3) 
          implies_intro.hyps(4) implies_intro.prems(1) by blast
    hence "\<Theta>,insert N \<Gamma> \<turnstile> B" 
      using True implies_elim implies_intro insert_absorb by fastforce
    then show ?thesis
      using True implies_elim implies_intro.hyps(3) implies_intro.hyps(4) implies_intro.prems(1) 
        trivial_pre_depr by (simp add: implies_intro'_pre2 implies_intro.hyps(1))
  next
    case False
    hence s: "insert A (\<Gamma> - {N}) = insert A \<Gamma> - {N}" by auto

    have I: "\<Theta>,insert A \<Gamma> \<turnstile> B"
      using implies_intro.prems False by (auto intro!: implies_intro.IH)
      
    show ?thesis
      apply (subst s)
      apply (rule proves.implies_intro)
      using implies_intro.hyps I by auto
  qed
next
  case (implies_elim \<Gamma>\<^sub>1 A' B \<Gamma>\<^sub>2)
  show ?case 
    using proves.implies_elim implies_elim by (metis UnCI Un_insert_left finite_Un)
next
  case (\<beta>_conversion \<Gamma> s T t x)
  then show ?case using proves.\<beta>_conversion by blast
next
  case (eta t \<tau> \<tau>')
  then show ?case using proves.eta by simp
next
  case (of_class c T' T \<Gamma>)
  then show ?case
    by (simp add: proves.of_class)
qed
corollary weaken_proves: "\<Theta>, \<Gamma> \<turnstile> B \<Longrightarrow> term_ok \<Theta> A \<Longrightarrow> typ_of A = Some propT
  \<Longrightarrow> finite \<Gamma> 
  \<Longrightarrow> \<Theta>, insert A \<Gamma> \<turnstile> B"
  using weaken_proves' by (metis insert_absorb) 

lemma weaken_proves_set: "finite \<Gamma>2 \<Longrightarrow> \<Theta>, \<Gamma> \<turnstile> B \<Longrightarrow> \<forall>A\<in>\<Gamma>2 . term_ok \<Theta> A \<Longrightarrow> \<forall>A\<in>\<Gamma>2 . typ_of A = Some propT
  \<Longrightarrow> finite \<Gamma>
  \<Longrightarrow> \<Theta>, \<Gamma> \<union> \<Gamma>2 \<turnstile> B"
  by (induction \<Gamma>2 arbitrary: \<Gamma> rule: finite_induct) (use weaken_proves in auto)

(* Maybe do directly instead *)
lemma no_tvsT_imp_subst_typ_unchanged: "tvsT T = empty \<Longrightarrow> subst_typ insts T = T"
  by (simp add: no_tvsT_imp_tsubsT_unchanged tsubstT_simulates_subst_typ)

lemma subst_typ_fv:
  shows "apsnd (subst_typ insts) ` fv B = fv (subst_typ' insts B)" 
  by (induction B) auto

lemma subst_typ_fv_point:
  assumes "(x, \<tau>) \<in> fv B" 
  shows "(x, subst_typ insts \<tau>) \<in> fv (subst_typ' insts B)" 
  using subst_typ_fv by (metis apsnd_conv assms image_eqI)

lemma subst_typ_typ_ok:
  assumes "typ_ok_sig \<Sigma> \<tau>"
  assumes "list_all (typ_ok_sig \<Sigma>) (map snd insts)"
  shows "typ_ok_sig \<Sigma> (subst_typ insts \<tau>)"
using assms proof (induction \<tau>)
  case (Tv idn \<tau>)
  then show ?case 
    by (cases "lookup (\<lambda>x. x = (idn, \<tau>)) insts")
      (fastforce simp add: list_all_iff dest: lookup_present_eq_key' split: prod.splits)+  
qed (auto simp add: list_all_iff lookup_present_eq_key' split: option.splits)

lemma subst_typ_comp_single_left: "subst_typ [single] (subst_typ insts T) 
  = subst_typ (map (apsnd (subst_typ [single])) insts@[single]) T"
proof (induction T)
  case (Tv idn ty) 
  then show ?case by (induction insts) auto
qed auto

lemma subst_typ_comp_single_left_stronger: "subst_typ [single] (subst_typ insts T) 
  = subst_typ (map (apsnd (subst_typ [single])) insts
  @ (if fst single \<in> set (map fst insts) then [] else [single])) T"
proof (induction T)
  case (Tv idn S)
  then show ?case
  proof (cases "lookup (\<lambda>x. x = (idn,S)) insts")
    case None
    hence "lookup (\<lambda>x. x = (idn, S)) (map (apsnd (subst_typ [single])) insts) = None" 
      by (induction insts) (auto split: if_splits)
    then show ?thesis 
      using None apply simp
      by (metis eq_fst_iff list.set_map lookup.simps(2) lookup_None_iff subst_typ.simps(2) 
          subst_typ_comp subst_typ_nil the_default.simps(1))
  next
    case (Some a)
    hence "lookup (\<lambda>x. x = (idn, S)) (map (apsnd (subst_typ [single])) insts) = Some (subst_typ [single] a)" 
      by (induction insts) (auto split: if_splits)
    then show ?thesis 
      using Some apply simp 
      by (metis subst_typ.simps(2) subst_typ_comp_single_left the_default.simps(2))
  qed
qed auto

lemma subst_typ'_comp_single_left: "subst_typ' [single] (subst_typ' insts t)
  = subst_typ' (map (apsnd (subst_typ [single])) insts@[single]) t"
  by (induction t) (use subst_typ_comp_single_left in auto)

lemma subst_typ'_comp_single_left_stronger: "subst_typ' [single] (subst_typ' insts t)
  = subst_typ' (map (apsnd (subst_typ [single])) insts
  @ (if fst single \<in> set (map fst insts) then [] else [single])) t"
  by (induction t) (use subst_typ_comp_single_left_stronger in auto)

lemma subst_typ_preserves_typ_ok:
  assumes "wf_theory \<Theta>"
  assumes "typ_ok \<Theta> T"
  assumes "list_all (typ_ok \<Theta>) (map snd insts)"
  shows "typ_ok \<Theta> (subst_typ insts T)" 
using assms proof (induction T)
  case (Ty n Ts)
  have I: "\<forall>x \<in> set Ts . typ_ok \<Theta> (subst_typ insts x)"
    using Ty by (auto simp add: typ_ok_def list_all_iff split: option.splits) 
  moreover have "(\<forall>x \<in> set Ts . typ_ok \<Theta> (subst_typ insts x)) =
     (\<forall>x \<in> set (map (subst_typ insts) Ts) . typ_ok \<Theta> x)" by (induction Ts) auto
  ultimately have "list_all (wf_type (sig \<Theta>)) (map (subst_typ insts) Ts)"
    using  list_allI typ_ok_def Ball_set typ_ok_def by fastforce
  then show ?case using Ty list.pred_mono_strong by (force split: option.splits)
next
  case (Tv idn \<tau>)
  then show ?case by (induction insts) auto
qed

lemma typ_ok_Ty[simp]: "typ_ok \<Theta> (Ty n Ts) \<Longrightarrow> list_all (typ_ok \<Theta>) Ts"
  by (auto simp add: typ_ok_def list.pred_mono_strong split: option.splits)
lemma typ_ok_sig_Ty[simp]: "typ_ok_sig \<Sigma> (Ty n Ts) \<Longrightarrow> list_all (typ_ok_sig \<Sigma>) Ts"
  by (auto simp add: list.pred_mono_strong split: option.splits)

lemma wf_theory_imp_wf_osig: "wf_theory \<Theta> \<Longrightarrow> wf_osig (osig (sig \<Theta>))"
  by (cases \<Theta> rule: theory_full_exhaust) simp

lemma the_lift2_option_Somes[simp]: "the (lift2_option f (Some a) (Some b)) = f a b" by simp

lemma class_les_mgd:
  assumes "wf_osig oss" 
  assumes "tcsigs oss type = Some mgd"
  assumes "mgd C' = Some Ss'"
  assumes "class_les (subclass oss) C' C"
  shows "mgd C \<noteq> None"
proof-
  have "complete_tcsigs (subclass oss) (tcsigs oss)"
    using assms(1) by (cases oss) simp
  thus ?thesis
    using assms(2-4) by (auto simp add: class_les_def class_leq_def complete_tcsigs_def intro!: domI ranI)
qed

lemma has_sort_sort_leq_osig:
  assumes "wf_osig (sub, tcs)" "has_sort (sub,tcs) T S" "sort_leq sub S S'"
  shows "has_sort (sub,tcs) T S'"
using assms(2,3,1) proof (induction "(sub,tcs)" T S arbitrary: S' rule: has_sort.induct)
  case (has_sort_Tv S S' tcs a)
  then show ?case
    using wf_osig.simps wf_subclass_loc.intro wf_subclass_loc.sort_leq_trans by blast
next
  case (has_sort_Ty \<kappa> K S Ts)
  show ?case
  proof (rule has_sort.has_sort_Ty[where dm=K])
    show "tcs \<kappa> = Some K"
      using has_sort_Ty.hyps(1) .
  next
    show "\<forall>C\<in>S'. \<exists>Ss. K C = Some Ss \<and> list_all2 (has_sort (sub, tcs)) Ts Ss"
    proof (rule ballI)
      fix C assume C: "C \<in> S'"
      show "\<exists>Ss. K C = Some Ss \<and> list_all2 (has_sort (sub, tcs)) Ts Ss"
      proof (cases "C \<in> S")
        case True
        then show ?thesis
          using list_all2_mono has_sort_Ty.hyps(2) by fastforce
      next
        case False
        from this obtain C' where C': 
          "C' \<in> S" "class_les sub C' C"
          by (metis C class_les_def has_sort_Ty.prems(1) has_sort_Ty.prems(2) sort_leq_def 
              subclass.simps wf_osig_imp_wf_subclass_loc wf_subclass_loc.class_leq_antisym)
        from this obtain Ss' where Ss': 
          "K C' = Some Ss'" "list_all2 (has_sort (sub,tcs)) Ts Ss'"
          using list_all2_mono has_sort_Ty.hyps(2) by fastforce
        from this obtain Ss where Ss: "K C = Some Ss"
          using has_sort_Ty.prems class_les_mgd C'(2) has_sort_Ty.hyps(1) wf_theory_imp_wf_osig
          by force
        have lengthSs': "length Ts = length Ss'"
          using Ss'(2) list_all2_lengthD by auto
        have coregular: 
          "coregular_tcsigs sub tcs"
          using has_sort_Ty.prems(2) wf_theory_imp_wf_osig wf_tcsigs_def 
          by (metis wf_osig.simps)

        hence leq: "list_all2 (sort_leq sub) Ss' Ss"
          using C'(2) Ss'(1) Ss has_sort_Ty.hyps(1) ranI
          by (metis class_les_def coregular_tcsigs_def domI option.sel)

        have "list_all2 (has_sort (sub,tcs)) Ts Ss"
        proof(rule list_all2_all_nthI)
          show "length Ts = length Ss" 
            using Ss Ss'(1) lengthSs' wf_theory_imp_wf_osig leq list_all2_lengthD by auto
        next
          fix n assume n: "n < length Ts"
          hence "sort_leq sub (Ss' ! n) (Ss ! n)"
            using leq by (simp add: lengthSs' list_all2_nthD)
          thus "has_sort (sub,tcs) (Ts ! n) (Ss ! n)"
            using has_sort_Ty.hyps(2) has_sort_Ty.prems(2) C'(1) Ss'(1) n list_all2_nthD
            by fastforce
        qed

        thus "\<exists>Ss. K C = Some Ss \<and> list_all2 (has_sort (sub, tcs)) Ts Ss"
          using Ss by (simp)
      qed
    qed
  qed
qed

lemma has_sort_sort_leq: "wf_theory \<Theta> \<Longrightarrow> has_sort (osig (sig \<Theta>)) T S 
  \<Longrightarrow> sort_leq (subclass (osig (sig \<Theta>))) S S'
  \<Longrightarrow> has_sort (osig (sig \<Theta>)) T S'"
by (metis has_sort_sort_leq_osig subclass.elims wf_theory_imp_wf_osig)

lemma subst_typ_preserves_has_sort:
  assumes "wf_theory \<Theta>"
  assumes "has_sort (osig (sig \<Theta>)) T S"
  assumes "list_all (\<lambda>((idn, S), T). has_sort (osig (sig \<Theta>)) T S) insts"
  shows "has_sort (osig (sig \<Theta>)) (subst_typ insts T) S"
using assms proof(induction T arbitrary: S)
  case (Ty \<kappa> Ts)
  obtain cl tcs where cltcs: "osig (sig \<Theta>) = (cl, tcs)"
    by fastforce
  moreover obtain K where "tcsigs (osig (sig \<Theta>)) \<kappa> = Some K"
    using Ty.prems(2) has_sort.simps by auto
  ultimately have mgd: "tcs \<kappa> = Some K" 
    by simp
  have "has_sort (osig (sig \<Theta>)) (subst_typ insts (Ty \<kappa> Ts)) S
    = has_sort (osig (sig \<Theta>)) (Ty \<kappa> (map (subst_typ insts) Ts)) S"
    by simp
  moreover have "has_sort (osig (sig \<Theta>)) (Ty \<kappa> (map (subst_typ insts) Ts)) S"
  proof (subst cltcs, rule has_sort_Ty[of tcs, OF mgd], rule ballI)
    fix C assume C: "C \<in> S"
    obtain Ss where Ss: "K C = Some Ss"
      using C Ty.prems(2) mgd has_sort.simps cltcs by auto
    have "list_all2 (has_sort (osig (sig \<Theta>))) (map (subst_typ insts) Ts) Ss"
    proof (rule list_all2_all_nthI)
      show "length (map (subst_typ insts) Ts) = length Ss"
        using C Ss Ty.prems(2) list_all2_lengthD mgd has_sort.simps cltcs by fastforce
    next
      fix n assume n: "n < length (map (subst_typ insts) Ts)"

      have "list_all2 (has_sort (cl, tcs)) Ts Ss"
        using C Ss Ty.prems(2) cltcs has_sort.simps mgd by auto
      hence 1: "has_sort (osig (sig \<Theta>)) (Ts ! n) (Ss ! n)"
        using cltcs list_all2_conv_all_nth n by auto
      have "has_sort (osig (sig \<Theta>)) (subst_typ insts (Ts ! n)) (Ss ! n)"
        using 1 n Ty.prems cltcs C Ss mgd Ty.IH by auto

      then show "has_sort (osig (sig \<Theta>)) (map (subst_typ insts) Ts ! n) (Ss ! n)"
        using n by auto
    qed
    thus "\<exists>Ss. K C = Some Ss \<and> list_all2 (has_sort (cl, tcs)) (map (subst_typ insts) Ts) Ss"
      using Ss cltcs by simp
  qed
  ultimately show ?case
    by simp
next
  case (Tv idn S')
  show ?case
  proof(cases "(lookup (\<lambda>x. x = (idn, S')) insts)")
    case None
    then show ?thesis using Tv by simp
  next
    case (Some res)
    hence "((idn, S'), res) \<in> set insts" using lookup_present_eq_key' by fast
    hence "has_sort (osig (sig \<Theta>)) res S'" using Tv
      using split_list by fastforce
    moreover have 1: "sort_leq (subclass (osig (sig \<Theta>))) S' S"
      using Tv.prems(2) has_sort_Tv_imp_sort_leq by blast
    ultimately show ?thesis 
      using Some Tv(2) has_sort_Tv_imp_sort_leq apply simp
      using assms(1) 1 has_sort_sort_leq by blast
  qed
qed


lemma subst_typ_preserves_Some_typ_of1:
  assumes "typ_of1 Ts t = Some T"
  shows "typ_of1 (map (subst_typ insts) Ts) (subst_typ' insts t) 
      = Some (subst_typ insts T)"
using assms proof (induction t arbitrary: T Ts)
next
  case (App t1 t2)
  from this obtain RT where "typ_of1 Ts t1 = Some (RT \<rightarrow> T)" 
    using typ_of1_split_App_obtains by blast
  hence "typ_of1 (map (subst_typ insts) Ts) (subst_typ' insts t1) =
    Some (subst_typ insts (RT \<rightarrow> T))" using App.IH(1) by blast
  moreover have "typ_of1 (map (subst_typ insts) Ts) (subst_typ' insts t2) = Some (subst_typ insts RT)"
    using App \<open>typ_of1 Ts t1 = Some (RT \<rightarrow> T)\<close> typ_of1_fun_typ by blast
  ultimately show ?case by simp
qed (fastforce split: if_splits simp add: bind_eq_Some_conv)+

corollary subst_typ_preserves_Some_typ_of:
  assumes "typ_of t = Some T"
  shows "typ_of (subst_typ' insts t) 
      = Some (subst_typ insts T)"
  using assms subst_typ_preserves_Some_typ_of1 typ_of_def by fastforce

lemma subst_typ'_incr_bv: 
  "subst_typ' insts (incr_bv inc lev t) = incr_bv inc lev (subst_typ' insts t)"
  by (induction inc lev t rule: incr_bv.induct) auto 

lemma subst_typ'_incr_boundvars:
  "subst_typ' insts (incr_boundvars lev t) = incr_boundvars lev (subst_typ' insts t)"
  using subst_typ'_incr_bv incr_boundvars_def by simp 

lemma subst_typ'_subst_bv1: "subst_typ' insts (subst_bv1 t n u) 
  = subst_bv1 (subst_typ' insts t) n (subst_typ' insts u)"
  by (induction t n u rule: subst_bv1.induct) (auto simp add: subst_typ'_incr_boundvars)

lemma subst_typ'_subst_bv: "subst_typ' insts (subst_bv t u) 
  = subst_bv (subst_typ' insts t) (subst_typ' insts u)"
  using subst_typ'_subst_bv1 subst_bv_def by simp

lemma subst_typ_no_tvsT_unchanged:
  "\<forall>(f, s) \<in> set insts . f \<notin> tvsT T \<Longrightarrow> subst_typ insts T = T"
proof (induction T)
  case (Ty n Ts)
  then show ?case by (induction Ts) (fastforce split: prod.splits)+ 
next
  case (Tv idn S)
  then show ?case 
    by simp (smt case_prodD case_prodE find_None_iff lookup_None_iff_find_None the_default.simps(1))
qed

lemma subst_typ'_no_tvs_unchanged:
  "\<forall>(f, s) \<in> set insts . f \<notin> tvs t \<Longrightarrow> subst_typ' insts t = t"
  by (induction t) (use subst_typ_no_tvsT_unchanged in \<open>fastforce+\<close>)
  
(* This is weaker than the previously proved version, but probably easier to use... *)
lemma subst_typ'_preserves_term_ok':
  assumes "wf_theory \<Theta>"
  assumes "inst_ok \<Theta> insts"
  assumes "term_ok' (sig \<Theta>) t"
  shows "term_ok' (sig \<Theta>) (subst_typ' insts t)"
  using assms term_ok'_subst_typ' typ_ok_def
  by (metis list.pred_mono_strong wf_theory_imp_is_std_sig wf_type_imp_typ_ok_sig)

lemma subst_typ'_preserves_term_ok:
  assumes "wf_theory \<Theta>"
  assumes "inst_ok \<Theta> insts"
  assumes "term_ok \<Theta> t"
  shows "term_ok \<Theta> (subst_typ' insts t)"
using assms subst_typ_preserves_Some_typ_of wt_term_def subst_typ'_preserves_term_ok' by auto

lemma subst_typ_rename_vars_cancel:
  assumes "y \<notin> fst ` tvsT T" 
  shows "subst_typ [((y,S), Tv x S)] (subst_typ [((x,S), Tv y S)] T) = T"
using assms proof (induction T)
  case (Ty n Ts)
  then show ?case by (induction Ts) auto
qed auto

lemma subst_typ'_rename_tvars_cancel:
  assumes "y \<notin> fst ` tvs t" assumes "y \<notin> fst ` tvsT \<tau>" 
  shows "subst_typ' [((y,S), Tv x S)] ((bind_fv2 (x, subst_typ [((x,S), Tv y S)] \<tau>)) 
    lev (subst_typ' [((x,S), Tv y S)] t))
  = bind_fv2 (x, \<tau>) lev t"
using assms proof (induction t arbitrary: lev)
  case (Ct n T)
  then show ?case 
    by (simp add: subst_typ_rename_vars_cancel)
next
  case (Fv idn T)
  then show ?case
    by (clarsimp simp add: subst_typ_rename_vars_cancel) (metis subst_typ_rename_vars_cancel)
next
  case (Abs T t)
  thus ?case
    by (simp add: image_Un subst_typ_rename_vars_cancel)
next
  case (App t1 t2)
  then show ?case
    by (simp add: image_Un)
qed auto

lemma bind_fv2_renamed_var:
  assumes "y \<notin> fst ` fv t" 
  shows "bind_fv2 (y, \<tau>) i (subst_term [((x, \<tau>), Fv y \<tau>)] t) 
    = bind_fv2 (x, \<tau>) i t"
using assms proof (induction t arbitrary: i)
qed auto

lemma bind_fv_renamed_var:
  assumes "y \<notin> fst ` fv t" 
  shows "bind_fv (y, \<tau>) (subst_term [((x, \<tau>), Fv y \<tau>)] t)
    = bind_fv (x, \<tau>) t"
  using bind_fv2_renamed_var bind_fv_def assms by auto

lemma subst_typ'_rename_tvar_bind_fv2:
  assumes "y \<notin> fst ` fv t" 
  assumes "(b, S) \<notin> tvs t"
  assumes "(b, S) \<notin> tvsT \<tau>"
  shows "bind_fv2 (y, subst_typ [((a, S), Tv b S)] \<tau>) i 
  (subst_typ' [((a,S), Tv b S)] (subst_term [((x, \<tau>), Fv y \<tau>)] t))
    = subst_typ' [((a,S), Tv b S)] (bind_fv2 (x, \<tau>) i t)"
using assms proof (induction t arbitrary: i)
qed auto

lemma subst_typ'_rename_tvar_bind_fv:
  assumes "y \<notin> fst ` fv t" 
  assumes "(b, S) \<notin> tvs t"
  assumes "(b, S) \<notin> tvsT \<tau>"
  shows "bind_fv (y, subst_typ [((a,S), Tv b S)] \<tau>) 
  (subst_typ' [((a,S), Tv b S)] (subst_term [((x, \<tau>), Fv y \<tau>)] t))
    = subst_typ' [((a,S), Tv b S)] (bind_fv (x, \<tau>) t)"
  using bind_fv_def assms subst_typ'_rename_tvar_bind_fv2 by auto

lemma tvar_in_fv_in_tvs: "(a, \<tau>) \<in> fv B \<Longrightarrow> (x, S) \<in> tvsT \<tau> \<Longrightarrow> (x, S) \<in> tvs B"
  by (induction B) auto

lemma tvs_bind_fv2_subset: "tvs (bind_fv2 (a, \<tau>) i B) \<subseteq> tvs B"
  by (induction B arbitrary: i) auto

lemma tvs_bind_fv_subset: "tvs (bind_fv (a, \<tau>) B) \<subseteq> tvs B"
  using tvs_bind_fv2_subset bind_fv_def by simp

lemma subst_typ_rename_tvar_preserves_eq:
  "(y, S) \<notin> tvsT T \<Longrightarrow> (y, S) \<notin> tvsT \<tau> \<Longrightarrow>
    subst_typ [((x, S), Tv y S)] T = subst_typ [((x, S), Tv y S)] \<tau> \<Longrightarrow> T=\<tau>"
proof (induction T arbitrary: \<tau>)
  case (Ty n Ts)
  then show ?case
  proof (induction \<tau>)
    case (Ty n Ts)
    then show ?case
      by simp (smt list.inj_map_strong)
  next
    case (Tv n S)
    then show ?case 
      by (auto split: if_splits)
  qed
next
  case (Tv n S)
  then show ?case by (induction \<tau>) (auto split: if_splits)
qed

lemma subst_typ'_subst_term_rename_var_swap:
  assumes "b \<notin> fst ` fv B"
  assumes "(y, S) \<notin> tvs B"
  assumes "(y, S) \<notin> tvsT \<tau>"
  shows "subst_typ' [((x, S), Tv y S)] (subst_term [((a, \<tau>), Fv b \<tau>)] B)
    = subst_term [((a, (subst_typ [((x, S), Tv y S)] \<tau>)), Fv b (subst_typ [((x, S), Tv y S)] \<tau>))] 
      (subst_typ' [((x, S), Tv y S)] B)"
using assms proof (induction B)
  case (Fv idn T)
  then show ?case using subst_typ_rename_tvar_preserves_eq by auto
qed auto  

(* My naming needs work, also those lemmas might be subsumed *)
lemma tvar_not_in_term_imp_free_not_in_term:
  "(y, S) \<in> tvsT \<tau> \<Longrightarrow> (y,S) \<notin> tvs t \<Longrightarrow> (a, \<tau>) \<notin> fv t"
  by (induction t) auto

lemma tvar_not_in_term_imp_free_not_in_term_set:
  "finite \<Gamma> \<Longrightarrow> (y, S) \<in> tvsT \<tau> \<Longrightarrow> (y,S) \<notin> tvs_Set \<Gamma> \<Longrightarrow> (a, \<tau>) \<notin> FV \<Gamma>"
  using tvar_not_in_term_imp_free_not_in_term by simp

(* I can probably weaken vars a bit, should only need wf criteria on insts, nothing more *)
lemma inst_var_multiple: 
  assumes wf_theory: "wf_theory \<Theta>"
  assumes B: "\<Theta>, \<Gamma> \<turnstile> B"
  assumes vars: "\<forall>(x,\<tau>)\<in>fst ` set insts . term_ok \<Theta> (Fv x \<tau>)"
  assumes a_ok: "\<forall>a\<in>snd ` set insts . term_ok \<Theta> a" 
  assumes typ_a: "\<forall>((_,\<tau>), a)\<in>set insts . typ_of a = Some \<tau>"
  assumes free: "\<forall>(v, _)\<in>set insts . v \<notin> FV \<Gamma>"
  assumes distinct: "distinct (map fst insts)"
  assumes finite: "finite \<Gamma>"
  shows "\<Theta>, \<Gamma> \<turnstile> subst_term insts B"
proof- 
  obtain fresh_idns where fresh_idns:
    "length fresh_idns = length insts"
    "\<forall>idn \<in> set fresh_idns . 
      idn \<notin> fst ` (fv B \<union> (\<Union>t\<in>snd ` set insts . (fv t)) \<union> (fst ` set insts)) \<union> fst ` (FV \<Gamma>)"
    "distinct fresh_idns" 
    using distinct_fresh_rename_idns fresh_fresh_rename_idns length_fresh_rename_idns finite_FV finite 
    by (metis finite_imageI)
  have 0: "subst_term insts B                                        
    = fold (\<lambda>single acc . subst_term [single] acc) (zip (zip fresh_idns (map snd (map fst insts))) (map snd insts)) 
      (fold (\<lambda>single acc . subst_term [single] acc) (zip (map fst insts) (map2 Fv fresh_idns (map snd (map fst insts)))) B)"
    using fresh_idns distinct subst_term_combine' by simp

  from fresh_idns vars a_ok typ_a free distinct have 1: 
    "\<Theta>, \<Gamma> \<turnstile> (fold (\<lambda>single acc . subst_term [single] acc) 
    (zip (map fst insts) (map2 Fv fresh_idns (map snd (map fst insts)))) B)"
  proof (induction fresh_idns insts rule: rev_induct2)
    case Nil
    then show ?case using B by simp 
  next
    case (snoc x xs y ys)
    from snoc have term_oky: "term_ok \<Theta> (Fv (fst (fst y)) (snd (fst y)))"
      by (auto simp add: wt_term_def split: prod.splits)

    have 1: "\<Theta>, \<Gamma> \<turnstile> fold (\<lambda>single. subst_term [single])
            (zip (map fst ys) (map2 Fv xs (map snd (map fst ys)))) B" 
      apply (rule snoc.IH)
      subgoal using snoc.prems(1) by (clarsimp split: prod.splits) (smt UN_I Un_iff fst_conv image_iff)
      using snoc.prems(2-7) by auto

    moreover obtain yn n where ynn: "fst y = (yn, n)" by fastforce 
    moreover have "\<Theta>,\<Gamma> \<turnstile> subst_term [(fst y, Fv x n)]
          (fold (\<lambda>single. subst_term [single]) (zip (map fst (ys))
            (map2 Fv (xs) (map snd (map fst (ys))))) B)" 
      apply (simp only: ynn)
      apply (rule inst_var[of "\<Theta>" \<Gamma> "(fold (\<lambda>single. subst_term [single]) (zip (map fst (ys))
            (map2 Fv (xs) (map snd (map fst (ys))))) B)" "(Fv x n)" "n" "yn"])
      using snoc.prems \<open>wf_theory \<Theta>\<close> 1 apply (solves simp)+
      using term_oky ynn apply (simp add: wt_term_def typ_of_def)
      using term_oky ynn apply (simp add: wt_term_def typ_of_def)
      using snoc.prems(6) ynn by auto

    moreover have "fold (\<lambda>single. subst_term [single]) (zip (map fst (ys @ [y]))
      (map2 Fv (xs @ [x]) (map snd (map fst (ys @ [y]))))) B
      = subst_term [(fst y, Fv x (snd (fst y)))]
          (fold (\<lambda>single. subst_term [single]) (zip (map fst (ys))
            (map2 Fv (xs) (map snd (map fst (ys))))) B)"
      using snoc.hyps by (induction xs ys rule: list_induct2) simp_all 
      
    ultimately show ?case by simp
  qed
  define point where "point \<equiv> (fold (\<lambda>single acc . subst_term [single] acc) 
    (zip (map fst insts) (map2 Fv fresh_idns (map snd (map fst insts)))) B)" 
  
  from fresh_idns vars a_ok typ_a free distinct have 2: 
    "\<Theta>, \<Gamma> \<turnstile> fold (\<lambda>single acc . subst_term [single] acc)
      (zip (zip fresh_idns (map snd (map fst insts))) (map snd insts)) 
      point"
  proof (induction fresh_idns insts rule: rev_induct2)
    case Nil
    then show ?case using B 
      using 1 point_def by auto
  next
    case (snoc x xs y ys)
    
    from snoc have typ_ofy: "typ_of (snd y) = Some (snd (fst y))" by auto 

    have 1: " \<Theta>,\<Gamma> \<turnstile> fold (\<lambda>single. subst_term [single])
            (zip (zip xs (map snd (map fst ys))) (map snd ys))
            point" 
      apply (rule snoc.IH)
      subgoal using snoc.prems(1) by (clarsimp split: prod.splits) (smt UN_I Un_iff fst_conv image_iff)
      using snoc.prems(2-7) by auto
    moreover obtain yn n where ynn: "fst y = (yn, n)" by fastforce 
    moreover have "\<Theta>,\<Gamma> \<turnstile> subst_term [((x, snd (fst y)), snd y)] (fold (\<lambda>single. subst_term [single])
            (zip (zip (xs) (map snd (map fst (ys))))
              (map snd (ys)))
            point)"
      apply (simp only: ynn) apply (rule inst_var) 
      using snoc.prems \<open>wf_theory \<Theta>\<close> 1 apply (solves simp)+ 
      using typ_ofy ynn apply (simp add: wt_term_def typ_of_def)
      using snoc.prems apply simp
      by (metis (full_types, hide_lams) UN_I fst_conv image_eqI)
    moreover have "fold (\<lambda>single. subst_term [single])
            (zip (zip (xs @ [x]) (map snd (map fst (ys @ [y]))))
              (map snd (ys @ [y])))
            point = subst_term [((x, snd (fst y)), snd y)] (fold (\<lambda>single. subst_term [single])
            (zip (zip (xs) (map snd (map fst (ys))))
              (map snd (ys)))
            point)" 
      using snoc.hyps by (induction xs ys rule: list_induct2) simp_all 
    
    ultimately show ?case by simp
  qed
  
  from 0 1 2 show ?thesis using point_def by simp
qed

lemma term_ok_eta_red_step: 
  "\<not> is_dependent t \<Longrightarrow> term_ok \<Theta> (Abs T (t $ Bv 0)) \<Longrightarrow> term_ok \<Theta> (decr 0 t)"
  unfolding term_ok_def wt_term_def using term_ok'_decr eta_preserves_typ_of by simp blast

end