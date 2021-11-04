
section "Wellformed Signature and Theory"

theory Theory
  imports Term Sorts SortConstants 
begin

(* Functional versions of wf_type/wf_term, for historic reasons still used in definitions and proofs *)
fun typ_ok_sig :: "signature \<Rightarrow> typ \<Rightarrow> bool" where
  "typ_ok_sig \<Sigma> (Ty c Ts) = (case type_arity \<Sigma> c of
    None \<Rightarrow> False
  | Some ar \<Rightarrow> length Ts = ar \<and> list_all (typ_ok_sig \<Sigma>) Ts)"
| "typ_ok_sig \<Sigma> (Tv _ S) = wf_sort (subclass (osig \<Sigma>)) S"

lemma typ_ok_sig_imp_wf_type: "typ_ok_sig \<Sigma> T \<Longrightarrow> wf_type \<Sigma> T"
  by (induction T) (auto split: option.splits intro: wf_type.intros simp add: list_all_iff)
lemma wf_type_imp_typ_ok_sig: "wf_type \<Sigma> T \<Longrightarrow> typ_ok_sig \<Sigma> T"
  by (induction \<Sigma> T rule: wf_type.induct) (simp_all split: option.splits add: list_all_iff)
  
corollary wf_type_iff_typ_ok_sig[iff]: "wf_type \<Sigma> T = typ_ok_sig \<Sigma> T"
  using wf_type_imp_typ_ok_sig typ_ok_sig_imp_wf_type by blast

fun term_ok' :: "signature \<Rightarrow> term \<Rightarrow> bool" where
  "term_ok' \<Sigma> (Fv _ T) = typ_ok_sig \<Sigma> T"
| "term_ok' \<Sigma> (Bv _) = True"
| "term_ok' \<Sigma> (Ct s T) = (case const_type \<Sigma> s of
    None \<Rightarrow> False
  | Some ty \<Rightarrow> typ_ok_sig \<Sigma> T \<and> tinstT T ty)"
| "term_ok' \<Sigma> (t $ u) \<longleftrightarrow> term_ok' \<Sigma> t \<and> term_ok' \<Sigma> u" 
| "term_ok' \<Sigma> (Abs T t) \<longleftrightarrow> typ_ok_sig \<Sigma> T \<and> term_ok' \<Sigma> t"

lemma term_ok'_imp_wf_term: "term_ok' \<Sigma> t \<Longrightarrow> wf_term \<Sigma> t"
  by (induction t) (auto intro: wf_term.intros split: option.splits)
lemma wf_term_imp_term_ok': "wf_term \<Sigma> t \<Longrightarrow> term_ok' \<Sigma> t"
  by (induction \<Sigma> t rule: wf_term.induct) (auto split: option.splits)
corollary wf_term_iff_term_ok'[iff]: "wf_term \<Sigma> t = term_ok' \<Sigma> t"
  using term_ok'_imp_wf_term wf_term_imp_term_ok' by blast

lemma acyclic_empty[simp]: "acyclic {}" unfolding acyclic_def by simp

lemma "wf_sig (Map.empty, Map.empty, empty_osig)"
  by (simp add: coregular_tcsigs_def complete_tcsigs_def consistent_length_tcsigs_def 
      all_normalized_and_ex_tcsigs_def)
lemma 
  term_ok_imp_typ_ok_pre:
  "is_std_sig \<Sigma> \<Longrightarrow> wf_term \<Sigma> t \<Longrightarrow> list_all (typ_ok_sig \<Sigma>) Ts
  \<Longrightarrow> typ_of1 Ts t = Some ty \<Longrightarrow> typ_ok_sig \<Sigma> ty"
proof (induction Ts t arbitrary: ty rule: typ_of1.induct)
  case (2 Ts i)
  then show ?case by (auto simp add: bind_eq_Some_conv list_all_length split: option.splits if_splits)
next
  case (4 Ts T body)
  obtain bodyT where bodyT: "typ_of1 (T#Ts) body = Some bodyT"
    using "4.prems" by fastforce
  hence ty: "ty = T \<rightarrow> bodyT" 
    using 4 by simp
  have "typ_ok_sig \<Sigma> bodyT" 
    using 4 bodyT by simp
  thus ?case 
    using ty 4 by (cases \<Sigma>) auto
next
  case (5 Ts f u T)
  from this obtain U where "typ_of1 Ts u = Some U"
    using typ_of1_split_App by blast
  moreover hence "typ_of1 Ts f = Some (U \<rightarrow> T)"
    using "5.prems"(4) by (meson typ_of1_arg_typ)
  ultimately have "typ_ok_sig \<Sigma> (U \<rightarrow> T)"
    using "5.IH"(2) "5.prems"(1) "5.prems"(2) "5.prems"(3) term_ok'.simps(4) by blast
  then show ?case
    by (auto simp add: bind_eq_Some_conv split: option.splits if_splits)
qed (auto simp add: bind_eq_Some_conv split: option.splits if_splits)

(* This might now be doable with just prod rules *)
lemma theory_full_exhaust: "(\<And>cto tao sorts axioms. 
    \<Theta> = ((cto, tao, sorts), axioms) \<Longrightarrow> P)
  \<Longrightarrow> P"
  apply (cases \<Theta>) subgoal for \<Sigma> axioms apply (cases \<Sigma>) by auto done

definition [simp]: "typ_ok \<Theta> T \<equiv> wf_type (sig \<Theta>) T"
definition [simp]: "term_ok \<Theta> t \<equiv> wt_term (sig \<Theta>) t"

corollary typ_of_subst_bv_no_change: "typ_of t \<noteq> None \<Longrightarrow> subst_bv u t = t"
  using closed_subst_bv_no_change typ_of_imp_closed by auto
corollary term_ok_subst_bv_no_change: "term_ok \<Theta> t \<Longrightarrow> subst_bv u t = t"
  using typ_of_subst_bv_no_change wt_term_def by auto

lemmas eq_axs_def = eq_reflexive_ax_def eq_symmetric_ax_def eq_transitive_ax_def eq_intr_ax_def 
  eq_elim_ax_def eq_combination_ax_def eq_abstract_rule_ax_def

bundle eq_axs_simp
begin
declare eq_axs_def[simp]
declare mk_all_list_def[simp] add_vars'_def[simp] bind_eq_Some_conv[simp] bind_fv_def[simp]
end

lemma typ_of_eq_ax: "typ_of (eq_reflexive_ax) = Some propT" 
    "typ_of (eq_symmetric_ax) = Some propT" 
    "typ_of (eq_transitive_ax) = Some propT" 
    "typ_of (eq_intr_ax) = Some propT" 
    "typ_of (eq_elim_ax) = Some propT"
    "typ_of (eq_combination_ax) = Some propT" 
    "typ_of (eq_abstract_rule_ax) = Some propT" 
  by (auto simp add: typ_of_def eq_axs_def mk_all_list_def add_vars'_def bind_eq_Some_conv bind_fv_def)
  
lemma term_ok_eq_ax:
  assumes "is_std_sig (sig \<Theta>)"
  shows "term_ok \<Theta> (eq_reflexive_ax)" 
    "term_ok \<Theta> (eq_symmetric_ax)" 
    "term_ok \<Theta> (eq_transitive_ax)" 
    "term_ok \<Theta> (eq_intr_ax)" 
    "term_ok \<Theta> (eq_elim_ax)"
    "term_ok \<Theta> (eq_combination_ax)"
    "term_ok \<Theta> (eq_abstract_rule_ax)"
  using assms 
  by (all \<open>cases \<Theta> rule: theory_full_exhaust\<close>) 
   (auto simp add: wt_term_def typ_of_def tinstT_def eq_axs_def bind_eq_Some_conv
      bind_fv_def sort_ex_def normalize_sort_def mk_all_list_def add_vars'_def wf_sort_def)

lemma wf_theory_imp_is_std_sig: "wf_theory \<Theta> \<Longrightarrow> is_std_sig (sig \<Theta>)"
  by (cases \<Theta> rule: theory_full_exhaust) simp
lemma wf_theory_imp_wf_sig: "wf_theory \<Theta> \<Longrightarrow> wf_sig (sig \<Theta>)"
  by (cases \<Theta> rule: theory_full_exhaust) simp

lemma 
  term_ok_imp_typ_ok:
  "wf_theory thy \<Longrightarrow> term_ok thy t \<Longrightarrow> typ_of t = Some ty \<Longrightarrow> typ_ok thy ty"
  apply (cases thy)
  using term_ok_imp_typ_ok_pre term_ok_def
  by (metis list.pred_inject(1) wt_term_def wf_theory_imp_is_std_sig typ_of_def typ_ok_def wf_type_iff_typ_ok_sig)

lemma axioms_terms_ok: "wf_theory thy \<Longrightarrow> A\<in>axioms thy \<Longrightarrow> term_ok thy A"
  using wt_term_def by (cases thy rule: theory_full_exhaust) simp

lemma axioms_typ_of_propT: "wf_theory thy \<Longrightarrow> A\<in>axioms thy \<Longrightarrow> typ_of A = Some propT"
  using has_typ_iff_typ_of by (cases thy rule: theory_full_exhaust) simp

lemma propT_ok[simp]: "wf_theory \<Theta> \<Longrightarrow> typ_ok \<Theta> propT"
  using term_ok_imp_typ_ok wf_theory.elims(2)
  by (metis sig.simps term_ok_eq_ax(4) typ_of_eq_ax(4))

lemma term_ok_mk_eqD: "term_ok \<Theta> (mk_eq s t) \<Longrightarrow> term_ok \<Theta> s \<and> term_ok \<Theta> t"
  using term_ok'.simps(4) wt_term_def typ_of_def by (auto simp add: bind_eq_Some_conv)
lemma term_ok_app_eqD: "term_ok \<Theta> (s $ t) \<Longrightarrow> term_ok \<Theta> s \<and> term_ok \<Theta> t"
  using term_ok'.simps(4) wt_term_def typ_of_def by (auto simp add: bind_eq_Some_conv)

lemma wf_type_Type_imp_mgd: 
  "wf_sig \<Sigma> \<Longrightarrow> wf_type \<Sigma> (Ty n Ts) \<Longrightarrow> tcsigs (osig \<Sigma>) n \<noteq> None"
  by (cases \<Sigma>) (auto split: option.splits)

lemma term_ok_eta_expand:
  assumes "wf_theory \<Theta>" "term_ok \<Theta> f" "typ_of f = Some (\<tau> \<rightarrow> \<tau>')" "typ_ok \<Theta> \<tau>"
  shows "term_ok \<Theta> (Abs \<tau> (f $ Bv 0))"
  using assms typ_of_eta_expand by (auto simp add: wt_term_def)

lemma term_ok'_incr_bv: "term_ok' \<Sigma> t \<Longrightarrow> term_ok' \<Sigma> (incr_bv inc lev t)"
  by (induction inc lev t rule: incr_bv.induct) auto

lemma term_ok'_subst_bv2: "term_ok' \<Sigma> s \<Longrightarrow> term_ok' \<Sigma> u \<Longrightarrow> term_ok' \<Sigma> (subst_bv2 s lev u)"
  by (induction s lev u rule: subst_bv2.induct) (auto simp add: term_ok'_incr_bv)

lemma term_ok'_subst_bv: "term_ok' \<Sigma> (Abs T t) \<Longrightarrow> term_ok' \<Sigma> (subst_bv (Fv x T) t)"
  by (simp add: substn_subst_0' term_ok'_subst_bv2)
lemma term_ok_subst_bv: "term_ok \<Theta> (Abs T t) \<Longrightarrow> term_ok \<Theta> (subst_bv (Fv x T) t)"
  apply (simp add: term_ok'_subst_bv wt_term_def)
  using subst_bv_def typ_of1_subst_bv_gen' typ_of_Abs_body_typ' typ_of_def by fastforce

lemma term_ok_subst_bv2_0: "term_ok \<Theta> (Abs T t) \<Longrightarrow> term_ok \<Theta> (subst_bv2 t 0 (Fv x T))"
  apply (clarsimp simp add: term_ok'_subst_bv2 wt_term_def)
  using substn_subst_0' typ_of1_subst_bv_gen' typ_of_Abs_body_typ' typ_of_def
    wt_term_def term_ok_subst_bv by auto

lemma has_sort_empty[simp]:
  assumes "wf_sig \<Sigma>" "wf_type \<Sigma> T"
  shows "has_sort (osig \<Sigma>) T full_sort" 
proof(cases T)
  case (Ty n Ts)
  obtain cl tcs where cltcs: "osig \<Sigma> = (cl, tcs)"
    by fastforce
  obtain mgd where mgd: "tcsigs (osig \<Sigma>) n = Some mgd"
    using wf_type_Type_imp_mgd assms Ty by blast
  show ?thesis
    using mgd cltcs by (auto simp add: Ty intro!: has_sort_Ty)
next
  case (Tv v S)
  then show ?thesis 
    by (cases "osig \<Sigma>") (auto simp add: sort_leq_def split: prod.splits)
qed

lemma typ_Fv_of_full_sort[simp]:
  "wf_theory \<Theta> \<Longrightarrow> term_ok \<Theta> (Fv v T) \<Longrightarrow> has_sort (osig (sig \<Theta>)) T full_sort"
  by (simp add: wt_term_def wf_theory_imp_wf_sig)

end
