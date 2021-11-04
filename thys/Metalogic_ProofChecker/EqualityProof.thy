section "Derived rules on equality and normalization"

theory EqualityProof
  imports Logic
begin

(* Check for automation here, steps seem very small*)

lemma proves_eq_reflexive_pre:
  assumes "wf_theory \<Theta>"
  assumes "term_ok \<Theta> t"
  shows "\<Theta>, {} \<turnstile> mk_eq t t"
proof-
  have "eq_reflexive_ax \<in> axioms \<Theta>"
    using assms by (cases \<Theta> rule: theory_full_exhaust) auto
  moreover obtain \<tau> where \<tau>: "typ_of t = Some \<tau>" using assms wt_term_def by auto
  moreover hence "typ_ok \<Theta> \<tau>" using assms term_ok_imp_typ_ok by blast       
  ultimately have "\<Theta>, {} \<turnstile> subst_typ' [((Var (STR '''a'', 0), full_sort), \<tau>)] eq_reflexive_ax"
    using axiom_subst_typ' assms by (simp del: term_ok_def)
  hence "\<Theta>, {} \<turnstile> subst_term [((Var (STR ''x'', 0), \<tau>), t)] 
    (subst_typ' [((Var (STR '''a'', 0), full_sort), \<tau>)] eq_reflexive_ax)"
    using \<tau> assms(1) assms(2) inst_var by auto
  moreover have "subst_term [((Var (STR ''x'', 0), \<tau>), t)] 
    (subst_typ' [((Var (STR '''a'', 0), full_sort), \<tau>)] eq_reflexive_ax)
    = mk_eq t t"
    using \<tau> by (simp add: eq_axs_def typ_of_def) 
  ultimately show ?thesis 
    by simp
qed

lemma unsimp_context: "\<Gamma> = {} \<union> \<Gamma>"
  by simp

lemma proves_eq_reflexive:
  assumes "wf_theory \<Theta>"
  assumes "term_ok \<Theta> t"
  assumes "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq t t"
  by (subst unsimp_context) (use assms proves_eq_reflexive_pre weaken_proves_set in blast)

lemma proves_eq_symmetric_pre:
  assumes "wf_theory \<Theta>"
  assumes "term_ok \<Theta> t"
  assumes "term_ok \<Theta> s"
  assumes "typ_of s = typ_of t"
  shows "\<Theta>, {} \<turnstile> mk_eq s t \<longmapsto> mk_eq t s"
proof-

  have "eq_symmetric_ax \<in> axioms \<Theta>"
    using assms by (cases \<Theta> rule: theory_full_exhaust) auto
  moreover obtain \<tau> where \<tau>: "typ_of t = Some \<tau>" using assms wt_term_def by auto

  moreover hence "typ_ok \<Theta> \<tau>" using assms term_ok_imp_typ_ok by blast
  ultimately have "\<Theta>, {} \<turnstile> subst_typ' [((Var (STR '''a'', 0), full_sort), \<tau>)] eq_symmetric_ax"
    using assms axiom_subst_typ' by (auto simp del: term_ok_def)
  hence "\<Theta>, {} \<turnstile> subst_term [((Var (STR ''x'', 0), \<tau>), s), ((Var (STR ''y'', 0), \<tau>), t)]
    (subst_typ' [((Var (STR '''a'', 0), full_sort), \<tau>)] eq_symmetric_ax)"
    using \<tau> \<open>typ_ok \<Theta> \<tau>\<close> term_ok_var assms by (fastforce intro!: inst_var_multiple simp add: eq_symmetric_ax_def)
  thus ?thesis
    using \<tau> assms(4) by (simp add: eq_axs_def typ_of_def)
qed

lemma proves_eq_symmetric:
  assumes "wf_theory \<Theta>"
  assumes "term_ok \<Theta> t"
  assumes "term_ok \<Theta> s"
  assumes "typ_of s = typ_of t"
  assumes "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq s t \<longmapsto> mk_eq t s"
  by (subst unsimp_context) (use assms proves_eq_symmetric_pre weaken_proves_set in blast)

lemma proves_eq_symmetric2':
  assumes "wf_theory \<Theta>"
  assumes "term_ok \<Theta> (mk_eq s t)"
  assumes "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq s t \<longmapsto> mk_eq t s"
proof-
  have "term_ok \<Theta> s" "term_ok \<Theta> t"
    using assms wt_term_def term_ok_mk_eqD by blast+ 
  moreover have "typ_of s = typ_of t" 
    using assms by (cases \<Theta> rule: theory_full_exhaust)
      (auto simp add: tinstT_def typ_of_def wt_term_def bind_eq_Some_conv)
  ultimately show ?thesis
    using proves_eq_symmetric assms by blast
qed

lemma proves_eq_symmetric_rule:
  assumes "wf_theory \<Theta>"
  assumes "term_ok \<Theta> t"
  assumes "term_ok \<Theta> s"
  assumes "typ_of s = typ_of t"
  assumes "\<Theta>, \<Gamma> \<turnstile> mk_eq s t"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq t s"
  using proves.implies_elim[OF proves_eq_symmetric[OF assms(1-4), of \<Gamma>] assms(5), OF ctxt] by simp  

lemma proves_eq_transitive_pre:
  assumes "wf_theory \<Theta>"
  assumes "term_ok \<Theta> s"
  assumes "term_ok \<Theta> t"
  assumes "term_ok \<Theta> u"
  assumes "typ_of s = typ_of t" "typ_of t = typ_of u"
  shows "\<Theta>, {} \<turnstile> mk_eq s t \<longmapsto> mk_eq t u \<longmapsto> mk_eq s u"
proof-
  have "eq_transitive_ax \<in> axioms \<Theta>"
    using assms by (cases \<Theta> rule: theory_full_exhaust) auto
  moreover obtain \<tau> where \<tau>: "typ_of t = Some \<tau>" using assms wt_term_def by auto
  moreover hence ok: "typ_ok \<Theta> \<tau>" using assms term_ok_imp_typ_ok by blast
  ultimately have "\<Theta>, {} \<turnstile> subst_typ' [((Var (STR '''a'', 0), full_sort), \<tau>)] eq_transitive_ax"
    using assms axiom_subst_typ' by (auto simp del: term_ok_def)
  hence "\<Theta>, {} \<turnstile> subst_term [((Var (STR ''x'', 0), \<tau>), s), ((Var (STR ''y'', 0), \<tau>), t), 
      ((Var (STR ''z'', 0), \<tau>), u)] 
    (subst_typ' [((Var (STR '''a'', 0), full_sort), \<tau>)] eq_transitive_ax)"
      using \<tau> assms ok term_ok_var by (fastforce intro!: inst_var_multiple simp add: eq_transitive_ax_def)
  moreover have "subst_term [((Var (STR ''x'', 0), \<tau>), s), ((Var (STR ''y'', 0), \<tau>), t), 
      ((Var (STR ''z'', 0), \<tau>), u)] 
    (subst_typ' [((Var (STR '''a'', 0), full_sort), \<tau>)] eq_transitive_ax)
    = mk_eq s t \<longmapsto> mk_eq t u \<longmapsto> mk_eq s u"
    using \<tau> assms(5-6) apply (simp add: eq_axs_def typ_of_def)
    by (metis option.sel the_default.simps(2))
  ultimately show ?thesis
    by simp
qed

lemma proves_eq_transitive:
  assumes "wf_theory \<Theta>"
  assumes "term_ok \<Theta> s"
  assumes "term_ok \<Theta> t"
  assumes "term_ok \<Theta> u"
  assumes "typ_of s = typ_of t" "typ_of t = typ_of u"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq s t \<longmapsto> mk_eq t u \<longmapsto> mk_eq s u"
  by (subst unsimp_context) (use assms proves_eq_transitive_pre weaken_proves_set in blast)
    
lemma proves_eq_transitive2:
  assumes "wf_theory \<Theta>"
  assumes "term_ok \<Theta> (mk_eq s t)"
  assumes "term_ok \<Theta> (mk_eq t u)"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq s t \<longmapsto> mk_eq t u \<longmapsto> mk_eq s u"
proof-
  have "term_ok \<Theta> s" "term_ok \<Theta> t" "term_ok \<Theta> u"
    using assms wt_term_def term_ok_mk_eqD by blast+
  moreover have "typ_of s = typ_of t"
    using assms by (cases \<Theta> rule: theory_full_exhaust)
      (auto simp add: tinstT_def typ_of_def wt_term_def bind_eq_Some_conv)
  moreover have "typ_of t = typ_of u" 
    using assms by (cases \<Theta> rule: theory_full_exhaust)
      (auto simp add: tinstT_def typ_of_def wt_term_def bind_eq_Some_conv)
  ultimately show ?thesis using proves_eq_transitive assms by blast
qed

lemma proves_eq_transitive_rule:
  assumes "wf_theory \<Theta>"
  assumes "term_ok \<Theta> s"
  assumes "term_ok \<Theta> t"
  assumes "term_ok \<Theta> u"
  assumes "typ_of s = typ_of t" "typ_of t = typ_of u"
  assumes "\<Theta>, \<Gamma> \<turnstile> mk_eq s t" "\<Theta>, \<Gamma> \<turnstile> mk_eq t u"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq s u"
proof-
  note 1 = proves_eq_transitive[OF assms(1-6), of \<Gamma>]
  note 2 = proves.implies_elim[OF 1 assms(7)]
  note 3 = proves.implies_elim[OF 2 assms(8)]
  thus ?thesis using ctxt by simp
qed

lemma proves_eq_intr_pre:
  assumes thy: "wf_theory \<Theta>"
  assumes A: "term_ok \<Theta> A" "typ_of A = Some propT"
  assumes B: "term_ok \<Theta> B" "typ_of B = Some propT"
  shows "\<Theta>, {} \<turnstile> (A \<longmapsto> B) \<longmapsto> (B \<longmapsto> A) \<longmapsto> mk_eq A B"
proof-
  have closed: "is_closed A" "is_closed B"
    using assms(3) assms(5) typ_of_imp_closed by auto
  have "eq_intr_ax \<in> axioms \<Theta>" 
    using thy by (cases \<Theta> rule: theory_full_exhaust) auto

  hence 1: "\<Theta>, {} \<turnstile> eq_intr_ax"
    by (simp add: axiom' thy)
  hence "\<Theta>, {} \<turnstile> subst_term [((Var (STR ''A'', 0), propT), A), ((Var (STR ''B'', 0), propT), B)]
    eq_intr_ax"
    using assms term_ok_var propT_ok by (fastforce intro!: inst_var_multiple simp add: eq_intr_ax_def)
  thus ?thesis using assms by (simp add: eq_axs_def typ_of_def)
qed

lemma proves_eq_intr:
  assumes thy: "wf_theory \<Theta>"
  assumes A: "term_ok \<Theta> A" "typ_of A = Some propT"
  assumes B: "term_ok \<Theta> B" "typ_of B = Some propT"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> (A \<longmapsto> B) \<longmapsto> (B \<longmapsto> A) \<longmapsto> mk_eq A B"
  by (subst unsimp_context) (use assms proves_eq_intr_pre weaken_proves_set in blast)

lemma proves_eq_intr_rule:
  assumes thy: "wf_theory \<Theta>"
  assumes A: "term_ok \<Theta> A" "typ_of A = Some propT"
  assumes B: "term_ok \<Theta> B" "typ_of B = Some propT"
  assumes "\<Theta>, \<Gamma> \<turnstile> (A \<longmapsto> B)" "\<Theta>, \<Gamma> \<turnstile> (B \<longmapsto> A)"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq A B"
proof-
  note 1 = proves_eq_intr[OF assms(1-5), of \<Gamma>]
  note 2 = proves.implies_elim[OF 1 assms(6)]
  note 3 = proves.implies_elim[OF 2 assms(7)]
  thus ?thesis using ctxt by simp
qed

lemma proves_eq_elim_pre:
  assumes thy: "wf_theory \<Theta>"
  assumes A: "term_ok \<Theta> A" "typ_of A = Some propT"
  assumes B: "term_ok \<Theta> B" "typ_of B = Some propT"
  shows "\<Theta>, {} \<turnstile> mk_eq A B \<longmapsto> A \<longmapsto> B"
proof-
  have closed: "is_closed A" "is_closed B"
    by (simp_all add: assms(3) assms(5) typ_of_imp_closed)
  have "eq_elim_ax \<in> axioms \<Theta>" 
    using thy by (cases \<Theta> rule: theory_full_exhaust) auto
  hence 1: "\<Theta>, {} \<turnstile> eq_elim_ax"
    by (simp add: axiom' thy)
  hence "\<Theta>, {} \<turnstile> subst_term [((Var (STR ''A'', 0), propT), A), ((Var (STR ''B'', 0), propT), B)]
    eq_elim_ax"
    using assms term_ok_var propT_ok by (fastforce intro!: inst_var_multiple simp add: eq_elim_ax_def)
  thus ?thesis 
    using assms by (simp add: eq_axs_def typ_of_def)
qed

lemma proves_eq_elim:
  assumes thy: "wf_theory \<Theta>"
  assumes A: "term_ok \<Theta> A" "typ_of A = Some propT"
  assumes B: "term_ok \<Theta> B" "typ_of B = Some propT"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq A B \<longmapsto> A \<longmapsto> B"
  by (subst unsimp_context) (use assms proves_eq_elim_pre weaken_proves_set in blast)

lemma proves_eq_elim_rule:
  assumes thy: "wf_theory \<Theta>"
  assumes A: "term_ok \<Theta> A" "typ_of A = Some propT"
  assumes B: "term_ok \<Theta> B" "typ_of B = Some propT"
  assumes "\<Theta>, \<Gamma> \<turnstile> mk_eq A B"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> A \<longmapsto> B"
  using proves.implies_elim[OF proves_eq_elim[OF assms(1-5)] assms(6), of \<Gamma>, OF ctxt] by simp 

lemma proves_eq_elim2_rule:
  assumes thy: "wf_theory \<Theta>"
  assumes A: "term_ok \<Theta> A" "typ_of A = Some propT"
  assumes B: "term_ok \<Theta> B" "typ_of B = Some propT"
  assumes "\<Theta>, \<Gamma> \<turnstile> mk_eq A B"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> B \<longmapsto> A"
proof-
  have "\<Theta>, \<Gamma> \<turnstile> mk_eq B A"
    by (rule proves_eq_symmetric_rule) (use assms in simp_all)
  thus ?thesis by (intro proves_eq_elim_rule) (use assms in simp_all)
qed

lemma proves_eq_combination_pre:
  assumes thy: "wf_theory \<Theta>"
  assumes f: "term_ok \<Theta> f" "typ_of f = Some (\<tau> \<rightarrow> \<tau>')"
  assumes g: "term_ok \<Theta> g" "typ_of g = Some (\<tau> \<rightarrow> \<tau>')"
  assumes x: "term_ok \<Theta> x" "typ_of x = Some \<tau>"
  assumes y: "term_ok \<Theta> y" "typ_of y = Some \<tau>"
  shows "\<Theta>, {} \<turnstile> mk_eq f g \<longmapsto> mk_eq x y \<longmapsto> mk_eq (f $ x) (g $ y)"
proof-
  have ok: "typ_ok \<Theta> \<tau>" "typ_ok \<Theta> (\<tau> \<rightarrow> \<tau>')" "typ_ok \<Theta> \<tau>'"
    using term_ok_betapply term_ok_imp_typ_ok thy typ_of_betaply thy x f by blast+

  have "eq_combination_ax \<in> axioms \<Theta>" 
    using thy by (cases \<Theta> rule: theory_full_exhaust) auto
  moreover have "typ_ok \<Theta> \<tau>" "typ_ok \<Theta> \<tau>'"
    using assms term_ok_imp_typ_ok thy term_ok_betapply typ_of_betaply by meson+
  ultimately have 1: "\<Theta>, {} \<turnstile> subst_typ' 
    [((Var (STR '''a'', 0), full_sort), \<tau>), ((Var (STR '''b'', 0), full_sort), \<tau>')] eq_combination_ax"
    using assms axiom_subst_typ' by (simp del: term_ok_def)
  hence "\<Theta>, {} \<turnstile> subst_term 
    [((Var (STR ''f'', 0), \<tau> \<rightarrow> \<tau>'), f), ((Var (STR ''g'', 0), \<tau> \<rightarrow> \<tau>'), g),
      ((Var (STR ''x'', 0), \<tau>), x), ((Var (STR ''y'', 0), \<tau>), y)]
    (subst_typ' [((Var (STR '''a'', 0), full_sort), \<tau>), ((Var (STR '''b'', 0), full_sort), \<tau>')] 
    eq_combination_ax)"
    using assms term_ok_var ok by (fastforce intro!: inst_var_multiple simp add: eq_combination_ax_def)
  thus ?thesis 
    using assms by (simp add: eq_axs_def typ_of_def)
qed

lemma proves_eq_combination:
  assumes thy: "wf_theory \<Theta>"
  assumes f: "term_ok \<Theta> f" "typ_of f = Some (\<tau> \<rightarrow> \<tau>')"
  assumes g: "term_ok \<Theta> g" "typ_of g = Some (\<tau> \<rightarrow> \<tau>')"
  assumes x: "term_ok \<Theta> x" "typ_of x = Some \<tau>"
  assumes y: "term_ok \<Theta> y" "typ_of y = Some \<tau>"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq f g \<longmapsto> mk_eq x y \<longmapsto> mk_eq (f $ x) (g $ y)"
  by (subst unsimp_context) (use assms proves_eq_combination_pre weaken_proves_set in blast)

(* Can probably drop a whole lot of assumptions as thy are deriveable from the last one*)
lemma proves_eq_combination_rule:
  assumes thy: "wf_theory \<Theta>"
  assumes f: "term_ok \<Theta> f" "typ_of f = Some (\<tau> \<rightarrow> \<tau>')"
  assumes g: "term_ok \<Theta> g" "typ_of g = Some (\<tau> \<rightarrow> \<tau>')"
  assumes x: "term_ok \<Theta> x" "typ_of x = Some \<tau>"
  assumes y: "term_ok \<Theta> y" "typ_of y = Some \<tau>"
  assumes "\<Theta>, \<Gamma> \<turnstile> mk_eq f g" "\<Theta>, \<Gamma> \<turnstile> mk_eq x y"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq (f $ x) (g $ y)"
proof-
  note 1 = proves_eq_combination[OF assms(1-9), of \<Gamma>]
  note 2 = proves.implies_elim[OF 1 assms(10)]
  note 3 = proves.implies_elim[OF 2 assms(11)]
  thus ?thesis using ctxt by simp
qed

lemma proves_eq_combination_rule_better:
  assumes thy: "wf_theory \<Theta>"
  assumes "\<Theta>, \<Gamma> \<turnstile> mk_eq f g" "\<Theta>, \<Gamma> \<turnstile> mk_eq x y"
  assumes f: "typ_of f = Some (\<tau> \<rightarrow> \<tau>')"
  assumes x: "typ_of x = Some \<tau>"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq (f $ x) (g $ y)"
proof-
  have ok_Apps: "term_ok \<Theta> (mk_eq f g)" "term_ok \<Theta> (mk_eq x y)"
    using assms(2-3) proved_terms_well_formed_pre by auto 
  hence tyy: "typ_of y = Some \<tau>" and tyg: "typ_of g = Some (\<tau> \<rightarrow> \<tau>')"
    using term_ok_mk_eq_same_typ thy x f term_okD1 by metis+
  moreover have "term_ok \<Theta> x" "term_ok \<Theta> y" "term_ok \<Theta> f" "term_ok \<Theta> g"
    using ok_Apps term_ok_mk_eqD by blast+
  ultimately show ?thesis using proves_eq_combination_rule assms by simp
qed

lemma proves_eq_mp_rule:
  assumes thy: "wf_theory \<Theta>"
  assumes A: "term_ok \<Theta> A" "typ_of A = Some propT"
  assumes B: "term_ok \<Theta> B" "typ_of B = Some propT"
  assumes eq: "\<Theta>, \<Gamma> \<turnstile> mk_eq A B"
  assumes pA: "\<Theta>, \<Gamma> \<turnstile> A"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> B"
proof-
  have "\<Theta>, \<Gamma> \<turnstile> A \<longmapsto> B" using proves_eq_elim_rule[OF assms(1-5) eq ctxt] .
  thus "\<Theta>, \<Gamma> \<turnstile> B" using proves.implies_elim pA by fastforce
qed

lemma proves_eq_mp_rule_better:
  assumes thy: "wf_theory \<Theta>"
  assumes eq: "\<Theta>, \<Gamma> \<turnstile> mk_eq A B"
  assumes pA: "\<Theta>, \<Gamma> \<turnstile> A"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> B"
  by (metis ctxt eq pA proved_terms_well_formed(1) proved_terms_well_formed(2)
      proves_eq_mp_rule term_ok_mk_eqD term_ok_mk_eq_same_typ thy)

lemma proves_subst_rule:
  assumes thy: "wf_theory \<Theta>"
  assumes x: "term_ok \<Theta> x" "typ_of x = Some \<tau>"
  assumes y: "term_ok \<Theta> y" "typ_of y = Some \<tau>"
  assumes P: "term_ok \<Theta> P" "typ_of P = Some (\<tau> \<rightarrow> propT)"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma> . term_ok \<Theta> A" "\<forall>A\<in>\<Gamma> . typ_of A = Some propT"
  assumes eq: "\<Theta>, \<Gamma> \<turnstile> mk_eq x y"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq (P $ x) (P $ y)"
proof-
  have "\<Theta>, \<Gamma> \<turnstile> mk_eq P P" using assms proves_eq_reflexive by blast
  thus ?thesis using proves_eq_combination_rule assms by blast
qed


lemma proves_beta_step_rule: 
  assumes thy: "wf_theory \<Theta>"
  assumes abs: "term_ok \<Theta> (Abs T t)" "\<Theta>, \<Gamma> \<turnstile> (Abs T t) $ x"
  assumes x: "term_ok \<Theta> x" "typ_of x = Some T"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> subst_bv x t"
proof-
  have "\<Theta>, \<Gamma> \<turnstile> mk_eq ((Abs T t) $ x) (subst_bv x t)"
    using proves.\<beta>_conversion assms by (simp add: term_okD1)
  moreover have "term_ok \<Theta> (Abs T t $ x)" and tyAbs: "typ_of (Abs T t $ x) = Some propT" 
    using abs(2) proved_terms_well_formed by simp_all
  moreover have tySub: "typ_of (subst_bv x t) = Some propT"
    using tyAbs unfolding subst_bv_def typ_of_def 
    using typ_of1_subst_bv_gen' by (auto simp add: bind_eq_Some_conv split: if_splits)
  moreover have "term_ok \<Theta> (subst_bv x t)" 
  proof-
    have "term_ok' (sig \<Theta>) t"
      using assms(2) term_ok'.simps(5) wt_term_def term_ok_def by blast
    hence "term_ok' (sig \<Theta>) (subst_bv x t)"
      using term_ok'_subst_bv1 x(1) by (simp add: term_okD1 subst_bv_def) 
    thus ?thesis 
      using x(1) wt_term_def term_ok'_subst_bv1 subst_bv_def tySub term_okD1 by simp
  qed
  ultimately show ?thesis apply -
    apply (rule proves_eq_mp_rule[where A="(Abs T t) $ x"])
    using assms by simp_all
qed

(* TODO: Remember the name of this rule *)
lemma proves_add_param_rule:
  assumes thy: "wf_theory \<Theta>"
  assumes ctxt: "finite \<Gamma>"
  assumes eq: "\<Theta>, \<Gamma> \<turnstile> mk_eq f g" "typ_of f = Some (\<tau> \<rightarrow> \<tau>')"
  assumes type: "typ_ok \<Theta> \<tau>"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> (Ct STR ''Pure.all'' ((\<tau> \<rightarrow> propT) \<rightarrow> propT) $ 
      (Abs \<tau> (mk_eq' \<tau>' (f $ Bv 0) (g $ Bv 0))))"
proof-
  have term_ok: "term_ok \<Theta> (mk_eq f g)"
    using eq(1) proved_terms_well_formed_pre by blast
  hence term_ok': "term_ok \<Theta> f" "term_ok \<Theta> g"
    apply (simp add: eq(2) wt_term_def)
    using \<open>term_ok \<Theta> (mk_eq f g)\<close> wt_term_def typ_of_def  term_ok_app_eqD by blast
  hence "typ_of f = typ_of g"
    using thy term_ok by (cases \<Theta> rule: theory_full_exhaust)
      (auto simp add: tinstT_def typ_of_def wt_term_def bind_eq_Some_conv)
  hence type': "typ_of g = Some (\<tau> \<rightarrow> \<tau>')" 
    using eq(2) by simp

  obtain x where "x \<notin> fst ` (fv (mk_eq f g) \<union> FV \<Gamma>)"
    using finite_fv finite_FV infinite_fv_UNIV variant_variable_fresh ctxt
    by (meson finite_Un finite_imageI)
  hence free: "(x,\<tau>) \<notin> fv (mk_eq f g) \<union> FV \<Gamma>" 
    by force
  hence "\<Theta>, \<Gamma> \<turnstile> mk_eq (Fv x \<tau>) (Fv x \<tau>)"
    using ctxt proves_eq_reflexive term_ok_var thy type by presburger
  hence "\<Theta>, \<Gamma> \<turnstile> mk_eq (f $ Fv x \<tau>) (g $ Fv x \<tau>)"
    apply -
    apply (rule proves_eq_combination_rule[where \<tau>'=\<tau>'])
    using assms term_ok' type' by (simp_all del: term_ok_def)
  hence "\<Theta>, \<Gamma> \<turnstile> mk_all x \<tau> (mk_eq (f $ Fv x \<tau>) (g $ Fv x \<tau>))" 
    apply -
    apply (rule proves.forall_intro)
    using thy eq type free by simp_all
  moreover have "mk_all x \<tau> (mk_eq (f $ Fv x \<tau>) (g $ Fv x \<tau>)) 
    = (Ct STR ''Pure.all'' ((\<tau> \<rightarrow> propT) \<rightarrow> propT) $ 
      (Abs \<tau> (mk_eq' \<tau>' (f $ Bv 0) (g $ Bv 0))))"
    using free eq type type' bind_fv2_changed
    by (fastforce simp add: bind_fv_def bind_fv_unchanged typ_of_def)
  ultimately show ?thesis
    by simp
qed

lemma proves_add_abs_rule:
  assumes thy: "wf_theory \<Theta>"
  assumes ctxt: "finite \<Gamma>"
  assumes eq: "\<Theta>, \<Gamma> \<turnstile> mk_eq f g" "typ_of f = Some (\<tau> \<rightarrow> \<tau>')"
  assumes type: "typ_ok \<Theta> \<tau>"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq (Abs \<tau> (f $ Bv 0)) (Abs \<tau> (g $ Bv 0))" 
proof-
  have ok: "term_ok \<Theta> f" "term_ok \<Theta> g"
    using eq(1) proved_terms_well_formed(2) term_ok_mk_eqD by blast+
  have g_ty: "typ_of g = Some (\<tau> \<rightarrow> \<tau>')"
    by (metis eq(1) eq(2) proved_terms_well_formed(2) term_ok_mk_eq_same_typ thy)
  hence closed: "is_closed f" "is_closed g"
    using eq(2) typ_of_imp_closed by blast+

  have ok': "term_ok \<Theta> (Abs \<tau> (f $ Bv 0))" "term_ok \<Theta> (Abs \<tau> (g $ Bv 0))"
    using type term_ok_eta_expand ok thy eq(2) g_ty by blast+

  have ok_ind: "wf_term (sig \<Theta>) f"  "wf_term (sig \<Theta>) g"
    using ok wt_term_def by simp_all

  note 1 = proves.eta[OF thy ok_ind(1) typ_of_imp_has_typ[OF eq(2)], of \<Gamma>]
  note 2 = proves.eta[OF thy ok_ind(2) typ_of_imp_has_typ[OF g_ty], of \<Gamma>]

  have simp': "subst_bv x f = f" "subst_bv x g = g" for x
    using ok term_ok_subst_bv_no_change by auto

  have s2: "\<Theta>,\<Gamma> \<turnstile> mk_eq g (Abs \<tau> (g $ Bv 0))" 
    apply (rule proves_eq_symmetric_rule)
    using "2"  ok'(2) ok(2) thy typ_of_eta_expand[OF g_ty] g_ty ctxt by (simp_all add: simp'(2))

  have tr1: "\<Theta>,\<Gamma> \<turnstile> mk_eq (Abs \<tau> (f $ Bv 0)) g" 
    using 1 eq(1) g_ty ok'(1) ok(1) ok(2) proves_eq_transitive_rule[OF thy _ _ _ _ _ _ _ ctxt]
      typ_of_eta_expand[OF eq(2)] eq(2) by (fastforce simp add: simp'(1))
  
  show ?thesis 
    using tr1 s2 proves_eq_transitive_rule[OF thy ok'(1) ok(2) ok'(2)] typ_of_eta_expand eq(2) g_ty
    ctxt
    by simp
qed

lemma proves_inst_bound_rule:
  assumes thy: "wf_theory \<Theta>"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma> . term_ok \<Theta> A" "\<forall>A\<in>\<Gamma> . typ_of A = Some propT"
  assumes eq: "\<Theta>, \<Gamma> \<turnstile> mk_eq (Abs \<tau> f) (Abs \<tau> g)" "typ_of (Abs \<tau> f) = Some (\<tau> \<rightarrow> \<tau>')"
  assumes x: "term_ok \<Theta> x" "typ_of x = Some \<tau>"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq (subst_bv x f) (subst_bv x g)"
proof-
  have "term_ok \<Theta> (mk_eq (Abs \<tau> f) (Abs \<tau> g))"
    using eq(1) proved_terms_well_formed(2) by blast
  hence "term_ok \<Theta> (Abs \<tau> f)" "term_ok \<Theta> (Abs \<tau> g)"
    using term_ok_mk_eqD by blast+
  hence "typ_of (Abs \<tau> f) = typ_of (Abs \<tau> g)"
    using thy \<open>term_ok \<Theta> (mk_eq (Abs \<tau> f) (Abs \<tau> g))\<close> by (cases \<Theta> rule: theory_full_exhaust)
      (auto simp add: tinstT_def typ_of_def wt_term_def bind_eq_Some_conv)
  hence "typ_of (Abs \<tau> g) = Some (\<tau> \<rightarrow> \<tau>')"
    using eq(2) by simp

  have "\<Theta>, \<Gamma> \<turnstile> mk_eq x x" 
    by (simp add: ctxt proves_eq_reflexive thy x(1) del: term_ok_def)
  hence 1: "\<Theta>, \<Gamma> \<turnstile> mk_eq (Abs \<tau> f $ x) (Abs \<tau> g $ x)"
    using proves_eq_combination_rule[OF thy \<open>term_ok \<Theta> (Abs \<tau> f)\<close> eq(2) \<open>term_ok \<Theta> (Abs \<tau> g)\<close> 
        \<open>typ_of (Abs \<tau> g) = Some (\<tau> \<rightarrow> \<tau>')\<close> x x eq(1) _ ctxt]
    by blast 

  have "\<Theta>, \<Gamma> \<turnstile> mk_eq (Abs \<tau> f $ x) (subst_bv x f)"
    apply (rule \<beta>_conversion)
    using thy x \<open>term_ok \<Theta> (Abs \<tau> f)\<close> by (simp_all add: wt_term_def)
  
  have "term_ok \<Theta> (Abs \<tau> f $ x)" using \<open>term_ok \<Theta> (Abs \<tau> f)\<close> x
      \<open>\<Theta>,\<Gamma> \<turnstile> mk_eq (Abs \<tau> f $ x) (Abs \<tau> g $ x)\<close>  proved_terms_well_formed(1) 
      wt_term_def typ_of1_split_App_obtains typ_of_def 
    by (meson proved_terms_well_formed(2) term_ok_mk_eqD)
  have "term_ok \<Theta> (Abs \<tau> g $ x)" using \<open>term_ok \<Theta> (Abs \<tau> g)\<close> x
    \<open>\<Theta>,\<Gamma> \<turnstile> mk_eq (Abs \<tau> f $ x) (Abs \<tau> g $ x)\<close> proved_terms_well_formed(1) 
    wt_term_def typ_of1_split_App_obtains typ_of_def
    by (meson proved_terms_well_formed(2) term_ok_mk_eqD)
 
  have "typ_of (subst_bv x f) = Some \<tau>'"
    using \<open>typ_of (Abs \<tau> f) = Some (\<tau> \<rightarrow> \<tau>')\<close> x(2) typ_of_def  typ_of_betapply by auto
  moreover have "term_ok' (sig \<Theta>) (subst_bv x f)"
    using \<open>term_ok \<Theta> (Abs \<tau> f)\<close> substn_subst_0' term_ok'_subst_bv2 wt_term_def x(1) by auto
  ultimately have "term_ok \<Theta> (subst_bv x f)"
    by (simp add: wt_term_def)
  
  have "typ_of (Abs \<tau> f $ x) = typ_of (subst_bv x f)"
    using \<open>typ_of (Abs \<tau> f) = typ_of (Abs \<tau> g)\<close> typ_of_def \<open>typ_of (Abs \<tau> g) = Some (\<tau> \<rightarrow> \<tau>')\<close>
      \<open>typ_of (subst_bv x f) = Some \<tau>'\<close> typ_of_Abs_body_typ' x(2) by fastforce
    
  have "typ_of (Abs \<tau> f $ x) = typ_of (Abs \<tau> g $ x)"
    using \<open>typ_of (Abs \<tau> f) = typ_of (Abs \<tau> g)\<close> typ_of_def by auto

  have 2: "\<Theta>, \<Gamma> \<turnstile> mk_eq (subst_bv x f) (Abs \<tau> f $ x)"
    apply - apply (rule proves_eq_symmetric_rule)
    using thy apply blast
    using \<open>term_ok \<Theta> (subst_bv x f)\<close> apply blast
    using \<open>term_ok \<Theta> (Abs \<tau> f $ x)\<close> apply blast
    using \<open>typ_of (Abs \<tau> f $ x) = typ_of (subst_bv x f)\<close> apply blast
    using \<open>\<Theta>,\<Gamma> \<turnstile> mk_eq (Abs \<tau> f $ x) (subst_bv x f)\<close> apply blast
    using ctxt by blast+

  have 3: "\<Theta>, \<Gamma> \<turnstile> mk_eq (Abs \<tau> g $ x) (subst_bv x g)"
    apply (rule \<beta>_conversion)
    using thy x \<open>term_ok \<Theta> (Abs \<tau> g)\<close> by (simp_all add: wt_term_def)

  have "term_ok \<Theta> (subst_bv x g)" 
    using \<open>term_ok \<Theta> (Abs \<tau> g $ x)\<close> \<open>term_ok \<Theta> (Abs \<tau> g)\<close> \<open>typ_of (Abs \<tau> f $ x) = typ_of (Abs \<tau> g $ x)\<close> 
      \<open>typ_of (Abs \<tau> f $ x) = typ_of (subst_bv x f)\<close> \<open>typ_of (Abs \<tau> g) = Some (\<tau> \<rightarrow> \<tau>')\<close> 
      \<open>typ_of (subst_bv x f) = Some \<tau>'\<close> betapply.simps(1) subst_bv_def term_ok'.simps(5)
      term_ok'_subst_bv1 wt_term_def typ_of_betaply x(1) x(2)
    by (meson "3" proved_terms_well_formed(2) term_ok_mk_eqD)

  have "typ_of (subst_bv x f) = typ_of (Abs \<tau> g $ x)"
    using \<open>typ_of (Abs \<tau> f $ x) = typ_of (Abs \<tau> g $ x)\<close>
      \<open>typ_of (Abs \<tau> f $ x) = typ_of (subst_bv x f)\<close> by auto

  have "typ_of (Abs \<tau> g $ x) = typ_of (subst_bv x g)" 
    using \<open>typ_of (Abs \<tau> f) = typ_of (Abs \<tau> g)\<close> eq(2) typ_of_betapply typ_of_def x(2) by auto

  have c1: "\<Theta>, \<Gamma> \<turnstile> mk_eq (subst_bv x f) (Abs \<tau> g $ x)"
    apply (rule proves_eq_transitive_rule[where t="Abs \<tau> f $ x"]; 
        (use assms 1 2 \<open>term_ok \<Theta> (subst_bv x f)\<close>  in \<open>solves simp\<close>)?)
    using \<open>term_ok \<Theta> (Abs \<tau> f $ x)\<close> apply blast
    using \<open>term_ok \<Theta> (Abs \<tau> g $ x)\<close> apply blast
    using \<open>typ_of (Abs \<tau> f $ x) = typ_of (subst_bv x f)\<close> apply simp
    using \<open>typ_of (Abs \<tau> f $ x) = typ_of (Abs \<tau> g $ x)\<close> apply blast
    done
  show ?thesis
    apply (rule proves_eq_transitive_rule[where t="Abs \<tau> g $ x"]; 
        (use assms 1 2 \<open>term_ok \<Theta> (subst_bv x f)\<close>  in \<open>solves simp\<close>)?)
    using  \<open>term_ok \<Theta> (Abs \<tau> g $ x)\<close>
      \<open>term_ok \<Theta> (subst_bv x g)\<close>
      \<open>typ_of (subst_bv x f) = typ_of (Abs \<tau> g $ x)\<close>
      \<open>typ_of (Abs \<tau> g $ x) = typ_of (subst_bv x g)\<close>
      \<open>\<Theta>,\<Gamma> \<turnstile> mk_eq (subst_bv x f) (Abs \<tau> g $ x)\<close>
      \<open>\<Theta>,\<Gamma> \<turnstile> mk_eq (Abs \<tau> g $ x) (subst_bv x g)\<close> by simp_all
qed

(* The is_closeds are annoying *)
lemma proves_descend_abs_rule:
  assumes thy: "wf_theory \<Theta>"
  assumes eq: "\<Theta>, \<Gamma> \<turnstile> mk_eq (Abs \<tau>' (bind_fv (x, \<tau>') s)) (Abs \<tau>' (bind_fv (x, \<tau>') t))"
    "is_closed s" "is_closed t"
  assumes x: "(x, \<tau>') \<notin> FV \<Gamma>" "typ_ok \<Theta> \<tau>'"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq s t"
proof-
  have abs_ok: "term_ok \<Theta> (Abs_fv x \<tau>' s)" "term_ok \<Theta> (Abs_fv x \<tau>' t)"
    using eq proved_terms_well_formed wt_term_def typ_of1_split_App typ_of_def
    by (meson term_ok_mk_eqD)+
  obtain \<tau> where \<tau>1: "typ_of (Abs_fv x \<tau>' s) = Some (\<tau>' \<rightarrow> \<tau>)"
    by (smt eq proved_terms_well_formed_pre typ_of1_split_App_obtains typ_of_Abs_body_typ' typ_of_def)
  hence \<tau>2: "typ_of (Abs_fv x \<tau>' t) = Some (\<tau>' \<rightarrow> \<tau>)"
    by (metis eq(1) proved_terms_well_formed(2) term_ok_mk_eq_same_typ thy)

  have add_param: "\<Theta>, \<Gamma> \<turnstile> mk_eq 
    (Abs \<tau>' (bind_fv (x, \<tau>') s) $ Fv x \<tau>')
    (Abs \<tau>' (bind_fv (x, \<tau>') t) $ Fv x \<tau>')"
    apply(rule proves_eq_combination_rule; use assms abs_ok \<tau>1 \<tau>2 in \<open>(solves simp)?\<close>)
    using proves_eq_reflexive term_ok_var thy x(2) wt_term_def ctxt by blast+

  have \<beta>s: "\<Theta>, \<Gamma> \<turnstile> mk_eq 
    (Abs \<tau>' (bind_fv (x, \<tau>') s) $ Fv x \<tau>')
    (subst_bv (Fv x \<tau>') (bind_fv (x, \<tau>') s))"
    by (rule proves.\<beta>_conversion; use assms abs_ok \<tau>1 \<tau>2 in \<open>(solves \<open>simp add: wt_term_def\<close>)?\<close>)
  moreover have simps: "subst_bv (Fv x \<tau>') (bind_fv (x, \<tau>') s) = s"
    using subst_bv_bind_fv typ_of_imp_closed eq(2) by blast
  ultimately have \<beta>s: "\<Theta>, \<Gamma> \<turnstile> mk_eq (Abs \<tau>' (bind_fv (x, \<tau>') s) $ Fv x \<tau>') s"
    by simp

  have t1: "term_ok \<Theta> s" 
    using \<beta>s proved_terms_well_formed(2) wt_term_def typ_of_def 
    using term_ok_app_eqD by blast
  have t2: "term_ok \<Theta> (Abs_fv x \<tau>' s $ term.Fv x \<tau>')"
    using \<beta>s \<open>term_ok \<Theta> s\<close> proved_terms_well_formed(2) term_ok'.simps(4) 
        wt_term_def term_ok_mk_eq_same_typ thy
    by (meson term_ok_mk_eqD)

  have \<beta>s_rev: "\<Theta>, \<Gamma> \<turnstile> mk_eq s (Abs \<tau>' (bind_fv (x, \<tau>') s) $ Fv x \<tau>')"
    apply (rule proves_eq_symmetric_rule; use assms abs_ok \<tau>1 \<tau>2 t1 t2 in \<open>(solves simp)?\<close>)
    using \<beta>s proved_terms_well_formed(2) term_ok_mk_eq_same_typ thy apply blast
    using \<beta>s by simp

  have \<beta>t: "\<Theta>, \<Gamma> \<turnstile> mk_eq 
    (Abs \<tau>' (bind_fv (x, \<tau>') t) $ Fv x \<tau>')
    (subst_bv (Fv x \<tau>') (bind_fv (x, \<tau>') t))"
    by (rule proves.\<beta>_conversion; use assms abs_ok \<tau>1 \<tau>2 t1 t2 in \<open>(solves \<open>simp add: wt_term_def\<close>)?\<close>)
  moreover have simpt: "subst_bv (Fv x \<tau>') (bind_fv (x, \<tau>') t) = t"
    using subst_bv_bind_fv typ_of_imp_closed eq(3) by blast
  ultimately have \<beta>t: "\<Theta>, \<Gamma> \<turnstile> mk_eq  (Abs \<tau>' (bind_fv (x, \<tau>') t) $ Fv x \<tau>') t"
    by simp

  have t3: "term_ok \<Theta> (Abs_fv x \<tau>' t $ term.Fv x \<tau>')"
    using \<beta>s add_param proved_terms_well_formed(2) t1 term_ok'.simps(4)
        wt_term_def term_ok_mk_eq_same_typ thy 
    by (meson term_ok_mk_eqD)
  have t4: "typ_of s = typ_of (Abs_fv x \<tau>' t $ term.Fv x \<tau>')" 
    by (metis \<beta>s add_param proved_terms_well_formed(2) term_ok_mk_eq_same_typ thy)
  have t5: "typ_of s = typ_of (Abs_fv x \<tau>' s $ Fv x \<tau>')"
    using \<beta>s_rev proved_terms_well_formed(2) term_ok_mk_eq_same_typ thy by blast
  have t6: "typ_of (Abs_fv x \<tau>' s $ Fv x \<tau>') = typ_of (Abs_fv x \<tau>' t $ term.Fv x \<tau>')"
    using t4 t5 by auto
  have half: "\<Theta>, \<Gamma> \<turnstile> mk_eq s (Abs \<tau>' (bind_fv (x, \<tau>') t) $ Fv x \<tau>')"
    apply (rule proves_eq_transitive_rule[where t="Abs \<tau>' (bind_fv (x, \<tau>') s) $ Fv x \<tau>'"]
        ; use assms abs_ok \<tau>1 \<tau>2 t1 t2 t3 t4 t5 t6 in \<open>(solves simp)?\<close>)
    using \<beta>s_rev apply blast
    using add_param by blast

  have t7: "term_ok \<Theta> t"
    using \<beta>t proved_terms_well_formed(2) t1 t4 term_ok'.simps(4) wt_term_def term_ok_mk_eq_same_typ thy
    by (meson term_ok_app_eqD)
  have t8: "typ_of (Abs_fv x \<tau>' t $ term.Fv x \<tau>') = typ_of t"
      using \<beta>t proved_terms_well_formed(2) term_ok_mk_eq_same_typ thy by blast

  show ?thesis
    apply (rule proves_eq_transitive_rule[where t="Abs \<tau>' (bind_fv (x, \<tau>') t) $ Fv x \<tau>'"]
        ; use assms abs_ok \<tau>1 \<tau>2 t1 t2 t3 t4 t5 t6 t7 t8 in \<open>(solves simp)?\<close>)
    using half apply blast
    using \<beta>t by blast
qed

(* MOVE? Not general enough for other place, seems like an adhoc solution*)
lemma obtain_fresh_variable:
  assumes "finite \<Gamma>"
  obtains x where "(x,\<tau>) \<notin> fv t \<union> FV \<Gamma>"
  using assms finite_fv finite_FV
  by (metis finite_Un finite_imageI fst_conv image_eqI variant_variable_fresh)
lemma obtain_fresh_variable':
  assumes "finite \<Gamma>"
  obtains x where "(x,\<tau>) \<notin> fv t \<union> fv u \<union> FV \<Gamma>"
  using assms finite_fv finite_FV
  by (metis finite_Un finite_imageI fst_conv image_eqI variant_variable_fresh)

lemma proves_eq_abstract_rule_pre:
  assumes thy: "wf_theory \<Theta>"
  assumes A: "term_ok \<Theta> f" "typ_of f = Some (\<tau> \<rightarrow> \<tau>')"
  assumes B: "term_ok \<Theta> g" "typ_of g = Some (\<tau> \<rightarrow> \<tau>')"
  shows "\<Theta>, {} \<turnstile> (Ct STR ''Pure.all'' ((\<tau> \<rightarrow> propT) \<rightarrow> propT) $ Abs \<tau> (mk_eq' \<tau>' (f $ Bv 0) (g $ Bv 0)))
    \<longmapsto> mk_eq (Abs \<tau> (f $ Bv 0)) (Abs \<tau> (g $ Bv 0))"
proof-
  have "eq_abstract_rule_ax \<in> axioms \<Theta>" 
    using thy by (cases \<Theta> rule: theory_full_exhaust) auto
  moreover have ok2: "typ_ok \<Theta> (\<tau> \<rightarrow> \<tau>')"
      using assms(2) assms(3) term_ok_imp_typ_ok thy by blast
  moreover hence ok3: "typ_ok \<Theta> \<tau>'" 
    using thy A(2) by (cases \<Theta> rule: theory_full_exhaust) auto
  moreover have ok1: "typ_ok \<Theta> \<tau>" 
    using thy A(2) ok2 by (cases \<Theta> rule: theory_full_exhaust) auto
  ultimately have 1: "\<Theta>, {} \<turnstile> subst_typ' 
    [((Var (STR '''a'', 0), full_sort), \<tau>), ((Var (STR '''b'', 0), full_sort), \<tau>')] eq_abstract_rule_ax"
    using assms axiom_subst_typ' by (simp del: term_ok_def)
  hence "\<Theta>, {} \<turnstile> subst_term [((Var (STR ''g'', 0), \<tau> \<rightarrow> \<tau>'), g),
      ((Var (STR ''f'', 0), \<tau> \<rightarrow> \<tau>'), f)] (subst_typ'
    [((Var (STR '''a'', 0), full_sort), \<tau>), ((Var (STR '''b'', 0), full_sort), \<tau>')] eq_abstract_rule_ax)"
    using ok1 ok2 ok3 assms term_ok_var by (fastforce intro!: inst_var_multiple simp add: eq_abstract_rule_ax_def)
  moreover have "subst_term [((Var (STR ''g'', 0), \<tau> \<rightarrow> \<tau>'), g),
      ((Var (STR ''f'', 0), \<tau> \<rightarrow> \<tau>'), f)] (subst_typ'
    [((Var (STR '''a'', 0), full_sort), \<tau>), ((Var (STR '''b'', 0), full_sort), \<tau>')] eq_abstract_rule_ax)
    = (Ct STR ''Pure.all'' ((\<tau> \<rightarrow> propT) \<rightarrow> propT) $ Abs \<tau> (mk_eq' \<tau>' (f $ Bv 0) (g $ Bv 0)))
    \<longmapsto> mk_eq (Abs \<tau> (f $ Bv 0)) (Abs \<tau> (g $ Bv 0))"
    using assms typ_of1_weaken_Ts by (fastforce simp add: eq_axs_def typ_of_def)
  ultimately show ?thesis
    using assms by simp
qed

lemma proves_eq_abstract_rule:
  assumes thy: "wf_theory \<Theta>"
  assumes A: "term_ok \<Theta> f" "typ_of f = Some (\<tau> \<rightarrow> \<tau>')"
  assumes B: "term_ok \<Theta> g" "typ_of g = Some (\<tau> \<rightarrow> \<tau>')"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> (Ct STR ''Pure.all'' ((\<tau> \<rightarrow> propT) \<rightarrow> propT) $ Abs \<tau> (mk_eq' \<tau>' (f $ Bv 0) (g $ Bv 0)))
    \<longmapsto> mk_eq (Abs \<tau> (f $ Bv 0)) (Abs \<tau> (g $ Bv 0))"
  by (subst unsimp_context) (use assms proves_eq_abstract_rule_pre weaken_proves_set in blast)

lemma proves_eq_abstract_rule_rule:
  assumes thy: "wf_theory \<Theta>"
  assumes A: "term_ok \<Theta> f" "typ_of f = Some (\<tau> \<rightarrow> \<tau>')"
  assumes B: "term_ok \<Theta> g" "typ_of g = Some (\<tau> \<rightarrow> \<tau>')"
  assumes "\<Theta>, \<Gamma> \<turnstile> (Ct STR ''Pure.all'' ((\<tau> \<rightarrow> propT) \<rightarrow> propT) $ Abs \<tau> (mk_eq' \<tau>' (f $ Bv 0) (g $ Bv 0)))"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq (Abs \<tau> (f $ Bv 0)) (Abs \<tau> (g $ Bv 0))"
proof-
  note 1 = proves_eq_abstract_rule[where \<Gamma>=\<Gamma>, OF assms(1-5) ctxt]
  note 2 = proves.implies_elim[OF 1 assms(6)]
  thus ?thesis using ctxt by simp
qed

lemma proves_eq_ext_rule:
  assumes thy: "wf_theory \<Theta>"
  assumes f: "term_ok \<Theta> f" "typ_of f = Some (\<tau> \<rightarrow> \<tau>')"
  assumes g: "term_ok \<Theta> g" "typ_of g = Some (\<tau> \<rightarrow> \<tau>')"
  assumes prem: "\<Theta>, \<Gamma> \<turnstile> Ct STR ''Pure.all'' ((\<tau> \<rightarrow> propT) \<rightarrow> propT) $ Abs \<tau> (mk_eq' \<tau>' (f $ Bv 0) (g $ Bv 0))"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq f g"
proof-
  obtain x where x: "(x,\<tau>) \<notin> FV \<Gamma>" "(x,\<tau>) \<notin> fv f" "(x,\<tau>) \<notin> fv g"
    by (meson Un_iff ctxt(1) obtain_fresh_variable')
  have closed: "is_closed f" "is_closed g" 
    using f g has_typ_imp_closed term_ok_def wt_term_def by blast+

  have "term_ok \<Theta> (Abs \<tau> (mk_eq' \<tau>' (f $ Bv 0) (g $ Bv 0)))"
    using prem proved_terms_well_formed(2) term_ok_app_eqD by blast

  have "subst_bv (Fv x \<tau>) (f $ Bv 0) = f $ Fv x \<tau>"
    using Core.subst_bv_def f(1) term_ok_subst_bv_no_change by auto
  moreover have "subst_bv (Fv x \<tau>) (g $ Bv 0) = g $ Fv x \<tau>"
    using Core.subst_bv_def g(1) term_ok_subst_bv_no_change by auto
  ultimately have "subst_bv (Fv x \<tau>) (mk_eq' \<tau>' (f $ Bv 0) (g $ Bv 0))
    = mk_eq' \<tau>' (f $ Fv x \<tau>) (g $ Fv x \<tau>)"
    by (simp add: Core.subst_bv_def)  
  hence simp: "Abs \<tau> (mk_eq' \<tau>' (f $ Bv 0) (g $ Bv 0)) \<bullet> Fv x \<tau> = mk_eq (f $ Fv x \<tau>) (g $ Fv x \<tau>)"
    using f g by (auto simp add: typ_of_def)
  hence simp': "subst_bv (Fv x \<tau>) (mk_eq' \<tau>' (f $ Bv 0) (g $ Bv 0)) = mk_eq' \<tau>' (f $ Fv x \<tau>) (g $ Fv x \<tau>)"
    using f g by (auto simp add: typ_of_def)

  have "\<Theta>, \<Gamma> \<turnstile> mk_eq' \<tau>' (f $ Fv x \<tau>) (g $ Fv x \<tau>)"
    apply (subst simp'[symmetric])
    apply (rule forall_elim[where \<tau>=\<tau>])
    using prem apply blast
     apply simp
    using \<open>term_ok \<Theta> (Abs \<tau> (mk_eq' \<tau>' (f $ Bv 0) (g $ Bv 0)))\<close> term_ok'.simps(1) term_ok'.simps(5) term_okD1 by blast
  moreover have "typ_of (f $ Fv x \<tau>) = Some \<tau>'" "typ_of (g $ Fv x \<tau>) = Some \<tau>'"
    using f(2) g(2) by (simp_all add: typ_of_def)
  ultimately have 1: "\<Theta>, \<Gamma> \<turnstile> mk_eq (f $ Fv x \<tau>) (g $ Fv x \<tau>)"
    by simp
  have core: "\<Theta>, \<Gamma> \<turnstile> mk_eq (Abs \<tau> (f $ Bv 0)) (Abs \<tau> (g $ Bv 0))"
    apply (rule proves_eq_abstract_rule_rule[OF thy f g _ ctxt])
    using prem by blast
  have "\<Theta>, \<Gamma> \<turnstile> mk_eq (Abs \<tau> (f $ Bv 0)) f"
    using f proves.eta term_okD1 thy by blast
  have left: "\<Theta>, \<Gamma> \<turnstile> mk_eq f (Abs \<tau> (f $ Bv 0))" (* Should be: auto ... *)
    apply (rule proves_eq_symmetric_rule[OF thy f(1) _ _ _ ctxt])
    using \<open>\<Theta>,\<Gamma> \<turnstile> mk_eq (Abs \<tau> (f $ Bv 0)) (Abs \<tau> (g $ Bv 0))\<close> proved_terms_well_formed(2) term_ok_mk_eqD apply blast
     apply (simp add: Logic.typ_of_eta_expand f(2))
    using \<open>\<Theta>,\<Gamma> \<turnstile> mk_eq (Abs \<tau> (f $ Bv 0)) f\<close> by blast

  have right: "\<Theta>, \<Gamma> \<turnstile> mk_eq (Abs \<tau> (g $ Bv 0)) g"
    using g proves.eta term_okD1 thy by blast

  show ?thesis
    apply (rule proves_eq_transitive_rule[where t="Abs \<tau> (f $ Bv 0)", OF thy f(1) _ g(1) _ _ left _ ctxt])
    using \<open>\<Theta>,\<Gamma> \<turnstile> mk_eq (Abs \<tau> (f $ Bv 0)) f\<close> proved_terms_well_formed(2) term_ok_mk_eqD apply blast
      apply (simp add: Logic.typ_of_eta_expand f(2))
      apply (simp add: Logic.typ_of_eta_expand f(2) g(2))
    apply (rule proves_eq_transitive_rule[where t="Abs \<tau> (g $ Bv 0)", OF thy _ _ g(1)  _ _ core right ctxt])
    using \<open>\<Theta>,\<Gamma> \<turnstile> mk_eq (Abs \<tau> (f $ Bv 0)) f\<close> proved_terms_well_formed(2) term_ok_mk_eqD apply blast
    using \<open>\<Theta>,\<Gamma> \<turnstile> mk_eq (Abs \<tau> (g $ Bv 0)) g\<close> proved_terms_well_formed(2) term_ok_mk_eqD apply blast
    by (simp add: Logic.typ_of_eta_expand f(2) g(2))+
qed

lemma bind_fv2_idem[simp]: 
  "bind_fv2 (x, \<tau>) lev1 (bind_fv2 (x, \<tau>) lev2 t) = bind_fv2 (x, \<tau>) lev2 t "
  by (induction "(x,\<tau>)" lev2 t arbitrary: lev1 rule: bind_fv2.induct) auto
corollary bind_fv_idem[simp]: 
  "bind_fv (x, \<tau>) (bind_fv (x, \<tau>) t) = bind_fv (x, \<tau>) t "
  using bind_fv_def bind_fv2_idem by simp
corollary bind_fv_Abs_fv[simp]: "bind_fv (x, \<tau>) (Abs_fv x \<tau> t) = Abs_fv x \<tau> t"
  by (simp add: bind_fv_def)

lemma "bind_fv2 (x,\<tau>) lev (mk_eq' \<tau>' s t) = mk_eq' \<tau>' (bind_fv2 (x,\<tau>) lev s) (bind_fv2 (x,\<tau>) lev t)"
  by simp
lemma "bind_fv (x,\<tau>) (mk_eq' \<tau>' s t) = mk_eq' \<tau>' (bind_fv (x,\<tau>) s) (bind_fv (x,\<tau>) t)"
  by (simp add: bind_fv_def)

lemma term_ok_Abs_fvI: "term_ok \<Theta> s \<Longrightarrow> typ_ok \<Theta> \<tau> \<Longrightarrow> term_ok \<Theta> (Abs_fv x \<tau> s)"
  by (auto simp add: wt_term_def term_ok'_bind_fv typ_of_Abs_bind_fv)
  
lemma proves_eq_abstract_rule_derived_rule:
  assumes thy: "wf_theory \<Theta>"
  assumes x: "(x, \<tau>) \<notin> FV \<Gamma>" "typ_ok \<Theta> \<tau>"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  assumes eq: "\<Theta>, \<Gamma> \<turnstile> mk_eq s t" 
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq (Abs \<tau> (bind_fv (x, \<tau>) s)) (Abs \<tau> (bind_fv (x, \<tau>) t))"
proof-
  obtain \<tau>' where s: "typ_of s = Some \<tau>'"
    by (meson eq option.exhaust_sel proved_terms_well_formed(2) term_okD2 term_ok_app_eqD)
  have t: "typ_of t = Some \<tau>'"
    by (metis eq proved_terms_well_formed(2) s term_ok_mk_eq_same_typ thy)

  have ok: "term_ok \<Theta> s" "term_ok \<Theta> t"
    using eq proved_terms_well_formed(2) term_ok_mk_eqD by blast+

  have closed: "is_closed s" "is_closed t"
    using eq has_typ_imp_closed proved_terms_well_formed(2) term_ok_def term_ok_mk_eqD wt_term_def by blast+

  have "is_closed (mk_eq s t)"
    using eq proved_terms_closed by blast
  hence "Abs \<tau> (bind_fv (x, \<tau>) (mk_eq s t)) \<bullet> Fv x \<tau> = mk_eq s t"
     using betapply_Abs_fv by auto
  have "\<Theta>, \<Gamma> \<turnstile> mk_all x \<tau> (mk_eq s t)"
    using eq forall_intro thy typ_ok_def x(1) x(2) by blast

  have "\<Theta>, \<Gamma> \<turnstile> mk_eq (Abs \<tau> (bind_fv (x, \<tau>) s) $ Fv x \<tau>) (subst_bv (Fv x \<tau>) (bind_fv (x, \<tau>) s))"
    using term_ok_Abs_fvI[OF ok(1) x(2)] wf_term.intros(1) typ_ok_def x(2) 
    by (auto intro!: \<beta>_conversion[OF thy])
  moreover have "subst_bv (Fv x \<tau>) (bind_fv (x, \<tau>) s) = s"
    by (simp add: closed(1) subst_bv_bind_fv)
  ultimately have unfs: "\<Theta>, \<Gamma> \<turnstile> mk_eq (Abs \<tau> (bind_fv (x, \<tau>) s) $ Fv x \<tau>) s"
    by simp
  have "\<Theta>, \<Gamma> \<turnstile> mk_eq (Abs \<tau> (bind_fv (x, \<tau>) t) $ Fv x \<tau>) (subst_bv (Fv x \<tau>) (bind_fv (x, \<tau>) t))"
    using term_ok_Abs_fvI[OF ok(2) x(2)] wf_term.intros(1) typ_ok_def x(2) 
    by (auto intro!: \<beta>_conversion[OF thy])

  moreover have "subst_bv (Fv x \<tau>) (bind_fv (x, \<tau>) t) = t"
    by (simp add: closed(2) subst_bv_bind_fv)
  ultimately have unft: "\<Theta>, \<Gamma> \<turnstile> mk_eq (Abs \<tau> (bind_fv (x, \<tau>) t) $ Fv x \<tau>) t"
    by simp
  
  have prem:
    "\<Theta>, \<Gamma> \<turnstile> mk_eq (Abs \<tau> (bind_fv (x, \<tau>) s) $ Fv x \<tau>) (Abs \<tau> (bind_fv (x, \<tau>) t) $ Fv x \<tau>)"
    apply (rule proves_eq_transitive_rule[where t=s, OF thy _ _ _ _ _ _ _ ctxt])
    using ok(1) term_ok_mk_eqD unfs unft proved_terms_well_formed(2) term_ok_mk_eq_same_typ thy 
         apply (all blast)[4]
    apply (metis proved_terms_well_formed(2) s t term_ok_mk_eq_same_typ thy unft)
    using unfs apply blast
    subgoal
      apply (rule proves_eq_transitive_rule[where t=t, OF thy ok _ _ _ _ _ ctxt])
      using proved_terms_well_formed(2) term_ok_mk_eqD unft apply blast
      apply (simp add: s t)
        apply (metis proved_terms_well_formed(2) term_ok_mk_eq_same_typ thy unft)
      using eq apply simp
      subgoal apply (rule proves_eq_symmetric_rule[OF thy ok(2) _ _ _ ctxt])
        using proved_terms_well_formed(2) term_ok_mk_eqD unft apply blast
        using proved_terms_well_formed(2) term_ok_mk_eq_same_typ thy unft apply blast
        using unft apply blast
        done
      done
    done
  hence "\<Theta>, \<Gamma> \<turnstile> mk_all x \<tau>
    (mk_eq (Abs \<tau> (bind_fv (x, \<tau>) s) $ Fv x \<tau>) (Abs \<tau> (bind_fv (x, \<tau>) t) $ Fv x \<tau>))"
    using forall_intro thy typ_ok_def x(1) x(2) by blast
  moreover have "mk_all x \<tau> 
      (mk_eq (Abs \<tau> (bind_fv (x, \<tau>) s) $ Fv x \<tau>) (Abs \<tau> (bind_fv (x, \<tau>) t) $ Fv x \<tau>))
    = mk_all x \<tau> 
      (mk_eq' \<tau>' (Abs \<tau> (bind_fv (x, \<tau>) s) $ Fv x \<tau>) (Abs \<tau> (bind_fv (x, \<tau>) t) $ Fv x \<tau>))"
    using bind_fv2_preserves_type s t typ_of_def by (fastforce simp add: bind_fv_def typ_of_def)+
  moreover have "mk_all x \<tau> 
      (mk_eq' \<tau>' (Abs \<tau> (bind_fv (x, \<tau>) s) $ Fv x \<tau>) (Abs \<tau> (bind_fv (x, \<tau>) t) $ Fv x \<tau>)) =
    Ct STR ''Pure.all'' ((\<tau> \<rightarrow> propT) \<rightarrow> propT) $ Abs \<tau> 
      (mk_eq' \<tau>' (Abs \<tau> (bind_fv (x, \<tau>) s) $ Bv 0) (Abs \<tau> (bind_fv (x, \<tau>) t) $ Bv 0))"
    by (simp add: bind_fv_def)
  ultimately have pre_ext: "\<Theta>, \<Gamma> \<turnstile> Ct STR ''Pure.all'' ((\<tau> \<rightarrow> propT) \<rightarrow> propT) $ Abs \<tau> 
      (mk_eq' \<tau>' (Abs \<tau> (bind_fv (x, \<tau>) s) $ Bv 0) (Abs \<tau> (bind_fv (x, \<tau>) t) $ Bv 0))"
    by simp
  show ?thesis
    apply (rule proves_eq_ext_rule[where \<tau>=\<tau> and \<tau>'=\<tau>', OF thy _ _ _ _ _ ctxt])
    using proved_terms_well_formed(2) term_ok_app_eqD unfs apply blast
    apply (simp add: s typ_of_Abs_bind_fv)
    using proved_terms_well_formed(2) term_ok_app_eqD unft apply blast
     apply (simp add: t typ_of_Abs_bind_fv)
    using pre_ext by blast
qed

(* This should allow descending under abstractions for rewriting *)
lemma proves_descend_abs_rule_iff:
  assumes thy: "wf_theory \<Theta>"
  assumes ok: "is_closed s" "is_closed t"
  assumes x: "(x, \<tau>') \<notin> FV \<Gamma>" "typ_ok \<Theta> \<tau>'"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq s t 
    \<longleftrightarrow> \<Theta>, \<Gamma> \<turnstile> mk_eq (Abs \<tau>' (bind_fv (x, \<tau>') s)) (Abs \<tau>' (bind_fv (x, \<tau>') t))"
proof (rule iffI)
  assume asm: "\<Theta>,\<Gamma> \<turnstile> mk_eq s t"
  hence "term_ok \<Theta> s" "term_ok \<Theta> t"
    using proved_terms_well_formed(2) term_ok_mk_eqD by blast+
  show "\<Theta>,\<Gamma> \<turnstile> mk_eq (Abs_fv x \<tau>' s) (Abs_fv x \<tau>' t)"
    by (rule proves_eq_abstract_rule_derived_rule[OF thy x ctxt asm])
next
  assume asm: "\<Theta>,\<Gamma> \<turnstile> mk_eq (Abs_fv x \<tau>' s) (Abs_fv x \<tau>' t)"
  show "\<Theta>,\<Gamma> \<turnstile> mk_eq s t"
    using assms asm proves_descend_abs_rule by blast
qed

(* This seems better *)
lemma proves_descend_abs_rule':
  assumes thy: "wf_theory \<Theta>"
  assumes eq: "\<Theta>, \<Gamma> \<turnstile> mk_eq (Abs \<tau>' s) (Abs \<tau>' t)"
  assumes x: "(x, \<tau>') \<notin> FV \<Gamma>" "typ_ok \<Theta> \<tau>'"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq (subst_bv (Fv x \<tau>') s) (subst_bv (Fv x \<tau>') t)"
proof-
  have abs_ok: "term_ok \<Theta> (Abs \<tau>' s)" "term_ok \<Theta> (Abs \<tau>' t)"
    using eq(1) option.distinct(1) proved_terms_well_formed term_ok'.simps(4)
        wt_term_def typ_of1_split_App typ_of_def 
    by (smt term_ok_mk_eqD)+

  obtain \<tau> where \<tau>1: "typ_of (Abs \<tau>' s) = Some (\<tau>' \<rightarrow> \<tau>)"
    by (smt eq proved_terms_well_formed_pre typ_of1_split_App_obtains typ_of_Abs_body_typ' typ_of_def)
  hence \<tau>2: "typ_of (Abs \<tau>' t)= Some (\<tau>' \<rightarrow> \<tau>)"
    by (metis eq(1) proved_terms_well_formed(2) term_ok_mk_eq_same_typ thy)

  have add_param: "\<Theta>, \<Gamma> \<turnstile> mk_eq 
    (Abs \<tau>' s $ Fv x \<tau>')
    (Abs \<tau>' t $ Fv x \<tau>')"
    apply (rule proves_eq_combination_rule; use assms abs_ok \<tau>1 \<tau>2 in \<open>(solves \<open>simp del: term_ok_def\<close>)?\<close>)
    using proves_eq_reflexive term_ok_var thy x(2) ctxt by blast

  have \<beta>s: "\<Theta>, \<Gamma> \<turnstile> mk_eq 
    (Abs \<tau>' s $ Fv x \<tau>')
    (subst_bv (Fv x \<tau>') s)"
    by (rule proves.\<beta>_conversion; use assms abs_ok \<tau>1 \<tau>2 in \<open>(solves \<open>simp add: wt_term_def\<close>)?\<close>)

  have t1: "term_ok \<Theta> (subst_bv (Fv x \<tau>') s)" 
    using \<beta>s proved_terms_well_formed(2) wt_term_def typ_of_def 
    using term_ok_mk_eqD by blast
  have t2: "term_ok \<Theta> (Abs \<tau>' s $ term.Fv x \<tau>')"
    using \<beta>s proved_terms_well_formed(2) t1 term_ok'.simps(4) wt_term_def term_ok_mk_eq_same_typ thy
      term_ok_mk_eqD by blast
  have \<beta>s_rev: "\<Theta>, \<Gamma> \<turnstile> mk_eq (subst_bv (Fv x \<tau>') s) (Abs \<tau>' s $ Fv x \<tau>')"
    apply (rule proves_eq_symmetric_rule; use assms abs_ok \<tau>1 \<tau>2 t1 t2 in \<open>(solves simp)?\<close>)
    using \<beta>s proved_terms_well_formed(2) term_ok_mk_eq_same_typ thy apply blast
    using \<beta>s by simp

  have \<beta>t: "\<Theta>, \<Gamma> \<turnstile> mk_eq 
    (Abs \<tau>' t $ Fv x \<tau>')
    (subst_bv (Fv x \<tau>') t)"
    by (rule proves.\<beta>_conversion; use assms abs_ok \<tau>1 \<tau>2 t1 in \<open>(solves \<open>simp add: wt_term_def\<close>)?\<close>)
  
  have t3: "term_ok \<Theta> (Abs \<tau>' t $ term.Fv x \<tau>')"
    using \<beta>s add_param proved_terms_well_formed(2) t1 term_ok'.simps(4)
        wt_term_def term_ok_mk_eq_same_typ thy term_ok_mk_eqD 
    by meson
  have t4: "typ_of (subst_bv (Fv x \<tau>') s) = typ_of (Abs \<tau>' t $ term.Fv x \<tau>')" 
    by (metis \<beta>s add_param proved_terms_well_formed(2) term_ok_mk_eq_same_typ thy)
  have t5: "typ_of (subst_bv (Fv x \<tau>') s) = typ_of (Abs \<tau>' s $ Fv x \<tau>')"
    using \<beta>s_rev proved_terms_well_formed(2) term_ok_mk_eq_same_typ thy by blast
  have t6: "typ_of (Abs \<tau>' s $ Fv x \<tau>') = typ_of (Abs \<tau>' t $ term.Fv x \<tau>')"
    using t4 t5 by auto

  have half: "\<Theta>, \<Gamma> \<turnstile> mk_eq (subst_bv (Fv x \<tau>') s) (Abs \<tau>' t $ Fv x \<tau>')"
    apply (rule proves_eq_transitive_rule[where t="Abs \<tau>' s $ Fv x \<tau>'"]
        ; use assms abs_ok \<tau>1 \<tau>2 t1 t2 t3 t4 t5 t6 in \<open>(solves simp)?\<close>)
    using \<beta>s_rev apply blast
    using add_param by blast

  have t7: "term_ok \<Theta> (subst_bv (Fv x \<tau>') t)"
    using \<beta>t proved_terms_well_formed(2) t1 t4 term_ok'.simps(4) wt_term_def term_ok_mk_eq_same_typ thy
    by (meson term_ok_app_eqD)
  have t8: "typ_of (Abs \<tau>' t $ term.Fv x \<tau>') = typ_of (subst_bv (Fv x \<tau>') t)"
      using \<beta>t proved_terms_well_formed(2) term_ok_mk_eq_same_typ thy by blast

  show ?thesis
    apply (rule proves_eq_transitive_rule[where t="Abs \<tau>' t $ Fv x \<tau>'"]
        ; use assms abs_ok \<tau>1 \<tau>2 t1 t2 t3 t4 t5 t6 t7 t8 in \<open>(solves simp)?\<close>)
    using half apply blast
    using \<beta>t by blast
qed

lemma proves_ascend_abs_rule':
  assumes thy: "wf_theory \<Theta>"
  assumes x: "(x, \<tau>') \<notin> FV \<Gamma>" "(x,\<tau>') \<notin> fv (mk_eq (Abs \<tau>' s) (Abs \<tau>' t))" "typ_ok \<Theta> \<tau>'"
  assumes eq: "\<Theta>, \<Gamma> \<turnstile> mk_eq (subst_bv (Fv x \<tau>') s) (subst_bv (Fv x \<tau>') t)"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq (Abs \<tau>' s) (Abs \<tau>' t)"
proof-
  have ok_ind: "wf_type (sig \<Theta>) \<tau>'"
    using x(3) by simp


  note 1 = proves_eq_abstract_rule_derived_rule[OF thy]
  have "term_ok \<Theta> (subst_bv (Fv x \<tau>') s)"
    using eq proved_terms_well_formed(2) wt_term_def typ_of_def 
    by (meson term_ok_app_eqD)
  hence "is_closed (subst_bv (Fv x \<tau>') s)"
    using wt_term_def typ_of_imp_closed by auto
  hence loose_s: "\<not> loose_bvar s 1"
    using is_closed_subst_bv by simp
  hence loose_s': "(\<And>x. 1 < x \<Longrightarrow> \<not> loose_bvar1 s x) " 
    by (simp add: not_loose_bvar_imp_not_loose_bvar1_all_greater)
  moreover have " \<not> occs (case_prod Fv (x,\<tau>')) s"
  proof-
    have "(x,\<tau>') \<notin> fv s"
      using x(2) by auto 
    thus ?thesis
      by (simp add: fv_iff_occs)
  qed 
  ultimately have s: "Abs_fv x \<tau>' (subst_bv (term.Fv x \<tau>') s) = Abs \<tau>' s"
    unfolding subst_bv_def bind_fv_def 
      using bind_fv2_subst_bv1_cancel
      by (metis (full_types) case_prod_conv less_one linorder_neqE_nat
          loose_bvar1_imp_loose_bvar loose_s not_less_zero)

  have "term_ok \<Theta> (subst_bv (Fv x \<tau>') t)"
    using eq proved_terms_well_formed(2) wt_term_def typ_of_def 
    by (meson term_ok_app_eqD)
  hence "is_closed (subst_bv (Fv x \<tau>') t)"
    using wt_term_def typ_of_imp_closed by auto
  hence loose_s: "\<not> loose_bvar t 1"
    using is_closed_subst_bv by simp
  hence loose_s': "(\<And>x. 1 < x \<Longrightarrow> \<not> loose_bvar1 t x) " 
    by (simp add: not_loose_bvar_imp_not_loose_bvar1_all_greater)
  moreover have " \<not> occs (case_prod Fv (x,\<tau>')) t"
  proof-
    have "(x,\<tau>') \<notin> fv t"
      using x(2) by auto 
    thus ?thesis
      by (simp add: fv_iff_occs)
  qed 
  ultimately have t: "Abs_fv x \<tau>' (subst_bv (term.Fv x \<tau>') t) = Abs \<tau>' t"
    unfolding subst_bv_def bind_fv_def 
      using bind_fv2_subst_bv1_cancel
      by (metis (full_types) case_prod_conv less_one linorder_neqE_nat loose_bvar1_imp_loose_bvar 
        loose_s not_less_zero)

  from 1 s t show ?thesis
    using ctxt  eq x(1) x(3) by fastforce
qed

lemma proves_descend_abs_rule_iff':
  assumes thy: "wf_theory \<Theta>"
  assumes x: "(x, \<tau>') \<notin> FV \<Gamma>" "(x, \<tau>') \<notin> fv (mk_eq (Abs \<tau>' s) (Abs \<tau>' t))" "typ_ok \<Theta> \<tau>'"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq (subst_bv (Fv x \<tau>') s) (subst_bv (Fv x \<tau>') t)
    \<longleftrightarrow> \<Theta>, \<Gamma> \<turnstile> mk_eq (Abs \<tau>' s) (Abs \<tau>' t)"
  apply (rule iffI)
  using assms proves_ascend_abs_rule' apply simp
  using assms proves_descend_abs_rule' by simp

lemma proves_beta_step_pre:
  assumes thy: "wf_theory \<Theta>"
  assumes finite: "finite \<Gamma>"
  assumes free: "\<forall>(x,\<tau>) \<in> set vs . (x,\<tau>) \<notin> fv t \<union> FV \<Gamma>"
  assumes term_ok': "term_ok \<Theta> (subst_bvs (map (case_prod Fv) vs) t)"
  assumes beta: "t \<rightarrow>\<^sub>\<beta> u"
  assumes ctxt: "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq
    (subst_bvs (map (case_prod Fv) vs) t)
    (subst_bvs (map (case_prod Fv) vs) u)"
using beta term_ok' free proof(induction t u arbitrary: vs rule: beta.induct)
  case (beta T s t)
  have ok: "term_ok \<Theta> (subst_bvs (map (case_prod Fv) vs) (Abs T s))"
    "term_ok \<Theta> (subst_bvs (map (case_prod Fv) vs) t)"
    using beta.prems(1) apply simp_all
    using term_ok_app_eqD term_ok_def by blast+

  have "\<forall>x \<in> set (map (case_prod Fv) vs) . is_closed x"
    using beta.prems(2) by auto
  hence simp: "subst_bvs (map (case_prod Fv) vs) (Abs T s)
    = Abs T (subst_bvs1' s 1 (map (case_prod Fv) vs))"
    by auto
  hence ok': "term_ok \<Theta> (Abs T (subst_bvs1' s 1 (map (case_prod Fv) vs)))"
    using ok by simp
  have T: "typ_of (subst_bvs (map (case_prod Fv) vs) t) = Some T"
    using ok(2) wt_term_def typ_of_beta_redex_arg simp
    using beta.prems(1) subst_bvs_App
    by (metis term_okD2)

  have ok_unf: "wt_term (sig \<Theta>) (Abs T (subst_bvs1' s 1 (map (case_prod Fv) vs)))"
    "wf_term (sig \<Theta>) (subst_bvs (map (case_prod Fv) vs) t)"
    using ok(2) ok' wt_term_def by simp_all

  have "subst_bvs (map (\<lambda>a. case a of (a, b) \<Rightarrow> term.Fv a b) vs)
              (Abs T s $ t) = 
  Abs T (subst_bvs1' s 1 (map (case_prod Fv) vs)) $ subst_bvs (map (case_prod Fv) vs) t"
    by (simp add: simp) 
  moreover have "subst_bvs (map (case_prod Fv) vs) (subst_bv2 s 0 t)
    = (subst_bv (subst_bvs (map (case_prod Fv) vs) t)
              (subst_bvs1' s 1 (map (case_prod Fv) vs)))"
    using subst_bvs1'_subst_bv2[symmetric] subst_bvs_subst_bvs1'
    by simp (metis One_nat_def Suc_eq_plus1 map_map simp subst_bvs1.simps(2) subst_bvs1_subst_bvs1' 
        subst_bvs_def substn_subst_0' term.inject(4))
  ultimately show ?case
    using \<beta>_conversion[OF thy ok_unf, of \<Gamma>] T by simp
next
  case (appL s t u)
  hence ok: "term_ok \<Theta> (subst_bvs (map (case_prod Fv) vs) s)"
            "term_ok \<Theta> (subst_bvs (map (case_prod Fv) vs) u)"
    by (metis subst_bvs_App term_ok_app_eqD)+
  moreover have "\<forall>a \<in> set vs. case a of (x, \<tau>) \<Rightarrow> (x, \<tau>) \<notin> fv s \<union> FV \<Gamma>"
    using appL by simp
  ultimately have "\<Theta>,\<Gamma> \<turnstile> mk_eq (subst_bvs (map (case_prod Fv) vs) s)
            (subst_bvs (map (case_prod Fv) vs) t)"
    using appL.IH by blast
  moreover have "\<Theta>,\<Gamma> \<turnstile> mk_eq (subst_bvs (map (case_prod Fv) vs) u)
      (subst_bvs (map (case_prod Fv) vs) u)"
    using proves_eq_reflexive[OF thy ok(2), of \<Gamma>, OF finite ctxt] by blast
  moreover obtain \<tau> where \<tau>: "typ_of 
    (subst_bvs (map (case_prod Fv) vs) u) = Some \<tau>"
    using ok wt_term_def by auto
  moreover obtain \<tau>' where "typ_of 
    (subst_bvs (map (case_prod Fv) vs) s) = Some (\<tau> \<rightarrow> \<tau>')"
    using \<tau> appL.prems(1) not_None_eq subst_bvs_App wt_term_def typ_of1_arg_typ typ_of_def 
    by (metis term_okD2)
  ultimately show ?case 
    using proves_eq_combination_rule_better thy finite ctxt by simp
next
  case (appR s t u)
  hence ok: "term_ok \<Theta> (subst_bvs (map (case_prod Fv) vs) s)"
            "term_ok \<Theta> (subst_bvs (map (case_prod Fv) vs) u)"
    by (metis subst_bvs_App term_ok_app_eqD)+
  moreover have "\<forall>a \<in> set vs. case a of (x, \<tau>) \<Rightarrow> (x, \<tau>) \<notin> fv s \<union> FV \<Gamma>"
    using appR by simp
  ultimately have "\<Theta>,\<Gamma> \<turnstile> mk_eq (subst_bvs (map (case_prod Fv) vs) s)
            (subst_bvs (map (case_prod Fv) vs) t)"
    using appR.IH by blast
  moreover have "\<Theta>,\<Gamma> \<turnstile> mk_eq (subst_bvs (map (case_prod Fv) vs) u)
      (subst_bvs (map (case_prod Fv) vs) u)"
    using proves_eq_reflexive[OF thy ok(2), of \<Gamma>, OF finite ctxt] by blast
  moreover obtain \<tau> where \<tau>: "typ_of 
    (subst_bvs (map (case_prod Fv) vs) s) = Some \<tau>"
    using ok wt_term_def by auto
  moreover obtain \<tau>' where "typ_of 
    (subst_bvs (map (case_prod Fv) vs) u) = Some (\<tau> \<rightarrow> \<tau>')"
    using \<tau> appR.prems(1) not_None_eq subst_bvs_App wt_term_def typ_of1_arg_typ typ_of_def 
    by (metis term_okD2)
  ultimately show ?case 
    using proves_eq_combination_rule_better thy finite ctxt by simp
next
  case (abs s t T)
  have "\<forall>a \<in> set vs. case a of (x, \<tau>) \<Rightarrow> (x, \<tau>) \<notin> fv s \<union> FV \<Gamma>" 
    using abs.prems(2) by auto

  have "\<forall>v\<in>set (map (case_prod Fv) vs) . is_closed v"
    by auto
  
  hence simp: "mk_eq (subst_bvs (map (case_prod Fv) vs) (Abs T s))
            (subst_bvs (map (case_prod Fv) vs) (Abs T t))
    = mk_eq (Abs T (subst_bvs1' s 1 (map (case_prod Fv) vs)))
            (Abs T (subst_bvs1' t 1 (map (case_prod Fv) vs)))"
    by simp

  have T_ok: "typ_ok \<Theta> T"
    using abs.prems term_ok_Types_typ_ok simp thy by auto

  have 1: "finite (fv (mk_eq (Abs T (subst_bvs1' s 1 (map (case_prod Fv) vs)))
          (Abs T (subst_bvs1' t 1 (map (case_prod Fv) vs)))) \<union> FV \<Gamma> \<union> fv s)"
    using finite finite_fv finite_FV by simp
  hence "\<exists>x . (x,T) \<notin> (fv (mk_eq (Abs T (subst_bvs1' s 1 (map (case_prod Fv) vs)))
          (Abs T (subst_bvs1' t 1 (map (case_prod Fv) vs)))) \<union> FV \<Gamma> \<union> fv s)"
  proof -
    have "\<And>v t P. (v, t) \<notin> P \<or> v \<in> fst ` P"
      by (metis (no_types) fst_conv image_eqI)
    then show ?thesis 
      using 1 variant_variable_fresh finite_Un finite_imageI fst_conv image_eqI by smt
  qed
  from this
  obtain x where x: "(x,T) \<notin> (fv (mk_eq (Abs T (subst_bvs1' s 1 (map (case_prod Fv) vs)))
          (Abs T (subst_bvs1' t 1 (map (case_prod Fv) vs)))) \<union> FV \<Gamma> \<union> fv s)"
    by fastforce
  hence x: "(x, T) \<notin> fv (mk_eq (Abs T (subst_bvs1' s 1 (map (case_prod Fv) vs)))
            (Abs T (subst_bvs1' t 1 (map (case_prod Fv) vs))))"
      "(x,T) \<notin> FV \<Gamma>" "(x, T) \<notin> fv s"
    by auto

  have ok: "term_ok \<Theta> (Abs T (subst_bvs1' s 1 (map (case_prod Fv) vs)))"
    using abs.prems(1) simp by auto


  thm subst_bvs_extend_lower_level
  have combine: "(subst_bv (term.Fv x T)
              (subst_bvs1' s 1 (map (\<lambda>(x, y). term.Fv x y) vs))) = 
      (subst_bvs (map (case_prod Fv) ((x,T)#vs)) s)"
    using subst_bvs_extend_lower_level 
    using \<open>\<forall>v\<in>set (map (\<lambda>(x, y). term.Fv x y) vs). is_closed v\<close> by auto
  have 1: "\<Theta>,\<Gamma> \<turnstile> mk_eq (subst_bvs (map (case_prod Fv) ((x,T)#vs)) s)
        (subst_bvs (map (case_prod Fv) ((x,T)#vs)) t)"
    apply(rule abs.IH)
    using ok apply (metis combine term_ok_subst_bv)
    using x abs.prems(2) by auto 
  have "\<Theta>, \<Gamma> \<turnstile> mk_eq 
    (Abs T (subst_bvs1' s 1 (map (case_prod Fv) vs)))
    (Abs T (subst_bvs1' t 1 (map (case_prod Fv) vs)))"
    apply (rule proves_ascend_abs_rule'[where x=x])
    using thy apply simp
    using x apply simp
    using x apply simp
    using T_ok apply simp
    using 1  \<open>\<forall>v\<in>set (map (\<lambda>(x, y). term.Fv x y) vs). is_closed v\<close> subst_bvs_extend_lower_level 
      finite ctxt by auto
  then show ?case
    using simp by auto
qed

lemma subst_bvs_empty[simp]: "subst_bvs [] t = t"
  by (simp add: subst_bvs_subst_bvs1')

lemma proves_beta_step:
  assumes thy: "wf_theory \<Theta>"
  assumes finite: "finite \<Gamma>"
  assumes term_ok: "term_ok \<Theta> t"
  assumes beta: "t \<rightarrow>\<^sub>\<beta> u"
  assumes ctxt: "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq t u"
proof-
  have unsimpt: "t = subst_bvs (map (case_prod Fv) []) t"
    by simp
  moreover have unsimpu: "u = subst_bvs (map (case_prod Fv) []) u"
    by simp
  ultimately have unsimp: "mk_eq t u = mk_eq 
    (subst_bvs (map (case_prod Fv) []) t)
    (subst_bvs (map (case_prod Fv) []) u)"
    by simp
  show ?thesis
    apply (subst unsimp)
    apply (rule proves_beta_step_pre)
    using assms by simp_all
qed

lemma proves_beta_steps:
  assumes thy: "wf_theory \<Theta>"
  assumes finite: "finite \<Gamma>"
  assumes term_ok: "term_ok \<Theta> t"
  assumes beta: "t \<rightarrow>\<^sub>\<beta>\<^sup>* u"
  assumes ctxt: "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq t u"
using beta term_ok proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case using finite ctxt by (simp add: proves_eq_reflexive thy)
next
  case (rtrancl_into_rtrancl a b c)
  hence "\<Theta>,\<Gamma> \<turnstile> mk_eq a b" by simp
  moreover have "\<Theta>,\<Gamma> \<turnstile> mk_eq b c"
    using proves_beta_step rtrancl_into_rtrancl.hyps(2)
    using beta_star_preserves_term_ok local.finite rtrancl_into_rtrancl.hyps(1)
      rtrancl_into_rtrancl.prems thy finite ctxt by blast
  ultimately show ?case 
    by (meson finite ctxt proved_terms_well_formed(2) proves_eq_transitive_rule[OF thy _ _ _ _ _ _ _ finite ctxt]
        term_ok_mk_eqD term_ok_mk_eq_same_typ thy)
qed

lemma proves_beta_norm:
  assumes thy: "wf_theory \<Theta>"
  assumes finite: "finite \<Gamma>"
  assumes term_ok: "term_ok \<Theta> t"
  assumes beta: "beta_norm t = Some u"
  assumes ctxt: "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq t u"
  using finite ctxt
    by (simp add: beta_norm_imp_beta_reds local.beta local.finite proves_beta_steps term_ok thy
      del: term_ok_def)

lemma beta_norm_preserves_proves:
  assumes thy: "wf_theory \<Theta>"
  assumes finite: "finite \<Gamma>"
  assumes term_ok: "\<Theta>, \<Gamma> \<turnstile> t"
  assumes beta: "beta_norm t = Some u"
  assumes ctxt: "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> u"
  using assms proves_eq_mp_rule_better[OF thy _ _ finite ctxt] proves_beta_norm[OF thy finite _ _ ctxt]
    proved_terms_well_formed(2) 
  by blast

lemma proves_eta_step_pre:
  assumes thy: "wf_theory \<Theta>"
  assumes finite: "finite \<Gamma>"
  assumes free: "\<forall>(x,\<tau>) \<in> set vs . (x,\<tau>) \<notin> fv t \<union> FV \<Gamma>"
  assumes term_ok': "term_ok \<Theta> (subst_bvs (map (case_prod Fv) vs) t)"
  assumes eta: "t \<rightarrow>\<^sub>\<eta> u"
  assumes ctxt: "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq
    (subst_bvs (map (case_prod Fv) vs) t)
    (subst_bvs (map (case_prod Fv) vs) u)"
using eta term_ok' free proof(induction t u arbitrary: vs rule: eta.induct)
  case (eta s T)

  have closeds: "\<forall>x \<in> set (map (case_prod Fv) vs) . is_closed x"
    using eta.prems(2) by auto
  hence simp: "subst_bvs (map (case_prod Fv) vs) (Abs T (s $ Bv 0))
    = Abs T (subst_bvs1' (s $ Bv 0) 1 (map (case_prod Fv) vs))"
    by auto
  hence simp': "subst_bvs (map (case_prod Fv) vs) (Abs T (s $ Bv 0))
    = Abs T (subst_bvs1' s 1 (map (case_prod Fv) vs) $ Bv 0)"
    by auto

  have closed: "is_closed (subst_bvs (map (case_prod Fv) vs) (Abs T (s $ Bv 0)))"
    using eta(2) wt_term_def typ_of_imp_closed by auto
  hence no_loose1: "\<not> loose_bvar (subst_bvs1' s 1 (map (case_prod Fv) vs)) 1"
    unfolding is_open_def
    by (metis One_nat_def Suc_eq_plus1 loose_bvar.simps(2) loose_bvar.simps(3) simp subst_bvs1'.simps(3))
  have not_dependent: "\<not> is_dependent (subst_bvs1' s 1 (map (case_prod Fv) vs))"
    using is_closed_subst_bvs1'_closeds
    by (simp add: closeds eta.hyps)

  have decr_simp: "subst_bv x (subst_bvs1' s 1 (map (case_prod Fv) vs))
    = subst_bvs (map (case_prod Fv) vs) (decr 0 s)" for x
    apply (simp add: closeds eta.hyps subst_bvs_decr)
    using is_dependent_def no_loose_bvar1_subst_bv2_decr not_dependent substn_subst_0' by auto
  have ok: "term_ok \<Theta> (subst_bvs1' s 1 (map (case_prod Fv) vs))" 
    by (metis One_nat_def Suc_leI eta.prems(1) is_dependent_def le_eq_less_or_eq
      loose_bvar_decr_unchanged loose_bvar_iff_exist_loose_bvar1 no_loose1 not_dependent simp' 
      term_ok_eta_red_step)
  hence ok_ind: "wf_term (sig \<Theta>) (subst_bvs1' s 1 (map (case_prod Fv) vs))" 
    using wt_term_def by simp

  obtain \<tau> where "typ_of (Abs T (subst_bvs1' (s $ Bv 0) 1 (map (case_prod Fv) vs))) = Some (T \<rightarrow> \<tau>)"
    using eta.prems(1) simp wt_term_def typ_of_Abs_body_typ'
    by (smt has_typ_iff_typ_of typ_of_def term_ok_def)
  hence ty: "typ_of (subst_bvs1' s 1 (map (case_prod Fv) vs)) = Some (T \<rightarrow> \<tau>)"
    using eta.eta eta_preserves_typ_of is_closed_decr_unchanged not_dependent
        ok simp simp' wt_term_def typ_of_imp_closed
    by (metis (no_types, lifting) has_typ_imp_closed term_ok_def)

  then show ?case
    using proves.eta[OF thy ok_ind, of _ _ \<Gamma>] ty decr_simp simp' 
    by (simp add: closeds eta.hyps subst_bvs_decr typ_of_imp_closed)  
next
  case (appL s t u)
  hence ok: "term_ok \<Theta> (subst_bvs (map (case_prod Fv) vs) s)"
            "term_ok \<Theta> (subst_bvs (map (case_prod Fv) vs) u)"
    by (metis subst_bvs_App term_ok_app_eqD)+
  moreover have "\<forall>a \<in> set vs. case a of (x, \<tau>) \<Rightarrow> (x, \<tau>) \<notin> fv s \<union> FV \<Gamma>"
    using appL by simp
  ultimately have "\<Theta>,\<Gamma> \<turnstile> mk_eq (subst_bvs (map (case_prod Fv) vs) s)
            (subst_bvs (map (case_prod Fv) vs) t)"
    using appL.IH by blast
  moreover have "\<Theta>,\<Gamma> \<turnstile> mk_eq (subst_bvs (map (case_prod Fv) vs) u)
      (subst_bvs (map (case_prod Fv) vs) u)"
    using proves_eq_reflexive[OF thy ok(2), of \<Gamma>, OF finite ctxt] by blast
  moreover obtain \<tau> where \<tau>: "typ_of 
    (subst_bvs (map (case_prod Fv) vs) u) = Some \<tau>"
    using ok wt_term_def by auto
  moreover obtain \<tau>' where "typ_of 
    (subst_bvs (map (case_prod Fv) vs) s) = Some (\<tau> \<rightarrow> \<tau>')"
    using \<tau> appL.prems(1) not_None_eq subst_bvs_App wt_term_def typ_of1_arg_typ typ_of_def
    by (smt has_typ_iff_typ_of typ_of_def term_ok_def)
  ultimately show ?case 
    using proves_eq_combination_rule_better thy finite ctxt by simp
next
  case (appR s t u)
  hence ok: "term_ok \<Theta> (subst_bvs (map (case_prod Fv) vs) s)"
            "term_ok \<Theta> (subst_bvs (map (case_prod Fv) vs) u)"
    by (metis subst_bvs_App term_ok_app_eqD)+
  moreover have "\<forall>a \<in> set vs. case a of (x, \<tau>) \<Rightarrow> (x, \<tau>) \<notin> fv s \<union> FV \<Gamma>"
    using appR by simp
  ultimately have "\<Theta>,\<Gamma> \<turnstile> mk_eq (subst_bvs (map (case_prod Fv) vs) s)
            (subst_bvs (map (case_prod Fv) vs) t)"
    using appR.IH by blast
  moreover have "\<Theta>,\<Gamma> \<turnstile> mk_eq (subst_bvs (map (case_prod Fv) vs) u)
      (subst_bvs (map (case_prod Fv) vs) u)"
    using proves_eq_reflexive[OF thy ok(2), of \<Gamma>, OF finite ctxt] by blast
  moreover obtain \<tau> where \<tau>: "typ_of 
    (subst_bvs (map (case_prod Fv) vs) s) = Some \<tau>"
    using ok wt_term_def by auto
  moreover obtain \<tau>' where "typ_of 
    (subst_bvs (map (case_prod Fv) vs) u) = Some (\<tau> \<rightarrow> \<tau>')"
    using \<tau> appR.prems(1) not_None_eq subst_bvs_App wt_term_def typ_of1_arg_typ typ_of_def
    by (metis term_okD2)
  ultimately show ?case 
    using proves_eq_combination_rule_better thy finite ctxt by simp
next
  case (abs s t T)
  have "\<forall>a \<in> set vs. case a of (x, \<tau>) \<Rightarrow> (x, \<tau>) \<notin> fv s \<union> FV \<Gamma>" 
    using abs.prems(2) by auto

  have "\<forall>v\<in>set (map (case_prod Fv) vs) . is_closed v"
    by auto
  
  hence simp: "mk_eq (subst_bvs (map (case_prod Fv) vs) (Abs T s))
            (subst_bvs (map (case_prod Fv) vs) (Abs T t))
    = mk_eq (Abs T (subst_bvs1' s 1 (map (case_prod Fv) vs)))
            (Abs T (subst_bvs1' t 1 (map (case_prod Fv) vs)))"
    by simp

  have T_ok: "typ_ok \<Theta> T"
    using abs.prems term_ok_Types_typ_ok simp thy by auto

  have 1: "finite (fv (mk_eq (Abs T (subst_bvs1' s 1 (map (case_prod Fv) vs)))
          (Abs T (subst_bvs1' t 1 (map (case_prod Fv) vs)))) \<union> FV \<Gamma> \<union> fv s)"
    using finite finite_fv finite_FV by simp
  hence "\<exists>x . (x,T) \<notin> (fv (mk_eq (Abs T (subst_bvs1' s 1 (map (case_prod Fv) vs)))
          (Abs T (subst_bvs1' t 1 (map (case_prod Fv) vs)))) \<union> FV \<Gamma> \<union> fv s)"
  proof -
    have "\<And>v t P. (v::variable, t::typ) \<notin> P \<or> v \<in> fst ` P"
      by (metis (no_types) fst_conv image_eqI)
    then show ?thesis 
    using 1 variant_variable_fresh finite_Un finite_imageI fst_conv image_eqI 
    by smt
  qed
  from this
  obtain x where x: "(x,T) \<notin> (fv (mk_eq (Abs T (subst_bvs1' s 1 (map (case_prod Fv) vs)))
          (Abs T (subst_bvs1' t 1 (map (case_prod Fv) vs)))) \<union> FV \<Gamma> \<union> fv s)"
    by fastforce
  hence x: "(x, T) \<notin> fv (mk_eq (Abs T (subst_bvs1' s 1 (map (case_prod Fv) vs)))
            (Abs T (subst_bvs1' t 1 (map (case_prod Fv) vs))))"
      "(x,T) \<notin> FV \<Gamma>" "(x, T) \<notin> fv s"
    by auto

  have ok: "term_ok \<Theta> (Abs T (subst_bvs1' s 1 (map (case_prod Fv) vs)))"
    using abs.prems(1) simp by auto

  have combine: "(subst_bv (Fv x T)
              (subst_bvs1' s 1 (map (case_prod Fv) vs))) = 
      (subst_bvs (map (case_prod Fv) ((x,T)#vs)) s)"
    using subst_bvs_extend_lower_level 
    using \<open>\<forall>v\<in>set (map (\<lambda>(x, y). term.Fv x y) vs). is_closed v\<close> by auto
  have 1: "\<Theta>,\<Gamma> \<turnstile> mk_eq (subst_bvs (map (case_prod Fv) ((x,T)#vs)) s)
        (subst_bvs (map (case_prod Fv) ((x,T)#vs)) t)"
    apply(rule abs.IH)
    using ok combine apply (metis term_ok_subst_bv)
    using x abs.prems(2) by auto 
  have "\<Theta>, \<Gamma> \<turnstile> mk_eq 
    (Abs T (subst_bvs1' s 1 (map (case_prod Fv) vs)))
    (Abs T (subst_bvs1' t 1 (map (case_prod Fv) vs)))"
    apply (rule proves_ascend_abs_rule'[where x=x])
    using thy apply simp
    using x apply simp
    using x apply simp
    using T_ok apply simp
    using 1  \<open>\<forall>v\<in>set (map (\<lambda>(x, y). term.Fv x y) vs). is_closed v\<close> subst_bvs_extend_lower_level
    finite ctxt by auto
  then show ?case
    using simp by auto
qed

lemma proves_eta_step:
  assumes thy: "wf_theory \<Theta>"
  assumes finite: "finite \<Gamma>"
  assumes term_ok: "term_ok \<Theta> t"
  assumes eta: "t \<rightarrow>\<^sub>\<eta> u"
  assumes ctxt: "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq t u"
proof-
  have unsimpt: "t = subst_bvs (map (case_prod Fv) []) t"
    by simp
  moreover have unsimpu: "u = subst_bvs (map (case_prod Fv) []) u"
    by simp
  ultimately have unsimp: "mk_eq t u = mk_eq 
    (subst_bvs (map (case_prod Fv) []) t)
    (subst_bvs (map (case_prod Fv) []) u)"
    by simp
  show ?thesis
    apply (subst unsimp)
    apply (rule proves_eta_step_pre)
    using assms by simp_all
qed

lemma proves_eta_steps:
  assumes thy: "wf_theory \<Theta>"
  assumes finite: "finite \<Gamma>"
  assumes term_ok: "term_ok \<Theta> t"
  assumes eta: "t \<rightarrow>\<^sub>\<eta>\<^sup>* u"
  assumes ctxt: "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq t u"
using eta term_ok proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case using finite ctxt by (simp add: proves_eq_reflexive thy)
next
  case (rtrancl_into_rtrancl a b c)
  hence "\<Theta>,\<Gamma> \<turnstile> mk_eq a b" by simp
  moreover have "\<Theta>,\<Gamma> \<turnstile> mk_eq b c"
    using proves_eta_step rtrancl_into_rtrancl.hyps(2) eta_star_preserves_term_ok local.finite
      rtrancl_into_rtrancl.hyps(1) rtrancl_into_rtrancl.prems thy finite ctxt
      by blast
  ultimately show ?case
    by (meson proved_terms_well_formed(2) proves_eq_transitive_rule[OF thy _ _ _ _ _ _ _ finite ctxt]
        term_ok_mk_eqD term_ok_mk_eq_same_typ thy)
qed

lemma proves_eta_norm:
  assumes thy: "wf_theory \<Theta>"
  assumes finite: "finite \<Gamma>"
  assumes term_ok: "term_ok \<Theta> t"
  assumes eta: "eta_norm t = u"
  assumes ctxt: "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> mk_eq t u"
  using finite ctxt
  by (simp add: eta_norm_imp_eta_reds local.eta local.finite proves_eta_steps term_ok thy del: term_ok_def)

lemma eta_norm_preserves_proves:
  assumes thy: "wf_theory \<Theta>"
  assumes finite: "finite \<Gamma>"
  assumes term_ok: "\<Theta>, \<Gamma> \<turnstile> t"
  assumes eta: "eta_norm t = u"
  assumes ctxt: "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> u"
  using assms proves_eq_mp_rule_better[OF thy _ _ finite ctxt]
    proves_eta_norm[OF thy finite _ _ ctxt] proved_terms_well_formed(2) by blast

lemma beta_eta_norm_preserves_proves:
  assumes thy: "wf_theory \<Theta>"
  assumes finite: "finite \<Gamma>"
  assumes term_ok: "\<Theta>, \<Gamma> \<turnstile> t"
  assumes beta_eta: "beta_eta_norm t = Some u"
  assumes ctxt: "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> u"
  using beta_eta beta_norm_preserves_proves[OF thy finite _ _ ctxt]
    eta_norm_preserves_proves[OF thy finite _ _ ctxt] finite term_ok thy by blast

lemma forall_elim':
  assumes thy: "wf_theory \<Theta>"
  assumes all: "\<Theta>, \<Gamma> \<turnstile> Ct STR ''Pure.all'' ((\<tau> \<rightarrow> propT) \<rightarrow> propT) $ B"
  assumes a: "has_typ a \<tau>" "wf_term (sig \<Theta>) a"
  assumes ctxt: "finite \<Gamma>" "\<forall>A\<in>\<Gamma>. term_ok \<Theta> A" "\<forall>A\<in>\<Gamma>. typ_of A = Some propT"
  shows "\<Theta>, \<Gamma> \<turnstile> B \<bullet> a"
proof(cases "is_Abs B")
  case True
  from this obtain t T where Abs: "B = Abs T t"
    using is_Abs_def by auto
  have "T = \<tau>"
    by (smt Abs all list.inject proved_terms_well_formed(1) typ.inject(1) typ_of1.simps(1) 
        typ_of_Abs_body_typ' typ_of_def typ_of_fun)
  then show ?thesis
    using True Abs all a by (auto intro: forall_elim[where \<tau>=\<tau>])
next
  case False

  have wf_B: "wf_term (sig \<Theta>) B" 
    using all proved_terms_well_formed(2) term_okD1 term_ok_app_eqD by blast
  have B_typ: "\<turnstile>\<^sub>\<tau> B : \<tau> \<rightarrow> propT"
    by (metis (no_types, lifting) all proved_terms_well_formed(1) typ_of1.simps(1) typ_of_def 
        typ_of_fun typ_of_imp_has_typ)

  have "B \<bullet> a = B $ a"
    using False by (metis betapply.elims term.discI(4))
  moreover have "Abs \<tau> (B $ Bv 0) \<bullet> a = B $ a"
    using B_typ closed_subst_bv_no_change subst_bv_def typ_of_imp_closed 
    by (auto simp add: subst_bv_def incr_boundvars_def)
  ultimately have simp: "B \<bullet> a = subst_bv a (B $ Bv 0)"
    by auto

  have 1: "\<Theta>, \<Gamma> \<turnstile> mk_eq (Abs \<tau> (B $ Bv 0)) B" 
    by (rule proves.eta[OF thy wf_B B_typ])
  have 2: "\<Theta>, \<Gamma> \<turnstile> mk_eq B (Abs \<tau> (B $ Bv 0))" 
    apply (rule proves_eq_symmetric_rule[OF thy _ _ _ 1 ctxt])
    using wf_B  B_typ term_ok_def wt_term_def apply blast
    using 1 proved_terms_well_formed(2) term_ok_mk_eqD apply blast
    using B_typ Logic.typ_of_eta_expand by auto
  have 3: "\<Theta>, \<Gamma> \<turnstile> mk_eq (Ct STR ''Pure.all'' ((\<tau> \<rightarrow> propT) \<rightarrow> propT)) (Ct STR ''Pure.all'' ((\<tau> \<rightarrow> propT) \<rightarrow> propT))"
    apply (rule proves_eq_reflexive[OF thy _ ctxt])
    using all proved_terms_well_formed(2) term_ok_app_eqD by blast

  have 4: "\<Theta>, \<Gamma> \<turnstile> mk_eq 
    (Ct STR ''Pure.all'' ((\<tau> \<rightarrow> propT) \<rightarrow> propT) $ B)
    (Ct STR ''Pure.all'' ((\<tau> \<rightarrow> propT) \<rightarrow> propT) $ (Abs \<tau> (B $ Bv 0)))"
    apply (rule proves_eq_combination_rule_better[OF thy 3 2 _ _ ctxt, where \<tau>="(\<tau> \<rightarrow> propT)" and \<tau>'= propT])
    using typ_of_def apply auto[1]
    using B_typ by blast

  have 5: "\<Theta>, \<Gamma> \<turnstile> (Ct STR ''Pure.all'' ((\<tau> \<rightarrow> propT) \<rightarrow> propT) $ (Abs \<tau> (B $ Bv 0)))"
    by (rule proves_eq_mp_rule_better[OF thy 4 all ctxt])
  
  show ?thesis
    apply (subst simp)
    apply (rule proves.forall_elim[OF 5])
    using assms(3) apply blast
    using assms(4) by blast
  qed
end
