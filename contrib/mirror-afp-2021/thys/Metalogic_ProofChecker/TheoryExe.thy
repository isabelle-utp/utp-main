section "Executable Signature and Theory"

(* Proofs are ugly, clean up if time *)

theory TheoryExe
  imports SortsExe Theory Instances
begin

datatype exesignature = ExeSignature 
  (execonst_type_of: "(name \<times> typ) list")
  (exetyp_arity_of: "(name \<times> nat) list")
  (exesorts: exeosig)

lemma exe_const_type_of_ok: "
  alist_conds cto \<Longrightarrow>
  (\<forall>ty \<in> Map.ran (map_of cto) . typ_ok_sig (map_of cto, ta, sa) ty)
  \<longleftrightarrow> (\<forall>ty \<in> snd ` set cto  . typ_ok_sig (map_of cto, ta, sa) ty)"
  by (simp add: ran_distinct)

fun exe_wf_sig where
  "exe_wf_sig (ExeSignature cto tao sa) = (exe_wf_osig sa \<and>
  fst ` set (exetcsigs sa) = fst ` set tao 
  \<and> (\<forall>type \<in> fst ` set (exetcsigs sa). 
    (\<forall>ars \<in> snd ` set (the (lookup (\<lambda>k. k=type) (exetcsigs sa))) .
      the (lookup (\<lambda>k. k=type) tao) = length ars))
  \<and> (\<forall>ty \<in> snd ` set cto . typ_ok_sig (map_of cto, map_of tao, translate_osig sa) ty))"

lemma exe_wf_sig_imp_wf_sig:
  assumes "alist_conds cto" "alist_conds tao" "exe_osig_conds sa" "(exe_wf_osig sa
  \<and> fst ` set (exetcsigs sa) = fst ` set tao 
  \<and> (\<forall>type \<in> fst ` set (exetcsigs sa).  
      (\<forall>ars \<in> snd ` set (the (lookup (\<lambda>k. k=type) (exetcsigs sa))) .
      the (lookup (\<lambda>k. k=type) tao) = length ars)))
  \<and> (\<forall>ty \<in> snd ` set cto . typ_ok_sig (map_of cto, map_of tao, translate_osig sa) ty)"
  shows "wf_sig (map_of cto, map_of tao, translate_osig sa)"
proof-
  {
    fix type y
    assume p: "exe_osig_conds sa" "trans (fst (translate_osig sa))" "snd (translate_osig sa) type = Some y"
      hence "exe_ars_conds (exetcsigs sa)"
        using exe_osig_conds_def by blast
    from p have "translate_ars (exetcsigs sa) type = Some y"
      by (metis snd_conv translate_osig.elims)
    hence "(type, y) \<in> set (map (apsnd map_of) (exetcsigs sa))"
      using map_of_SomeD by force
    hence "type \<in> fst ` set (exetcsigs sa)" by force
    from this obtain x where "lookup (\<lambda>x. x=type) (exetcsigs sa) = Some x" 
      using key_present_imp_eq_lookup_finds_value by metis
    hence "map_of x = y"
      by (metis \<open>exe_ars_conds (snd sa)\<close> \<open>translate_ars (snd sa) type = Some y\<close> 
          exe_ars_conds_def in_alist_imp_in_map_of lookup_eq_map_of_ap 
          map_of_SomeD option.sel)
    have "\<exists>y. (type, y) \<in> set tao"
      using \<open>type \<in> fst ` set (exetcsigs sa)\<close> assms(4) by auto
  }
  note 1 = this

  {
    fix ars type y
    assume p: "exe_osig_conds sa"
      "trans (fst (translate_osig sa))"
      "\<forall>x\<in>set cto. typ_ok_sig (map_of cto, map_of tao, translate_osig sa) (snd x)"
      "ars \<in> ran y"
      "snd (translate_osig sa) type = Some y"

      hence "exe_ars_conds (exetcsigs sa)"
        using exe_osig_conds_def by blast
      from p(1-2) p(5) have "translate_ars (exetcsigs sa) type = Some y"
        by (metis snd_conv translate_osig.elims)
      hence "(type, y) \<in> set (map (apsnd map_of) (exetcsigs sa))"
        using map_of_SomeD by force
      hence dom: "type \<in> fst ` set (exetcsigs sa)" by force
      from this obtain x where x: "lookup (\<lambda>x. x=type) (exetcsigs sa) = Some x" 
        using key_present_imp_eq_lookup_finds_value by metis
      hence "map_of x = y"
        by (metis \<open>exe_ars_conds (snd sa)\<close> \<open>translate_ars (snd sa) type = Some y\<close> 
            exe_ars_conds_def in_alist_imp_in_map_of lookup_eq_map_of_ap map_of_SomeD option.sel)
      have "ars \<in> snd ` set x"
        by (metis \<open>map_of x = y\<close> image_iff in_range_if_ex_key map_of_SomeD p(4) snd_conv)

      have "type \<in> fst ` set tao"
        apply (simp add: \<open>type \<in> fst ` set (exetcsigs sa)\<close> assms(4))
        using assms(4) dom  by blast
      moreover have 1: "(\<forall>ars \<in> snd ` set (the (lookup (\<lambda>k. k=type) (exetcsigs sa))) .
        the (lookup (\<lambda>k. k=type) tao) = length ars)"
        using \<open>type \<in> fst ` set (exetcsigs sa)\<close> assms(4) by blast
      
      ultimately have "the (lookup (\<lambda>k. k = type) tao) = length ars" 
        using \<open>lookup (\<lambda>x. x = type) (exetcsigs sa) = Some x\<close> \<open>map_of x = y\<close> 
            in_range_if_ex_key map_of_SomeD option.sel p(3) snd_conv
        by (simp add: 1 \<open>ars \<in> snd ` set x\<close>)
      hence "the (map_of tao type) = length ars"
       by (metis \<open>the (lookup (\<lambda>k. k = type) tao) = length ars\<close> lookup_eq_map_of_ap)
  }
  note 2 = this
  {
    fix a b x y
    assume p: "fst ` set b = fst ` set tao"
      "(x, y) \<in> set tao"
      "sa = (a, b)"

    have "x \<in> fst ` set b"
      by (metis fst_conv image_iff p(1) p(2))
    from this obtain ars where "lookup (\<lambda>k. k=x) b = Some ars"
      by (metis key_present_imp_eq_lookup_finds_value)
    hence "(x,ars) \<in> set b"
      by (simp add: lookup_present_eq_key')
    hence "lookup (\<lambda>k. k=x) (map (apsnd map_of) b) = Some (map_of ars)"
      by (metis assms(3) exe_ars_conds_def exe_osig_conds_def in_alist_imp_in_map_of
          lookup_eq_map_of_ap p(3) snd_conv translate_ars.simps)
    hence "\<exists>y. map_of (map (apsnd map_of) b) x = Some y"
      by (metis lookup_eq_map_of_ap)
  }
  note 3 = this
  {
    fix a b x
    assume p: "alist_conds cto"
      "x \<in> ran (map_of cto)"
      "sa = (a, b)"
    have "typ_ok_sig (map_of cto, map_of tao, set a,  map_of (map (apsnd map_of) b)) x"
      using assms(4) p(1) p(2) p(3) ran_distinct by fastforce
  }
  note 4 = this
  have "wf_osig (translate_osig sa)"
    using assms(4) wf_osig_iff_exe_wf_osig by simp
  thus ?thesis apply (cases sa)
    using 1 2 3 4 assms by auto
qed

lemma wf_sig_imp_exe_wf_sig:
  assumes "alist_conds cto" "alist_conds tao" "exe_osig_conds sa"
    "wf_sig (map_of cto, map_of tao, translate_osig sa)" 
  shows "(exe_wf_osig sa
    \<and> fst ` set (exetcsigs sa) = fst ` set tao 
    \<and> (\<forall>type \<in> fst ` set (exetcsigs sa). 
        (\<forall>ars \<in> snd ` set (the (lookup (\<lambda>k. k=type) (exetcsigs sa))) .
        the (lookup (\<lambda>k. k=type) tao) = length ars)))
    \<and> (\<forall>ty \<in> snd ` set cto . typ_ok_sig (map_of cto, map_of tao, translate_osig sa) ty)"
proof-
  {
    fix a b x y
    assume p: "alist_conds tao"
      "exe_ars_conds b"
      "dom (map_of (map (apsnd map_of) b)) = dom (map_of tao)"
      "(x, y) \<in> set b"

    hence "x \<in> fst ` set tao"
      by (metis domIff dom_map_of_conv_image_fst exe_ars_conds_def 
          in_alist_imp_in_map_of option.distinct(1) translate_ars.simps)
  }
  note 1 = this
  {
    fix cl n ar and tcs :: "(String.literal \<times> (String.literal \<times> String.literal set list) list) list"
    assume p: "dom (map_of (map (apsnd map_of) tcs)) = dom (map_of tao)"
      "alist_conds tao"
      "(n, ar) \<in> set tao"
    
    obtain mgd where "translate_ars tcs n = Some mgd"
      using p by (metis Some_eq_map_of_iff domI domIff option.exhaust_sel translate_ars.simps)
    hence "map_of (map (apsnd map_of) tcs) n = Some mgd" 
      by (simp add: tcsigs_translate exe_osig_conds_def p)
    hence "n \<in> fst ` set (map (apsnd map_of) tcs)"
      by (meson domI domIff map_of_eq_None_iff)
    then have "n \<in> fst ` set tcs" 
      by force
  }
  note 2 = this
  {
    fix cl tcs n K c Ss 
    assume p: "(n, K) \<in> set tcs"
      "(c, Ss) \<in> set (the (lookup (\<lambda>k. k = n) tcs))"
      "exe_ars_conds tcs"
      "dom (map_of (map (apsnd map_of) tcs)) = dom (map_of tao)"
      "\<forall>type\<in>dom (map_of tao). \<forall>ars\<in>ran (the (map_of (map (apsnd map_of) tcs) type)).
          the (map_of tao type) = length ars"
    
    have 1: "translate_ars tcs n = Some (map_of K)"
      using exe_ars_conds_def in_alist_imp_in_map_of p(1-3) by blast
    have 2: "map_of K c = Some Ss"
      using p(1-3)
      by (metis Some_eq_map_of_iff exe_ars_conds_def image_iff lookup_eq_map_of_ap
          option.sel snd_conv)
    have "the (lookup (\<lambda>k. k = n) tao) = length Ss"
      using 1 2 p(4,5)
      by (metis domIff lookup_eq_map_of_ap option.distinct(1) option.sel ranI translate_ars.simps)
  }
  note 3 = this

  have 1: "wf_osig (translate_osig sa)" "dom (tcsigs (translate_osig sa)) = dom (map_of tao)"
    "(\<forall>type \<in> dom (tcsigs (translate_osig sa)). 
    (\<forall>ars \<in> ran (the (tcsigs (translate_osig sa) type)) . the ((map_of tao) type) = length ars))"
    "(\<forall>ty \<in> Map.ran (map_of cto) . wf_type (map_of cto, map_of tao, translate_osig sa) ty)"
    using assms(4) by auto
  note pre = 1
           
  have "exe_wf_osig sa"
    using "1"(1) wf_osig_iff_exe_wf_osig by blast
  moreover have "fst ` set (snd sa) = fst ` set tao"
  proof
    show "fst ` set (snd sa) \<subseteq> fst ` set tao"
      using assms(3-4)
      by (clarsimp simp add: dom_map_of_conv_image_fst exe_ars_conds_def exe_osig_conds_def)
        (metis tcsigs_translate assms(3) domIff in_alist_imp_in_map_of option.simps(3))
  next
    show "fst ` set (snd sa) \<supseteq> fst ` set tao" 
      using "1"(2) "2" assms(2-3) tcsigs_translate by auto
  qed
  moreover have "(\<forall>type\<in>fst ` set (snd sa).  \<forall>ars\<in>snd ` set (the (lookup (\<lambda>k. k = type) (snd sa))).
        the (lookup (\<lambda>k. k = type) tao) = length ars)"
  proof (standard+, goal_cases)
    case (1 n Ss) 
    obtain c where c: "(c, Ss) \<in> set (the (lookup (\<lambda>k. k = n) (snd sa)))"
      using "1"(2) by force
    have "dom (map_of (map (apsnd map_of) (snd sa))) = dom (map_of tao)"
      using assms(3) pre(2) tcsigs_translate by fastforce
    show ?case
      using assms(3) pre(2) c tcsigs_translate pre(2-3) domI 
      by (fastforce simp add: exe_osig_conds_def tcsigs_translate[OF assms(3)] 
          "1"(1) key_present_imp_eq_lookup_finds_value lookup_present_eq_key'
          split: option.splits intro!: 3[of _ "the (lookup (\<lambda>k. k = n) (snd sa))" "snd sa" c])+
  qed
  moreover have "(\<forall>ty \<in> Map.ran (map_of cto) . wf_type (map_of cto, map_of tao, translate_osig sa) ty)"
    using "1"(4) by blast
  ultimately show ?thesis 
    by (simp add: assms(1) ran_distinct)
qed

lemma wf_sig_iff_exe_wf_sig_pre: "alist_conds cto \<Longrightarrow> alist_conds tao \<Longrightarrow> exe_osig_conds sa
  \<Longrightarrow> wf_sig (map_of cto, map_of tao, translate_osig sa) = (exe_wf_osig sa
  \<and> fst ` set (exetcsigs sa) = fst ` set tao  
  \<and> (\<forall>type \<in> fst ` set (exetcsigs sa).
      (\<forall>ars \<in> snd ` set (the (lookup (\<lambda>k. k=type) (exetcsigs sa))) .
      the (lookup (\<lambda>k. k=type) tao) = length ars))
  \<and> (\<forall>ty \<in> snd ` set cto . typ_ok_sig (map_of cto, map_of tao, translate_osig sa) ty))"
  using exe_wf_sig_imp_wf_sig wf_sig_imp_exe_wf_sig by meson

lemma wf_sig_iff_exe_wf_sig: "alist_conds cto \<Longrightarrow> alist_conds tao \<Longrightarrow> exe_osig_conds sa
  \<Longrightarrow> wf_sig (map_of cto, map_of tao, translate_osig sa)
  \<longleftrightarrow> exe_wf_sig (ExeSignature cto tao sa)"
  unfolding exe_wf_sig.simps
  using wf_sig_iff_exe_wf_sig_pre by presburger

fun translate_signature :: "exesignature \<Rightarrow> signature" where
  "translate_signature (ExeSignature cto tao sa) 
    = (map_of cto, map_of tao, translate_osig sa)"

fun exetyp_ok_sig :: "exesignature \<Rightarrow> typ \<Rightarrow> bool" where
  "exetyp_ok_sig \<Sigma> (Ty c Ts) = (case lookup (\<lambda>k. k=c) (exetyp_arity_of \<Sigma>) of
    None \<Rightarrow> False
  | Some ar \<Rightarrow> length Ts = ar \<and> list_all (exetyp_ok_sig \<Sigma>) Ts)"
| "exetyp_ok_sig \<Sigma> (Tv _ S) = exewf_sort (execlasses (exesorts \<Sigma>)) S"

thm exewf_sort_def
definition [simp]: "exesort_ok_sig \<Sigma> S \<equiv> exesort_ex (execlasses (exesorts \<Sigma>)) S 
  \<and> exenormalized_sort (execlasses (exesorts \<Sigma>)) S"

lemma typ_arity_lookup_code: "type_arity (translate_signature \<Sigma>) n = lookup (\<lambda>k. k = n) (exetyp_arity_of \<Sigma>)"
  by (cases \<Sigma>) (simp add: lookup_eq_map_of_ap)

lemma typ_ok_sig_code: 
  assumes "exe_osig_conds (exesorts \<Sigma>)"
  shows "typ_ok_sig (translate_signature \<Sigma>) ty = exetyp_ok_sig \<Sigma> ty"
  using assms apply (induction ty) apply simp
  apply (auto split: option.splits simp add: wf_sort_def list_all_iff typ_arity_lookup_code)[]
  using wf_sort_code by (cases \<Sigma>) (simp add: exe_osig_conds_def classes_translate)

fun exe_wf_sig' where
  "exe_wf_sig' (ExeSignature cto tao sa) = (exe_wf_osig sa \<and>
  fst ` set (exetcsigs sa) = fst ` set tao 
  \<and> (\<forall>type \<in> fst ` set (exetcsigs sa). 
    (\<forall>ars \<in> snd ` set (the (lookup (\<lambda>k. k=type) (exetcsigs sa))) .
      the (lookup (\<lambda>k. k=type) tao) = length ars))
  \<and> (\<forall>ty \<in> snd ` set cto . exetyp_ok_sig (ExeSignature cto tao sa) ty))"

lemma exe_wf_sig_code[code]: "exe_wf_sig \<Sigma> = exe_wf_sig' \<Sigma>"
  using typ_ok_sig_code by (cases \<Sigma>, simp, metis exesignature.sel(3) translate_signature.simps)

fun exeterm_ok' :: "exesignature \<Rightarrow> term \<Rightarrow> bool" where
  "exeterm_ok' \<Sigma> (Fv _ T) = exetyp_ok_sig \<Sigma> T"
| "exeterm_ok' \<Sigma> (Bv _) = True"
| "exeterm_ok' \<Sigma> (Ct s T) = (case lookup (\<lambda>k. k=s) (execonst_type_of \<Sigma>) of
    None \<Rightarrow> False
  | Some ty \<Rightarrow> exetyp_ok_sig \<Sigma> T \<and> tinstT T ty)"
| "exeterm_ok' \<Sigma> (t $ u) \<longleftrightarrow> exeterm_ok' \<Sigma> t \<and> exeterm_ok' \<Sigma> u" 
| "exeterm_ok' \<Sigma> (Abs T t) \<longleftrightarrow> exetyp_ok_sig \<Sigma> T \<and> exeterm_ok' \<Sigma> t"

lemma const_type_of_lookup_code: "const_type (translate_signature \<Sigma>) n = lookup (\<lambda>k. k = n) (execonst_type_of \<Sigma>)"
  by (cases \<Sigma>) (simp add: lookup_eq_map_of_ap)

lemma wt_term_code: 
  assumes "exe_osig_conds (exesorts \<Sigma>)"
  shows "term_ok' (translate_signature \<Sigma>) t = exeterm_ok' \<Sigma> t"
  by (induction t) (auto simp add: const_type_of_lookup_code assms typ_ok_sig_code split: option.splits)

datatype exetheory = ExeTheory (exesig: exesignature) (exeaxioms_of: "term list")

lemma exetheory_full_exhaust: "(\<And>const_type typ_arity sorts axioms. 
    \<Theta> = (ExeTheory (ExeSignature const_type typ_arity sorts) axioms) \<Longrightarrow> P)
  \<Longrightarrow> P"
  apply (cases \<Theta>) subgoal for \<Sigma> axioms apply (cases \<Sigma>) by auto done

definition "exe_sig_conds \<Sigma> \<equiv> alist_conds (execonst_type_of \<Sigma>) \<and> alist_conds (exetyp_arity_of \<Sigma>) 
  \<and> exe_osig_conds (exesorts \<Sigma>)"

abbreviation "illformed_theory \<equiv>  ((Map.empty, Map.empty, illformed_osig), {})"

lemma illformed_theory_not_wf_theory: "\<not> wf_theory illformed_theory" 
  by simp

fun translate_theory :: "exetheory \<Rightarrow> theory" where
  "translate_theory (ExeTheory \<Sigma> ax) = (if exe_sig_conds \<Sigma> then 
    (translate_signature \<Sigma>, set ax) else illformed_theory)"

fun exe_wf_theory where "exe_wf_theory (ExeTheory (ExeSignature cto tao sa) ax) \<longleftrightarrow>
  exe_sig_conds (ExeSignature cto tao sa) \<and>
    (\<forall>p \<in> set ax . term_ok (translate_theory (ExeTheory (ExeSignature cto tao sa) ax)) p \<and> typ_of p = Some propT)
  \<and> is_std_sig (translate_signature (ExeSignature cto tao sa))
  \<and> exe_wf_sig (ExeSignature cto tao sa)
  \<and> eq_axs \<subseteq> set ax"

lemma wf_sig_iff_exe_wf_sig': "exe_sig_conds \<Sigma> \<Longrightarrow>
    wf_sig (translate_signature \<Sigma>) \<longleftrightarrow>
    exe_wf_sig \<Sigma>" 
  by (metis exe_sig_conds_def exesignature.exhaust_sel wf_sig_iff_exe_wf_sig translate_signature.simps)

lemma wf_sig_imp_exe_wf_sig': "exe_sig_conds \<Sigma> \<Longrightarrow>
    wf_sig (translate_signature \<Sigma>) \<Longrightarrow>
    exe_wf_sig \<Sigma>" 
  by (metis exe_sig_conds_def exesignature.exhaust_sel wf_sig_iff_exe_wf_sig translate_signature.simps)

lemma exe_wf_sig_imp_wf_sig': "exe_sig_conds \<Sigma> \<Longrightarrow>
    exe_wf_sig \<Sigma>
    \<Longrightarrow> wf_sig (translate_signature \<Sigma>)" 
  by (metis exe_sig_conds_def exesignature.exhaust_sel wf_sig_iff_exe_wf_sig translate_signature.simps)

lemma wf_theory_translate_imp_exe_wf_theory:
  assumes "wf_theory (translate_theory a)" shows "exe_wf_theory a" 
proof-
  have "exe_sig_conds (exesig a)" using assms
    by (metis exetheory.collapse illformed_theory_not_wf_theory translate_theory.simps)
  moreover have "wf_sig (translate_signature (exesig a))
    \<longleftrightarrow> exe_wf_sig (exesig a)"
    by (simp add: calculation(1) wf_sig_iff_exe_wf_sig')
  ultimately show ?thesis using assms
    by (cases a rule: exe_wf_theory.cases) (fastforce simp add: image_iff eq_fst_iff)
qed

lemma exe_wf_theory_translate_imp_wf_theory:
  assumes "exe_wf_theory a" shows "wf_theory (translate_theory a)"
proof-
  have "exe_sig_conds (exesig a)" using assms
    by (metis (full_types) exe_wf_theory.simps exesignature.exhaust_sel exetheory.sel(1) translate_theory.cases)
  moreover hence "
  (\<forall>ty \<in> Map.ran (map_of (execonst_type_of (exesig a))) . typ_ok_sig (translate_signature (exesig a)) ty)
  \<longleftrightarrow> (\<forall>ty \<in> snd ` set (execonst_type_of (exesig a)) . typ_ok_sig (translate_signature (exesig a)) ty)"
    by (simp add: exe_sig_conds_def ran_distinct)
  moreover have "wf_sig (translate_signature (exesig a))
    \<longleftrightarrow> exe_wf_sig (exesig a)"
    by (simp add: calculation(1) wf_sig_iff_exe_wf_sig')
  ultimately show ?thesis
    using assms by (cases a rule: exe_wf_theory.cases) auto 
qed

lemma wf_theory_translate_iff_exe_wf_theory:
  "wf_theory (translate_theory a) \<longleftrightarrow> exe_wf_theory a"
  using exe_wf_theory_translate_imp_wf_theory wf_theory_translate_imp_exe_wf_theory by blast

fun exeis_std_sig where "exeis_std_sig (ExeSignature cto tao sorts) \<longleftrightarrow>
    lookup (\<lambda>k. k = STR ''fun'') tao = Some 2 \<and> lookup (\<lambda>k. k = STR ''prop'') tao  = Some 0 
  \<and> lookup (\<lambda>k. k = STR ''itself'') tao = Some 1
  \<and> lookup (\<lambda>k. k = STR ''Pure.eq'') cto 
    = Some ((Tv (Var (STR '''a'', 0)) full_sort) \<rightarrow> ((Tv (Var (STR '''a'', 0)) full_sort) \<rightarrow> propT))
  \<and> lookup (\<lambda>k. k = STR ''Pure.all'') cto = Some ((Tv (Var  (STR '''a'', 0)) full_sort \<rightarrow> propT) \<rightarrow> propT)
  \<and> lookup (\<lambda>k. k = STR ''Pure.imp'') cto = Some (propT \<rightarrow> (propT \<rightarrow> propT))
  \<and> lookup (\<lambda>k. k = STR ''Pure.type'') cto = Some (itselfT (Tv (Var (STR '''a'', 0)) full_sort))"

lemma is_std_sig_code: "is_std_sig (translate_signature \<Sigma>) = exeis_std_sig \<Sigma>"
  by (cases \<Sigma>) (auto simp add: lookup_eq_map_of_ap)

fun exe_wf_theory' where "exe_wf_theory' (ExeTheory (ExeSignature cto tao sa) ax) \<longleftrightarrow>
  exe_sig_conds (ExeSignature cto tao sa) \<and>
    (\<forall>p \<in> set ax . exeterm_ok' (ExeSignature cto tao sa) p \<and> typ_of p = Some propT)
  \<and> exeis_std_sig (ExeSignature cto tao sa)
  \<and> exe_wf_sig (ExeSignature cto tao sa)
  \<and> eq_axs \<subseteq> set ax"

lemma term_ok'_code: 
  assumes "exe_osig_conds (exesorts (ExeSignature cto tao sa))"
  shows "(term_ok' (translate_signature (ExeSignature cto tao sa)) p \<and> typ_of p = Some propT)
    = (exeterm_ok' (ExeSignature cto tao sa) p \<and> typ_of p = Some propT)"
  using wt_term_code[OF assms] by force

lemma term_ok_translate_code_step:
  assumes "exe_sig_conds (ExeSignature cto tao sa)"
  shows "(term_ok (translate_theory (ExeTheory (ExeSignature cto tao sa) ax)) p \<and> typ_of p = Some propT)
    = (term_ok' (translate_signature (ExeSignature cto tao sa)) p \<and> typ_of p = Some propT)"
  using assms by (auto simp add: wt_term_def split: if_splits)
  
lemma term_ok_theory_cond_code:
  assumes "exe_sig_conds (ExeSignature cto tao sa)"
  shows"(\<forall>p \<in> set ax . term_ok (translate_theory (ExeTheory (ExeSignature cto tao sa) ax)) p \<and> typ_of p = Some propT)
    = (\<forall>p \<in> set ax . exeterm_ok' (ExeSignature cto tao sa) p \<and> typ_of p = Some propT)"
  using assms wf_term_imp_term_ok' exe_sig_conds_def wt_term_code
  by (fastforce simp add: term_ok_translate_code_step wt_term_code wt_term_def)
  
lemma exe_wf_theory_code[code]: "exe_wf_theory \<Theta> = exe_wf_theory' \<Theta>"
  apply (cases \<Theta> rule: exetheory_full_exhaust)
  apply (simp only: exe_wf_theory.simps exe_wf_theory'.simps)
  using term_ok_theory_cond_code is_std_sig_code by meson

end