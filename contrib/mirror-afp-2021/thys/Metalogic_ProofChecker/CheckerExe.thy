
theory CheckerExe
  imports TheoryExe ProofTerm
begin

abbreviation "exetyp_ok \<Theta> \<equiv> exetyp_ok_sig (exesig \<Theta>)"

lemma typ_ok_code: 
  assumes "exe_wf_theory' \<Theta>"
  shows "typ_ok (translate_theory \<Theta>) ty = exetyp_ok \<Theta> ty"
  using assms typ_ok_sig_code
  by (metis exe_sig_conds_def exe_wf_theory.simps exe_wf_theory_code exesignature.exhaust
      exetheory.sel(1) sig.simps translate_theory.elims typ_ok_def wf_type_iff_typ_ok_sig)

definition [simp]: "execlass_leq cs c1 c2 = List.member cs (c1,c2)"
lemma execlass_leq_code: "class_leq (set cs) c1 c2 = execlass_leq cs c1 c2"
  by (simp add: class_leq_def class_les_def member_def)

definition "exesort_leq sub s1 s2 = (\<forall>c\<^sub>2 \<in> s2 . \<exists>c\<^sub>1 \<in> s1. execlass_leq sub c\<^sub>1 c\<^sub>2)"
lemma exesort_les_code: "sort_leq (set cs) c1 c2 = exesort_leq cs c1 c2"
  by (simp add: execlass_leq_code exesort_leq_def sort_leq_def)

fun exehas_sort :: "exeosig \<Rightarrow> typ \<Rightarrow> sort \<Rightarrow> bool" where
"exehas_sort oss (Tv _ S) S' = exesort_leq (execlasses oss) S S'" |
"exehas_sort oss (Ty a Ts) S =
  (case lookup (\<lambda>k. k=a) (exetcsigs oss) of
  None \<Rightarrow> False |
  Some mgd \<Rightarrow> (\<forall>C \<in> S.
    case lookup (\<lambda>k. k=C) mgd of
        None \<Rightarrow> False
      | Some Ss \<Rightarrow> list_all2 (exehas_sort oss) Ts Ss))"

(* cleanup *)
lemma exehas_sort_imp_has_sort: 
  assumes "exe_osig_conds (sub, tcs)"
  shows "exehas_sort (sub, tcs) T S \<Longrightarrow> has_sort (translate_osig (sub, tcs)) T S"
proof (induction T arbitrary: S)
  case (Ty n Ts)
  obtain sub' tcs' where sub'_tcs': "translate_osig (sub, tcs) = (sub', tcs')" by fastforce
  obtain mgd where mgd: "tcs' n = Some mgd" 
    using Ty.prems sub'_tcs' apply (simp split: option.splits) 
    by (metis assms exe_ars_conds_def exe_osig_conds_def in_alist_imp_in_map_of lookup_eq_map_of_ap 
        map_of_SomeD snd_conv)
  show ?case
  proof (subst sub'_tcs', rule has_sort_Ty[of tcs', OF mgd], rule ballI)
    fix c assume asm: "c\<in>S"

    have l: "lookup (\<lambda>k. k=n) (map (apsnd map_of) tcs) = Some mgd"
      by (metis assms lookup_eq_map_of_ap mgd snd_conv sub'_tcs' translate_ars.simps translate_osig.simps)
    hence "\<exists>x. (lookup (\<lambda>k. k=n) tcs) = Some x"
      by (induction tcs) auto
    from this obtain pre_mgd where pre_mgd: "(lookup (\<lambda>k. k=n) tcs) = Some pre_mgd"
      by blast
    have pre_mgd_mgd: "map_of pre_mgd = mgd"
      by (metis l assms exe_ars_conds_def
          exe_osig_conds_def in_alist_imp_in_map_of lookup_eq_map_of_ap map_of_SomeD 
          option.sel pre_mgd snd_conv translate_ars.simps)

    obtain Ss where Ss: "lookup (\<lambda>k. k=c) pre_mgd = Some Ss"
      using Ty.prems asm by (auto simp add: pre_mgd split: option.splits)
    hence cond: "list_all2 (exehas_sort (sub,tcs)) Ts Ss"
      using \<open>exehas_sort (sub, tcs) (Ty n Ts) S\<close>asm pre_mgd by (auto split: option.splits)
      
    from Ss have "mgd c = Some Ss"
      by (simp add: lookup_eq_map_of_ap pre_mgd_mgd)
    then show "\<exists>Ss. mgd c = Some Ss \<and> list_all2 (has_sort (sub', tcs')) Ts Ss"
      using cond Ty.IH list.rel_mono_strong sub'_tcs' by force
  qed
next
  case (Tv n S)
  then show ?case
    by (metis assms exehas_sort.simps(1) exesort_les_code has_sort_Tv prod.collapse translate_osig.simps)
qed

lemma has_sort_imp_exehas_sort: 
  assumes "exe_osig_conds (sub, tcs)"
  shows "has_sort (translate_osig (sub, tcs)) T S \<Longrightarrow> exehas_sort (sub, tcs) T S"
proof (induction T arbitrary: S)
  case (Ty n Ts)
  obtain sub' tcs' where sub'_tcs': "translate_osig (sub, tcs) = (sub', tcs')" by fastforce
  obtain mgd where mgd: "tcs' n = Some mgd" 
    using Ty.prems sub'_tcs' has_sort.simps by (auto split: option.splits)
  hence "lookup (\<lambda>k. k=n) (map (apsnd map_of) tcs) = Some mgd"
    by (metis assms lookup_eq_map_of_ap prod.inject sub'_tcs' translate_ars.simps translate_osig.simps)
  have l: "lookup (\<lambda>k. k=n) (map (apsnd map_of) tcs) = Some mgd"
    by (metis assms lookup_eq_map_of_ap mgd snd_conv sub'_tcs' 
        translate_ars.simps translate_osig.simps)
  hence "\<exists>x. (lookup (\<lambda>k. k=n) tcs) = Some x"
    by (induction tcs) auto
  from this obtain pre_mgd where pre_mgd: "(lookup (\<lambda>k. k=n) tcs) = Some pre_mgd"
    by blast
  have pre_mgd_mgd: "map_of pre_mgd = mgd"
    by (metis l assms exe_ars_conds_def
        exe_osig_conds_def in_alist_imp_in_map_of lookup_eq_map_of_ap map_of_SomeD option.sel
        pre_mgd snd_conv translate_ars.simps)

  {
    fix c assume asm: "c\<in>S"
    
    obtain Ss where Ss: "lookup (\<lambda>k. k=c) pre_mgd = Some Ss"
      using \<open>c \<in> S\<close> \<open>map_of pre_mgd = mgd\<close> sub'_tcs' mgd assms Ty.prems has_sort.simps
      by (auto simp add: dom_map_of_conv_image_fst domIff eq_fst_iff exe_ars_conds_def 
          map_of_eq_None_iff classes_translate lookup_eq_map_of_ap split: typ.splits
          dest!: domD intro!: domI)
    have l: "length Ts = length Ss"
      using asm mgd pre_mgd Ty.prems assms sub'_tcs' Ss list_all2_lengthD pre_mgd_mgd
      by (fastforce simp add: has_sort.simps lookup_eq_map_of_ap)

    have 1: "\<forall>c \<in> S. \<exists>Ss . mgd c = Some Ss \<and> list_all2 (has_sort (sub', tcs')) Ts Ss"
      using mgd Ty.prems has_sort.simps sub'_tcs' by auto

    have cond: "list_all2 (exehas_sort (sub,tcs)) Ts Ss"
      apply (rule list_all2_all_nthI)
      using l apply simp
      subgoal premises p for m 
        apply (rule Ty.IH)
        using p apply simp
        using p Ty.prems assms 1
        by (metis Ss asm list_all2_conv_all_nth lookup_eq_map_of_ap option.sel pre_mgd_mgd sub'_tcs') 
      done
    have "(\<forall>C \<in> S.
    case lookup (\<lambda>k. k=C) pre_mgd of
        None \<Rightarrow> False
      | Some Ss \<Rightarrow> list_all2 (exehas_sort (sub,tcs)) Ts Ss)"
      by (metis "1" Ty.IH list_all2_conv_all_nth lookup_eq_map_of_ap nth_mem option.simps(5) 
        pre_mgd_mgd sub'_tcs')
  }

  then show ?case
    using pre_mgd by simp
next
  case (Tv n S)
  then show ?case
    using assms exesort_les_code has_sort_Tv_imp_sort_leq by fastforce
qed

lemma has_sort_code:
  assumes "exe_osig_conds oss"
  shows "has_sort (translate_osig oss) T S = exehas_sort oss T S"
  by (metis assms exehas_sort_imp_has_sort has_sort_imp_exehas_sort prod.collapse)

lemma has_sort_code':
  assumes "exe_wf_theory' \<Theta>"
  shows "has_sort (osig (sig (translate_theory \<Theta>))) T S 
    = exehas_sort (exesorts (exesig \<Theta>)) T S"
  apply (cases \<Theta> rule: exetheory_full_exhaust) using assms has_sort_code by auto

abbreviation "exeinst_ok \<Theta> insts \<equiv> 
    distinct (map fst insts)
  \<and> list_all (exetyp_ok \<Theta>) (map snd insts)
  \<and> list_all (\<lambda>((idn, S), T) . exehas_sort (exesorts (exesig \<Theta>)) T S) insts"

lemma inst_ok_code1:
  assumes "exe_wf_theory' \<Theta>"
  shows "list_all (exetyp_ok \<Theta>) (map snd insts) = list_all (typ_ok (translate_theory \<Theta>)) (map snd insts)"
  using assms typ_ok_code by (auto simp add: list_all_iff)

lemma inst_ok_code2:
  assumes "exe_wf_theory' \<Theta>"
  shows "list_all (\<lambda>((idn, S), T) . has_sort (osig (sig (translate_theory \<Theta>))) T S) insts
    = list_all (\<lambda>((idn, S), T) . exehas_sort (exesorts (exesig \<Theta>)) T S) insts"
  using has_sort_code' assms by auto

lemma inst_ok_code:
  assumes "exe_wf_theory' \<Theta>"
  shows "inst_ok (translate_theory \<Theta>) insts = exeinst_ok \<Theta> insts"
  using inst_ok_code1 inst_ok_code2 assms by auto

definition [simp]: "exeterm_ok \<Theta> t \<equiv> exeterm_ok' (exesig \<Theta>) t \<and> typ_of t \<noteq> None"
lemma term_ok_code:
  assumes "exe_wf_theory' \<Theta>"
  shows "term_ok (translate_theory \<Theta>) t = exeterm_ok \<Theta> t"
  using assms apply (cases \<Theta> rule: exetheory_full_exhaust) 
  by (metis exe_sig_conds_def exe_wf_theory'.simps exeterm_ok_def exetheory.sel(1) 
      sig.simps term_okD1 term_okD2 term_okI wt_term_code translate_theory.simps)

fun exereplay' :: "exetheory \<Rightarrow> (variable \<times> typ) list \<Rightarrow> variable set
  \<Rightarrow> term list \<Rightarrow> proofterm \<Rightarrow> term option" where
  "exereplay' thy _ _ Hs (PAxm t Tis) = (if exeinst_ok thy Tis \<and> exeterm_ok thy t
    then if t \<in> set (exeaxioms_of thy)
      then Some (forall_intro_vars (subst_typ' Tis t) []) 
    else None else None)"
| "exereplay' thy _ _ Hs (PBound n) = partial_nth Hs n" 
| "exereplay' thy vs ns Hs (Abst T p) = (if exetyp_ok thy T 
    then (let (s',ns') = variant_variable (Free STR ''default'') ns in 
      map_option (mk_all s' T) (exereplay' thy ((s', T) # vs) ns' Hs p))
    else None)"
| "exereplay' thy vs ns Hs (Appt p t) = 
    (let rep = exereplay' thy vs ns Hs p in
    let t' = subst_bvs (map (\<lambda>(x,y) . Fv x y) vs) t in
      case (rep, typ_of t') of
        (Some (Ct s (Ty fun1 [Ty fun2 [\<tau>, Ty propT1 Nil], Ty propT2 Nil]) $ b), Some \<tau>') \<Rightarrow> 
          if s = STR ''Pure.all'' \<and> fun1 = STR ''fun'' \<and> fun2 = STR ''fun'' 
            \<and> propT1 = STR ''prop'' \<and> propT2 = STR ''prop''
             \<and> \<tau>=\<tau>' \<and> exeterm_ok thy t'
            then Some (b \<bullet> t') else None
      | _ \<Rightarrow> None)" 
| "exereplay' thy vs ns Hs (AbsP t p) =
    (let t' = subst_bvs (map (\<lambda>(x,y) . Fv x y) vs) t in
    let rep = exereplay' thy vs ns (t'#Hs) p in
      (if typ_of t' = Some propT \<and> exeterm_ok thy t' then map_option (mk_imp t') rep else None))"
| "exereplay' thy vs ns Hs (AppP p1 p2) = 
    (let rep1 = Option.bind (exereplay' thy vs ns Hs p1) beta_eta_norm in
    let rep2 = Option.bind (exereplay' thy vs ns Hs p2) beta_eta_norm in
      (case (rep1, rep2) of (
        Some (Ct imp (Ty fn1 [Ty prp1 [], Ty fn2 [Ty prp2 [], Ty prp3 []]]) $ A $ B),
        Some A') \<Rightarrow> 
          if imp = STR ''Pure.imp'' \<and> fn1 = STR ''fun'' \<and> fn2 = STR ''fun''
            \<and> prp1 = STR ''prop'' \<and> prp2 = STR ''prop'' \<and> prp3 = STR ''prop'' \<and> A=A' 
          then Some B else None
        | _ \<Rightarrow> None))"
| "exereplay' thy vs ns Hs (OfClass ty c) = (if exehas_sort (exesorts (exesig thy)) ty {c} 
    \<and> exetyp_ok thy ty
    then (case lookup (\<lambda>k. k=const_of_class c) (execonst_type_of (exesig thy)) of 
      Some (Ty fun [Ty it [ity], Ty prop []]) \<Rightarrow> 
        if ity = tvariable STR '''a'' \<and> fun = STR ''fun'' \<and> prop = STR ''prop'' \<and> it = STR ''itself''
          then Some (mk_of_class ty c) else None | _ \<Rightarrow> None) else None)"
| "exereplay' thy vs ns Hs (Hyp t) = (if t\<in>set Hs then Some t else None)"

lemma of_class_code1: 
  assumes "exe_wf_theory' thy"
  shows "(has_sort (osig (sig (translate_theory thy))) ty {c} \<and> typ_ok (translate_theory thy) ty)
    = (exehas_sort (exesorts (exesig thy)) ty {c} \<and> exetyp_ok thy ty)"
proof-
  have "has_sort (osig (sig (translate_theory thy))) ty {c}
    = exehas_sort (exesorts (exesig thy)) ty {c}"
    using has_sort_code' assms by simp
  moreover have "typ_ok (translate_theory thy) ty = exetyp_ok thy ty"
    using typ_ok_code assms by simp
  ultimately show ?thesis 
    by auto
qed

lemma of_class_code2: 
  assumes "exe_wf_theory' thy"
  shows "const_type (sig (translate_theory thy)) (const_of_class c) 
    = lookup (\<lambda>k. k=const_of_class c) (execonst_type_of (exesig thy))"
  by (metis assms const_type_of_lookup_code exe_wf_theory_code 
      exe_wf_theory_translate_imp_wf_theory exetheory.sel(1) illformed_theory_not_wf_theory 
      sig.simps translate_theory.elims)

lemma replay'_code:
  assumes "exe_wf_theory' thy"
  shows "replay' (translate_theory thy) vs ns Hs P = exereplay' thy vs ns Hs P"
proof (induction P arbitrary: vs ns Hs)
  case (PAxm ax tys)
  have wf: "wf_theory (translate_theory thy)"
    by (simp add: assms exe_wf_theory_code exe_wf_theory_translate_imp_wf_theory)
  moreover have inst: "inst_ok (translate_theory thy) tys \<longleftrightarrow> exeinst_ok thy tys"
    by (simp add: assms inst_ok_code1 inst_ok_code2)
  moreover have tok: "term_ok (translate_theory thy) ax \<longleftrightarrow> exeterm_ok thy ax"
    using assms term_ok_code by blast
  moreover have ax: "ax \<in> axioms (translate_theory thy) \<longleftrightarrow> ax \<in> set (exeaxioms_of thy)"
    by (metis axioms.simps wf exetheory.sel(2) illformed_theory_not_wf_theory translate_theory.elims)
  ultimately show ?case
    by simp
qed (use assms term_ok_code typ_ok_code of_class_code1 of_class_code2 
      in \<open>auto simp only: replay'.simps exereplay'.simps split: if_splits\<close>)

abbreviation "exereplay'' thy vs ns Hs P \<equiv> Option.bind (exereplay' thy vs ns Hs P) beta_eta_norm"
lemma replay''_code:
  assumes "exe_wf_theory' thy"
  shows "replay'' (translate_theory thy) vs ns Hs P = exereplay'' thy vs ns Hs P"
  by (simp add: assms replay'_code)

definition [simp]: "exereplay thy P \<equiv> 
  (if \<forall>x\<in>set (hyps P) . exeterm_ok thy x \<and> typ_of x = Some propT then
  exereplay'' thy [] (fst ` (fv_Proof P \<union> FV (set (hyps P)))) (hyps P) P else None)"

lemma replay_code:
  assumes "exe_wf_theory' thy"
  shows "replay (translate_theory thy) P = exereplay thy P"
  using assms replay''_code term_ok_code by auto

definition "exe_replay' e P = exereplay'' e [] (fst ` fv_Proof P) [] P"

definition "exe_check_proof e P res \<equiv> 
  exe_wf_theory' e \<and> exereplay e P = Some res"

lemma exe_check_proof_iff_check_proof: 
  "exe_check_proof e P res \<longleftrightarrow> check_proof (translate_theory e) P res"
  using check_proof_def exe_check_proof_def wf_theory_translate_iff_exe_wf_theory 
  by (metis exe_wf_theory_code replay_code)

lemma check_proof_sound:
  shows "exe_check_proof e P res \<Longrightarrow> translate_theory e, set (hyps P) \<turnstile> res"
  by (simp add: check_proof_sound exe_check_proof_iff_check_proof)

lemma check_proof_really_sound:
  shows "exe_check_proof e P res \<Longrightarrow> translate_theory e, set (hyps P) \<tturnstile> res"
  by (simp add: check_proof_really_sound exe_check_proof_iff_check_proof)

end