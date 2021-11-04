
section "Proof Terms and proof checker"

theory ProofTerm
  imports Term Logic Term_Subst SortConstants EqualityProof
begin            

(* Move *)
type_synonym tyinst = "(variable \<times> sort) \<times> typ" 
type_synonym tinst = "(variable \<times> typ) \<times> term"

datatype proofterm = PAxm "term" "tyinst list" 
  | PBound nat
  | Abst "typ" proofterm 
  | AbsP "term" proofterm
  | Appt proofterm "term" 
  | AppP proofterm proofterm
  | OfClass "typ" "class"
  | Hyp "term"

(* For debbuging, move to code gen or seperate theory? *)
fun depth :: "proofterm \<Rightarrow> nat" where
  "depth (Abst _ P) = Suc (depth P)"
| "depth (AbsP _ P) = Suc (depth P)"
| "depth (Appt P _) = Suc (depth P)"
| "depth (AppP P1 P2) = Suc (max (depth P1) (depth P2))"
| "depth _ = 1"
fun size :: "proofterm \<Rightarrow> nat" where
  "size (Abst _ P) = Suc (size P)"
| "size (AbsP _ P) = Suc (size P)"
| "size (Appt P _) = Suc (size P)"
| "size (AppP P1 P2) = Suc (size P1 + size P2)"
| "size _ = 1"

lemma "depth P > 0"
  by (induction P) auto
lemma "size P > 0"
  by (induction P) auto
lemma "size P \<ge> depth P"
  by (induction P) auto

fun partial_nth :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" where
  "partial_nth [] _ = None"
| "partial_nth (x#xs) 0 = Some x"
| "partial_nth (x#xs) (Suc n) = partial_nth xs n"

definition [simp]: "partial_nth' xs n \<equiv> if n < length xs then Some (nth xs n) else None"

lemma "partial_nth xs n \<equiv> partial_nth' xs n"
  by (induction rule: partial_nth.induct) auto

lemma partial_nth_Some_imp_elem: "partial_nth l n = Some x \<Longrightarrow> x\<in>set l"
  by (induction rule: partial_nth.induct) auto 

text\<open>The core of the proof checker\<close>

fun replay' :: "theory \<Rightarrow> (variable \<times> typ) list \<Rightarrow> variable set 
  \<Rightarrow> term list \<Rightarrow> proofterm \<Rightarrow> term option" where
  "replay' thy _ _ Hs (PAxm t Tis) = (if inst_ok thy Tis \<and> term_ok thy t
    then if t \<in> axioms thy
      then Some (forall_intro_vars (subst_typ' Tis t) []) 
    else None else None)"
| "replay' thy _ _ Hs (PBound n) = partial_nth Hs n" 
| "replay' thy vs ns Hs (Abst T p) = (if typ_ok thy T 
    then (let (s',ns') = variant_variable (Free STR ''default'') ns in 
      map_option (mk_all s' T) (replay' thy ((s', T) # vs) ns' Hs p))
    else None)"
| "replay' thy vs ns Hs (Appt p t) = 
    (let rep = replay' thy vs ns Hs p in
    let t' = subst_bvs (map (\<lambda>(x,y) . Fv x y) vs) t in
      case (rep, typ_of t') of
        (Some (Ct s (Ty fun1 [Ty fun2 [\<tau>, Ty propT1 Nil], Ty propT2 Nil]) $ b), Some \<tau>') \<Rightarrow> 
          if s = STR ''Pure.all'' \<and> fun1 = STR ''fun'' \<and> fun2 = STR ''fun'' 
            \<and> propT1 = STR ''prop'' \<and> propT2 = STR ''prop''
             \<and> \<tau>=\<tau>' \<and> term_ok thy t'
            then Some (b \<bullet> t') else None
      | _ \<Rightarrow> None)" 
| "replay' thy vs ns Hs (AbsP t p) = 
    (let t' = subst_bvs (map (\<lambda>(x,y) . Fv x y) vs) t in
    let rep = replay' thy vs ns (t'#Hs) p in
      (if typ_of t' = Some propT \<and> term_ok thy t' then map_option (mk_imp t') rep else None))"
| "replay' thy vs ns Hs (AppP p1 p2) = 
    (let rep1 = Option.bind (replay' thy vs ns Hs p1) beta_eta_norm in
    let rep2 = Option.bind (replay' thy vs ns Hs p2) beta_eta_norm in
      (case (rep1, rep2) of (
        Some (Ct imp (Ty fn1 [Ty prp1 [], Ty fn2 [Ty prp2 [], Ty prp3 []]]) $ A $ B),
        Some A') \<Rightarrow> 
          if imp = STR ''Pure.imp'' \<and> fn1 = STR ''fun'' \<and> fn2 = STR ''fun''
            \<and> prp1 = STR ''prop'' \<and> prp2 = STR ''prop'' \<and> prp3 = STR ''prop'' \<and> A=A' 
          then Some B else None
        | _ \<Rightarrow> None))"
| "replay' thy vs ns Hs (OfClass ty c) = (if has_sort (osig (sig thy)) ty {c} 
    \<and> typ_ok thy ty
    then (case const_type (sig thy) (const_of_class c) of 
      Some (Ty fun [Ty it [ity], Ty prop []]) \<Rightarrow> 
        if ity = tvariable STR '''a'' \<and> fun = STR ''fun'' \<and> prop = STR ''prop'' \<and> it = STR ''itself''
          then Some (mk_of_class ty c) else None | _ \<Rightarrow> None) else None)"
| "replay' thy vs ns Hs (Hyp t) = (if t\<in>set Hs then Some t else None)"

lemma fv_subst_bv1: 
  "fv (subst_bv1 t lev u) = fv t \<union> (if loose_bvar1 t lev then fv u else {})"
  by (induction t lev u rule: subst_bv1.induct) (auto simp add: incr_boundvars_def)

(* Needs precondition, doable but diverges from previous checker*)
corollary fv_subst_bvs_upper_bound:
  assumes "is_closed t" 
  shows "fv (subst_bvs us t) \<subseteq> fv t \<union> (\<Union>x\<in>set us . (fv x))"
  unfolding subst_bvs_def
  using assms by (simp add: is_open_def no_loose_bvar_imp_no_subst_bvs1)

lemma fv_subst_bvs1_upper_bound: 
  "fv (subst_bvs1 t lev us) \<subseteq> fv t \<union> (\<Union>x\<in>set us . (fv x))"
proof (induction t lev us rule: subst_bvs1.induct)
  case (1 n lev args)
  then show ?case 
  proof (induction args arbitrary: n lev)
    case Nil
    then show ?case
      by simp
  next
    case (Cons a args)
    then show ?case
      by simp (metis SUP_upper le_supI1 le_supI2 length_Suc_conv nth_mem set_ConsD set_eq_subset)
  qed
qed (auto simp add: incr_boundvars_def)

lemma typ_of_axiom: "wf_theory thy \<Longrightarrow> t \<in> axioms thy \<Longrightarrow> typ_of t = Some propT" 
  by (cases thy rule: theory_full_exhaust) simp

fun fv_Proof :: "proofterm \<Rightarrow> (variable \<times> typ) set" where
  "fv_Proof (PAxm t _) = fv t"
| "fv_Proof (PBound _) = empty"
| "fv_Proof (Abst _ p) = fv_Proof p"
| "fv_Proof (AbsP t p) = fv t \<union> fv_Proof p"
| "fv_Proof (Appt p t) = fv_Proof p \<union> fv t"
| "fv_Proof (AppP p1 p2) = fv_Proof p1 \<union> fv_Proof p2"
| "fv_Proof (OfClass _ _) = empty"
| "fv_Proof (Hyp t) = fv t"

lemma typ_ok_Tv[simp]: "typ_ok thy (Tv idn S) = wf_sort (subclass (osig (sig thy))) S"
  by simp

lemma typ_ok_contained_tvars_typ_ok: "typ_ok thy ty \<Longrightarrow> (idn, S) \<in> tvsT ty \<Longrightarrow> typ_ok thy (Tv idn S)"
  by (induction ty) (use split_list typ_ok_Ty in \<open>all \<open>fastforce split: option.splits\<close>\<close>)

lemma typ_ok_sig_contained_tvars_typ_ok_sig: 
  "typ_ok_sig \<Sigma> ty \<Longrightarrow> (idn, S) \<in> tvsT ty \<Longrightarrow> typ_ok_sig \<Sigma> (Tv idn S)"
  by (induction ty) (use split_list typ_ok_sig_Ty in \<open>all \<open>fastforce split: option.splits\<close>\<close>)

lemma term_ok'_contained_tvars_typ_ok_sig:
  "term_ok' \<Sigma> t \<Longrightarrow> (idn, S) \<in> tvs t \<Longrightarrow> typ_ok_sig \<Sigma> (Tv idn S)"
  
proof (induction t)
  case (Ct n T)
  hence "typ_ok_sig \<Sigma> T" 
    by (auto split: option.splits)
  then show ?case 
    using typ_ok_sig_contained_tvars_typ_ok_sig Ct by auto
next
  case (Fv idn T)
  hence "typ_ok_sig \<Sigma> T"
    by (auto split: option.splits)
  then show ?case 
    using typ_ok_sig_contained_tvars_typ_ok_sig Fv by auto
next
  case (Bv n)
  then show ?case by auto
next
  case (Abs T t)
  hence "typ_ok_sig \<Sigma> T" 
    by (auto split: option.splits)
  then show ?case 
    using typ_ok_sig_contained_tvars_typ_ok_sig Abs by fastforce
next
  case (App t1 t2)
  then show ?case 
    by auto
qed 

lemma term_ok_contained_tvars_typ_ok:
  "term_ok thy t \<Longrightarrow> (idn, S) \<in> tvs t \<Longrightarrow> typ_ok thy (Tv idn S)"
  using wt_term_def typ_ok_def term_ok'_contained_tvars_typ_ok_sig term_ok_def by blast

lemma typ_ok_subst_typ:
  "typ_ok thy T \<Longrightarrow> \<forall>(_, ty) \<in> set insts . typ_ok thy ty \<Longrightarrow> typ_ok thy (subst_typ insts T)"
proof (induction insts T rule: subst_typ.induct)
  case (1 insts n Ts)
  have "typ_ok thy x" if "x\<in>set Ts" for x
    by (metis (full_types) "1.prems"(1) in_set_conv_decomp_first list_all_append list_all_simps(1)
      that typ_ok_Ty)
  hence "typ_ok thy (subst_typ insts x)" if "x\<in>set Ts" for x
    using that 1 by simp
  then show ?case 
    using "1.prems"(1) by (auto simp add: list_all_iff split: option.splits)
next
  case (2 insts idn S)
  then show ?case 
  proof(cases "(idn, S) \<in> set (map fst insts)")
    case True
    obtain ty where ty: "lookup (\<lambda>k. k=(idn,S)) insts = Some ty"
      by (metis (full_types) True lookup_None_iff not_Some_eq)
    hence "subst_typ insts (Tv idn S) = ty"
      by simp
    then show ?thesis 
      using "2.prems"(2) ty case_prodD lookup_present_eq_key' by fastforce
  next
    case False
    hence "subst_typ insts (Tv idn S) = Tv idn S"
      by (metis (mono_tags, lifting) lookup_None_iff subst_typ.simps(2) the_default.simps(1))
    then show ?thesis 
      using "2.prems"(1) by simp
  qed
qed

lemma typ_ok_sig_subst_typ:
  "typ_ok_sig \<Sigma> T \<Longrightarrow> \<forall>(_, ty) \<in> set insts . typ_ok_sig \<Sigma> ty \<Longrightarrow> typ_ok_sig \<Sigma> (subst_typ insts T)"
proof (induction insts T rule: subst_typ.induct)
  case (1 insts n Ts)
  have "typ_ok_sig \<Sigma> x" if "x\<in>set Ts" for x
    using "1.prems"(1) split_list that typ_ok_sig_Ty by fastforce
  hence "typ_ok_sig \<Sigma> (subst_typ insts x)" if "x\<in>set Ts" for x
    using that 1 by simp
  then show ?case 
    using "1.prems"(1) by (auto simp add: list_all_iff split: option.splits)
next
  case (2 insts idn S)
  then show ?case
  proof(cases "(idn, S) \<in> set (map fst insts)")
    case True
    obtain ty where ty: "lookup (\<lambda>k. k=(idn,S)) insts = Some ty"
      by (metis (full_types) True lookup_None_iff not_Some_eq)
    hence "subst_typ insts (Tv idn S) = ty"
      by simp
    then show ?thesis 
      using "2.prems"(2) ty case_prodD lookup_present_eq_key' by fastforce
  next
    case False
    hence "subst_typ insts (Tv idn S) = Tv idn S"
      by (metis (mono_tags, lifting) lookup_None_iff subst_typ.simps(2) the_default.simps(1))
    then show ?thesis 
      using "2.prems"(1) by simp
  qed
qed


lemma typ_ok_sig_imp_sortsT_ok_sig: "typ_ok_sig \<Sigma> T \<Longrightarrow> S \<in> SortsT T \<Longrightarrow> wf_sort (subclass (osig \<Sigma>)) S"
  by (induction T) (use split_list in \<open>all \<open>fastforce simp add: wf_sort_def split: option.splits\<close>\<close>)

lemma term_ok'_imp_Sorts_ok_sig: "term_ok' \<Sigma> t \<Longrightarrow> S \<in> Sorts t \<Longrightarrow> wf_sort (subclass (osig \<Sigma>)) S"
  by (induction t) (use typ_ok_sig_imp_sortsT_ok_sig in \<open>(fastforce split: option.splits)+\<close>)

lemma replay'_sound_pre:
  assumes thy: "wf_theory thy"
  (* Assumptions *)
  assumes HS_invs: 
    "\<And>x. x\<in>set Hs \<Longrightarrow> term_ok thy x"
    "\<And>x. x\<in>set Hs \<Longrightarrow> typ_of x = Some propT"
  (* Names used *)
  assumes ns_invs:
    "finite ns"
    "fst ` FV (set Hs) \<subseteq> ns"
    "fst ` fv_Proof P \<subseteq> ns"
  (* Fviables used *)
  assumes vs_invs:
    "fst ` set vs \<subseteq> ns"
  (* Checked proof can be replay'ed using proves*)
  assumes "replay' thy vs ns Hs P = Some res"
  shows "thy, (set Hs) \<turnstile> res"
using assms proof(induction thy vs ns Hs P arbitrary: res rule: replay'.induct)
  case (1 thy uu uv Hs t Tis)
  hence 
    ax: "t\<in>axioms thy"
    and insts: "inst_ok thy Tis" and t: "term_ok thy t"
    and res: "forall_intro_vars (subst_typ' Tis t) [] = res"
    by (auto split: if_splits)
  hence 1: "thy, {} \<turnstile> res"
    using res "1.prems"(1) proved_terms_well_formed_pre 
    using axiom forall_intro_vars inst_ok_imp_wf_inst tsubst_simulates_subst_typ' 
    by (metis (no_types, lifting) empty_set)
  show ?case 
    using weaken_proves_set[of "set Hs", OF _ 1]
    using "1.prems"(2) "1.prems"(3) by auto
next
  case (2 thy ux uy Hs n)
  hence "res \<in> set Hs" using partial_nth_Some_imp_elem by simp
  then show ?case using proves.assume 2 by (simp add: wt_term_def) 
next
  case (3 thy vs ns Hs T p)

  obtain s' ns' where names: "(s',ns') = variant_variable (Free STR ''default'') ns"
    by simp
  from this 3 obtain bres where bres: "replay' thy ((s', T) # vs) ns' Hs p = Some bres" 
    by (auto split: if_splits prod.splits) 
  have "ns' = insert s' ns" using variant_variable_adds names
    by (metis fst_conv snd_conv)
  have "s' \<notin> ns" using "3.prems" variant_variable_fresh names
    by (metis fst_conv)
  hence "s' \<notin> fst ` FV (set Hs)" using "3.prems" by blast
  hence free: "(s', T) \<notin> FV (set Hs)" by force

  have typ_ok: "wf_type (sig thy) T" 
      using names "3.prems" by (auto split: if_splits)
  have I:"thy, set Hs \<turnstile> bres"
    apply (rule "3.IH"[OF _ names])  
    using names "3.prems" apply (solves \<open>simp split: if_splits\<close>)+
    using names "3.prems" \<open>ns' = insert s' ns\<close> apply fastforce
    using "3.prems"(7) \<open>ns' = insert s' ns\<close> apply auto[1]
    using "3.prems"(8) \<open>ns' = insert s' ns\<close> apply auto[1]
    using "3.prems"(6) apply fastforce
    using "3.prems"(7) \<open>ns' = insert s' ns\<close> apply auto[1]
    using "3.prems"(8) \<open>ns' = insert s' ns\<close> apply auto[1]
    using bres by fastforce
  have res: "res = mk_all s' T bres" using names bres 3 by (auto split: if_splits prod.splits)
  show ?case using proves.forall_intro[OF \<open>wf_theory thy\<close> I free typ_ok] res by simp  
next
  case (4 thy vs ns Hs p t)
  from \<open>replay' thy vs ns Hs (Appt p t) = Some res\<close> obtain rep t' b s fun1 fun2 propT1 propT2 \<tau> \<tau>' where 
    conds: "replay' thy vs ns Hs p = Some rep"
    "t' = subst_bvs (map (\<lambda>(x,y) . Fv x y) vs) t"
    "typ_of t' = Some \<tau>'"
    "\<tau> = \<tau>'"
    "term_ok thy t'"
    "s= STR ''Pure.all'' \<and> fun1 = STR ''fun'' \<and> fun2 = STR ''fun'' \<and> propT1 = STR ''prop'' \<and> propT2 = STR ''prop''"
    "rep = Ct s (Ty fun1 [Ty fun2 [\<tau>, Ty propT1 Nil], Ty propT2 Nil]) $ b"
    and res: "res = (b \<bullet> t')"
    (* Takes forever, split up  *)
    by (auto split: term.splits typ.splits list.splits if_splits option.splits simp add: Let_def)

  
  have ctxt: "finite (set Hs)" "\<forall>A \<in> set Hs . term_ok thy A" "\<forall>A \<in> set Hs . typ_of A = Some propT"
    using 4 by auto

  show ?case
    using conds "4.prems" ctxt 
    by (auto simp add: res wt_term_def simp del: FV_def 
        intro!: forall_elim'[OF "4.prems"(1) _ _ _ ctxt] "4.IH")
next
  case (5 thy vs ns Hs t p)
  from this obtain t' rep where
    conds: "subst_bvs (map (\<lambda>(x,y) . Fv x y) vs) t = t'"
    "replay' thy vs ns (t'#Hs) p = Some rep"
    "typ_of t' = Some propT" "term_ok thy t'"
    and res: "res = mk_imp t' rep"
    by (auto split: term.splits typ.splits list.splits if_splits option.splits simp add: Let_def)
    
    show ?case
    proof (cases "t'\<in> set Hs")
      case True
      hence s: "set Hs = set (t' # Hs)" by auto
      hence s': "set Hs = insert t' (set Hs -{t'})" by auto

      have "thy,set (t' # Hs) \<turnstile> rep"
        apply (rule "5.IH")
        using conds(4) "5.prems" True by (auto simp add: conds(1) conds(2)[symmetric] conds(3))
      hence "thy,set Hs - {t'} \<turnstile> t' \<longmapsto> rep"
        using implies_intro "5.prems"(1) "5.prems"(4) conds(3) conds(4) s
        using has_typ_iff_typ_of term_ok'_imp_wf_term term_okD1 by presburger
      then show ?thesis 
        apply (subst res)
        apply (subst s') 
        apply (rule weaken_proves)
        using conds(3-4) by blast+
  next
    case False
    hence s: "set Hs = insert t' (set Hs) - {t'}" by auto

    have "FV (set (map (\<lambda>(x,y) . Fv x y) vs)) = set vs" by (induction vs) auto
    hence frees_bound: "fv t' \<subseteq> fv t \<union> set vs"
      using fv_subst_bvs1_upper_bound subst_bvs_def by (fastforce simp add: conds(1)[symmetric]) 

    have pre: "thy,set (t' # Hs) \<turnstile> rep"
      apply (rule "5.IH")
      using "5.prems"(5-8) conds(3-4) frees_bound 
      by (auto simp add: "5.prems"(1-4) conds(1) conds(2) image_subset_iff simp del: term_ok_def)
      
    show ?thesis
      apply (subst res) apply (subst s)
      apply (rule proves.implies_intro; use 5 conds in \<open>(solves \<open>simp add: wt_term_def\<close>)?\<close>)
      using pre by simp
  qed
next
  case (6 thy vs ns Hs p1 p2)
  from \<open>replay' thy vs ns Hs (AppP p1 p2) = Some res\<close> obtain fn1 fn2 prp1 prp2 prp3 A B A' imp
    where 
    conds: "Option.bind (replay' thy vs ns Hs p1) beta_eta_norm
      = Some (Ct imp (Ty fn1 [Ty prp1 [], Ty fn2 [Ty prp2 [], Ty prp3 []]]) $ A $ B)" 
    "Option.bind (replay' thy vs ns Hs p2) beta_eta_norm = Some A'" 
    "imp = STR ''Pure.imp'' \<and> fn1 = STR ''fun'' \<and> fn2 = STR ''fun''
      \<and> prp1 = STR ''prop'' \<and> prp2 = STR ''prop'' \<and> prp3 = STR ''prop'' \<and> A=A'"
    and res: "res = B"
    by (auto split: term.splits typ.splits list.splits if_splits option.splits simp add: Let_def)

  obtain C where C: "Option.bind (replay' thy vs ns Hs p1) beta_eta_norm = Some (C \<longmapsto> res)"
    using conds res by blast
  from this obtain pre pre_C where pre: "replay' thy vs ns Hs p1 = Some pre" 
    and pre_C: "replay' thy vs ns Hs p2 = Some pre_C"
    by (meson bind_eq_Some_conv conds(2))

  from pre C have norm_pre: "beta_eta_norm pre = Some (C \<longmapsto> res)" by simp
  from pre_C pre C conds have norm_pre_C: "beta_eta_norm pre_C = Some C" by auto

  have "thy, set Hs \<turnstile> pre_C" 
    by (rule "6.IH"(2)) (use "6.prems" conds in \<open>auto simp add: pre pre_C\<close>)
  hence I1: "thy, set Hs \<turnstile> C"
    using beta_eta_norm_preserves_proves norm_pre_C \<open>wf_theory thy\<close> 
    using "6.prems"(2) "6.prems"(3) by blast
  
  have "thy, set Hs \<turnstile> pre"
    by (rule "6.IH"(1)) (use "6.prems" conds in \<open>auto simp add: pre pre_C\<close>)
  hence I2: "thy, set Hs \<turnstile> C \<longmapsto> res"
    using beta_eta_norm_preserves_proves norm_pre \<open>wf_theory thy\<close> 
    using "6.prems"(2) "6.prems"(3) by blast

  from I1 I2 have "thy, set Hs \<union> set Hs \<turnstile> res" using proves.implies_elim by blast
  thus ?case by simp
next
  case (7 thy vs ns Hs ty c)
  from this obtain "fun" it ity "prop"  where conds: "has_sort (osig (sig thy)) ty {c}" 
    "typ_ok thy ty" "const_type (sig thy) (const_of_class c) 
      = Some (Ty fun [Ty it [ity], Ty prop []])" "ity = tvariable STR '''a''"
     "fun = STR ''fun''" "prop = STR ''prop''" "it = STR ''itself''" 
    and res: "res = (mk_of_class ty c)"
    by (auto split: term.splits typ.splits list.splits if_splits option.splits)

  from res have "res = mk_of_class ty c" by auto
  moreover have "thy,set Hs \<turnstile> mk_of_class ty c"
    by (rule proves.of_class[where T=ty, OF "7.prems"(1)]) (use conds in auto)

  ultimately show ?case by simp
next
  case (8 thy ux uy Hs n)
  hence "res \<in> set Hs"
    by (metis not_None_eq option.inject replay'.simps(8))
  then show ?case using proves.assume 8 by (simp add: wt_term_def) 
qed

lemma finite_fv_Proof: "finite (fv_Proof P)"
  by (induction P) auto

abbreviation "replay'' thy vs ns Hs P \<equiv> Option.bind (replay' thy vs ns Hs P) beta_eta_norm"

lemma replay''_sound:
  assumes "wf_theory thy"
  (* Assumptions *)
  assumes HS_invs: 
    "\<And>x. x\<in>set Hs \<Longrightarrow> term_ok thy x"
    "\<And>x. x\<in>set Hs \<Longrightarrow> typ_of x = Some propT" 
  (* Names used *)
  assumes ns_invs:
    "finite ns"
    "fst ` FV (set Hs) \<subseteq> ns"
    "fst ` fv_Proof P \<subseteq> ns"
  (* Fviables used *)
  assumes vs_invs:
    "fst ` set vs \<subseteq> ns"
  (* Checked proof can be replayed using proves*)
  assumes "replay'' thy vs ns Hs P = Some res"
  shows "thy, (set Hs) \<turnstile> res"
proof-
  obtain res' where res': "replay' thy vs ns Hs P = Some res'" 
    using replay'_sound_pre assms bind_eq_Some_conv by metis
  moreover have "beta_eta_norm res' = Some res"
    using res' assms(8) by auto
  moreover have "thy, set Hs \<turnstile> res'"
    using res' assms replay'_sound_pre  by simp
  ultimately show ?thesis
    using beta_eta_norm_preserves_proves assms(1-3) by blast
qed

lemma 
  assumes "wf_theory thy"
  assumes "replay'' thy [] (fst ` fv_Proof P) [] P = Some res"
  shows "thy, set [] \<turnstile> res"
  using assms finite_fv_Proof replay'_sound_pre replay''_sound[where vs="[]" 
      and ns="fst ` fv_Proof P" and P=P and Hs="[]"]
  by simp

(* With open hyps, run  *)

fun hyps :: "proofterm \<Rightarrow> term list" where
  "hyps (Abst _ p) = hyps p"
| "hyps (AbsP _ p) = hyps p"
| "hyps (Appt p _) = hyps p"
| "hyps (AppP p1 p2) = List.union (hyps p1) (hyps p2)"
| "hyps (Hyp t) = [t]"
| "hyps _ = []"

lemma replay''_sound_pre_hyps:
  assumes "wf_theory thy"
  (* This can be checked independently before running replay'. Could also check during replay' in Hyp step... *)
  assumes "\<And>x. x \<in> set (hyps P) \<Longrightarrow> term_ok thy x"
  assumes "\<And>x. x \<in> set (hyps P) \<Longrightarrow> typ_of x = Some propT"
  assumes "replay'' thy [] (fst ` (fv_Proof P \<union> FV (set (hyps P)))) (hyps P) P = Some res"
  shows "thy, set (hyps P) \<turnstile> res"
  apply (rule replay''_sound[where vs="[]" and ns="(fst ` (fv_Proof P \<union> FV (set (hyps P))))" and P=P and Hs="hyps P"]
  ; (use assms finite_fv_Proof replay'_sound_pre in \<open>solves simp\<close>)?)
  by blast+

definition [simp]: "replay thy P \<equiv> 
  (if \<forall>x\<in>set (hyps P) . term_ok thy x \<and> typ_of x = Some propT then
  replay'' thy [] (fst ` (fv_Proof P \<union> FV (set (hyps P)))) (hyps P) P else None)"

lemma replay_sound_pre_hyps:
  assumes "wf_theory thy"
  assumes "replay thy P = Some res"
  shows "thy, set (hyps P) \<turnstile> res"
  using replay''_sound_pre_hyps assms by (simp split: if_splits)

definition "check_proof thy P res \<equiv> wf_theory thy \<and> replay thy P = Some res"

lemma check_proof_sound:
  shows "check_proof thy P res \<Longrightarrow> thy, set (hyps P) \<turnstile> res"
  using check_proof_def replay_sound_pre_hyps by blast

lemma check_proof_really_sound:
  assumes "check_proof thy P res"
  shows "thy, set (hyps P) \<tturnstile> res"
proof-
  have "wf_theory thy"
    using assms check_proof_def by blast
  moreover have "Some res = replay thy P"
    by (metis assms check_proof_def)
  moreover hence "\<forall>x\<in>set (hyps P) . term_ok thy x \<and> typ_of x = Some propT"
    by (metis not_None_eq replay_def)
  ultimately show ?thesis
    by (meson assms check_proof_sound has_typ_iff_typ_of proved_terms_well_formed(1) proves'_def 
        term_ok_def wt_term_def)
qed
  
end