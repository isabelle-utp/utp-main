chapter \<open>Predicates for Terms, Formulas and Substitution\<close>

theory Coding_Predicates
imports Coding Sigma
begin

declare succ_iff [simp del]

text \<open>This material comes from Section 3, greatly modified for de Bruijn syntax.\<close>

section \<open>Predicates for atomic terms\<close>

subsection \<open>Free Variables\<close>

definition VarP :: "tm \<Rightarrow> fm" where "VarP x \<equiv> OrdP x AND Zero IN x"

lemma VarP_eqvt [eqvt]: "(p \<bullet> VarP x) = VarP (p \<bullet> x)"
  by (simp add: VarP_def)

lemma VarP_fresh_iff [simp]: "a \<sharp> VarP x \<longleftrightarrow> a \<sharp> x"
  by (simp add: VarP_def)

lemma VarP_sf [iff]: "Sigma_fm (VarP x)"
  by (auto simp: VarP_def)

lemma VarP_subst [simp]: "(VarP x)(i::=t) = VarP (subst i t x) "
  by (simp add: VarP_def)

lemma VarP_cong: "H \<turnstile> x EQ x' \<Longrightarrow> H \<turnstile> VarP x IFF VarP x'"
  by (rule P1_cong) auto

lemma VarP_HPairE [intro!]: "insert (VarP (HPair x y)) H \<turnstile> A"
  by (auto simp: VarP_def)

subsection \<open>De Bruijn Indexes\<close>

abbreviation Q_Ind :: "tm \<Rightarrow> tm"
  where "Q_Ind k \<equiv> HPair (HTuple 6) k"

nominal_function IndP :: "tm \<Rightarrow> fm"
  where "atom m \<sharp> x \<Longrightarrow>
    IndP x = Ex m (OrdP (Var m) AND x EQ HPair (HTuple 6) (Var m))"
  by (auto simp: eqvt_def IndP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows IndP_fresh_iff [simp]: "a \<sharp> IndP x \<longleftrightarrow> a \<sharp> x"                (is ?thesis1)
    and IndP_sf [iff]:         "Sigma_fm (IndP x)"                   (is ?thsf)
    and OrdP_IndP_Q_Ind:       "{OrdP x} \<turnstile> IndP (Q_Ind x)"           (is ?thqind)
proof -
  obtain m::name where "atom m \<sharp> x"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf ?thqind
    by (auto intro: Ex_I [where x=x])
qed

lemma IndP_Q_Ind: "H \<turnstile> OrdP x \<Longrightarrow> H \<turnstile> IndP (Q_Ind x)"
  by (rule cut1 [OF OrdP_IndP_Q_Ind])

lemma subst_fm_IndP [simp]: "(IndP t)(i::=x) = IndP (subst i x t)"
proof -
  obtain m::name where "atom m \<sharp> (i,t,x)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: IndP.simps [of m])
qed

lemma IndP_cong: "H \<turnstile> x EQ x' \<Longrightarrow> H \<turnstile> IndP x IFF IndP x'"
  by (rule P1_cong) auto

subsection \<open>Various syntactic lemmas\<close>

section \<open>The predicate \<open>SeqCTermP\<close>, for Terms and Constants\<close>

(*SeqCTerm(s,k,t) \<equiv> LstSeq(s,k,t) \<and> (\<forall>l\<in>k)[s l=0 \<or> Var(s l)\<or>(\<exists>m,n\<in>l)[s l = \<langle>Eats, s m, s n\<rangle>]]*)
nominal_function SeqCTermP :: "bool \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom l \<sharp> (s,k,sl,m,n,sm,sn);  atom sl \<sharp> (s,m,n,sm,sn);
          atom m \<sharp> (s,n,sm,sn);  atom n \<sharp> (s,sm,sn);
          atom sm \<sharp> (s,sn);  atom sn \<sharp> (s)\<rbrakk> \<Longrightarrow>
    SeqCTermP vf s k t =
      LstSeqP s k t AND
      All2 l (SUCC k) (Ex sl (HPair (Var l) (Var sl) IN s AND
               (Var sl EQ Zero OR (if vf then VarP (Var sl) else Fls) OR
                Ex m (Ex n (Ex sm (Ex sn (Var m IN Var l AND Var n IN Var l AND
                       HPair (Var m) (Var sm) IN s AND HPair (Var n) (Var sn) IN s AND
                       Var sl EQ Q_Eats (Var sm) (Var sn))))))))"
  by (auto simp: eqvt_def SeqCTermP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows SeqCTermP_fresh_iff [simp]:
       "a \<sharp> SeqCTermP vf s k t \<longleftrightarrow> a \<sharp> s \<and> a \<sharp> k \<and> a \<sharp> t"  (is ?thesis1)
    and SeqCTermP_sf [iff]:
       "Sigma_fm (SeqCTermP vf s k t)"   (is ?thsf)
    and SeqCTermP_imp_LstSeqP:
      "{ SeqCTermP vf s k t } \<turnstile> LstSeqP s k t"  (is ?thlstseq)
    and SeqCTermP_imp_OrdP [simp]:
      "{ SeqCTermP vf s k t } \<turnstile> OrdP k"  (is ?thord)
proof -
  obtain l::name and sl::name and m::name and n::name and sm::name and sn::name
    where atoms: "atom l \<sharp> (s,k,sl,m,n,sm,sn)"   "atom sl \<sharp> (s,m,n,sm,sn)"
        "atom m \<sharp> (s,n,sm,sn)"   "atom n \<sharp> (s,sm,sn)"
        "atom sm \<sharp> (s,sn)"   "atom sn \<sharp> (s)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf ?thlstseq ?thord
    by (auto simp: LstSeqP.simps)
qed

lemma SeqCTermP_subst [simp]:
      "(SeqCTermP vf s k t)(j::=w) = SeqCTermP vf (subst j w s) (subst j w k) (subst j w t)"
proof -
  obtain l::name and sl::name and m::name and n::name and sm::name and sn::name
    where "atom l \<sharp> (j,w,s,k,sl,m,n,sm,sn)"   "atom sl \<sharp> (j,w,s,m,n,sm,sn)"
          "atom m \<sharp> (j,w,s,n,sm,sn)"   "atom n \<sharp> (j,w,s,sm,sn)"
          "atom sm \<sharp> (j,w,s,sn)"   "atom sn \<sharp> (j,w,s)"
    by (metis obtain_fresh)
  thus ?thesis
    by (force simp add: SeqCTermP.simps [of l _ _ sl m n sm sn])
qed

declare SeqCTermP.simps [simp del]

abbreviation SeqTermP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "SeqTermP \<equiv> SeqCTermP True"

abbreviation SeqConstP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "SeqConstP \<equiv> SeqCTermP False"

lemma SeqConstP_imp_SeqTermP: "{SeqConstP s k t} \<turnstile> SeqTermP s k t"
proof -
  obtain l::name and sl::name and m::name and n::name and sm::name and sn::name
    where "atom l \<sharp> (s,k,t,sl,m,n,sm,sn)"   "atom sl \<sharp> (s,k,t,m,n,sm,sn)"
          "atom m \<sharp> (s,k,t,n,sm,sn)"   "atom n \<sharp> (s,k,t,sm,sn)"
          "atom sm \<sharp> (s,k,t,sn)"   "atom sn \<sharp> (s,k,t)"
    by (metis obtain_fresh)
  thus ?thesis
    apply (auto simp: SeqCTermP.simps [of l s k sl m n sm sn])
    apply (rule Ex_I [where x="Var l"], auto)
    apply (rule Ex_I [where x = "Var sl"], force intro: Disj_I1)
    apply (rule Ex_I [where x = "Var sl"], simp)
    apply (rule Conj_I, blast)
    apply (rule Disj_I2)+
    apply (rule Ex_I [where x = "Var m"], simp)
    apply (rule Ex_I [where x = "Var n"], simp)
    apply (rule Ex_I [where x = "Var sm"], simp)
    apply (rule Ex_I [where x = "Var sn"], auto)
    done
qed


section \<open>The predicates \<open>TermP\<close> and \<open>ConstP\<close>\<close>

subsection \<open>Definition\<close>

nominal_function CTermP :: "bool \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom k \<sharp> (s,t); atom s \<sharp> t\<rbrakk> \<Longrightarrow>
    CTermP vf t = Ex s (Ex k (SeqCTermP vf (Var s) (Var k) t))"
  by (auto simp: eqvt_def CTermP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows CTermP_fresh_iff [simp]: "a \<sharp> CTermP vf t \<longleftrightarrow> a \<sharp> t"            (is ?thesis1)
    and CTermP_sf [iff]: "Sigma_fm (CTermP vf t)"                      (is ?thsf)
proof -
  obtain k::name and s::name  where "atom k \<sharp> (s,t)" "atom s \<sharp> t"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf
    by auto
qed

lemma CTermP_subst [simp]: "(CTermP vf i)(j::=w) = CTermP vf (subst j w i)"
proof -
  obtain k::name and s::name  where "atom k \<sharp> (s,i,j,w)" "atom s \<sharp> (i,j,w)"
    by (metis obtain_fresh)
  thus ?thesis
    by (simp add: CTermP.simps [of k s])
qed

abbreviation TermP :: "tm \<Rightarrow> fm"
  where "TermP \<equiv> CTermP True"

abbreviation ConstP :: "tm \<Rightarrow> fm"
  where "ConstP \<equiv> CTermP False"

subsection \<open>Correctness properties for constants\<close>

lemma ConstP_imp_TermP: "{ConstP t} \<turnstile> TermP t"
proof -
  obtain k::name and s::name  where "atom k \<sharp> (s,t)" "atom s \<sharp> t"
    by (metis obtain_fresh)
  thus ?thesis
    apply auto
    apply (rule Ex_I [where x = "Var s"], simp)
    apply (rule Ex_I [where x = "Var k"], auto intro: SeqConstP_imp_SeqTermP [THEN cut1])
    done
qed


section \<open>Abstraction over terms\<close>

nominal_function SeqStTermP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom l \<sharp> (s,k,v,i,sl,sl',m,n,sm,sm',sn,sn');
          atom sl \<sharp> (s,v,i,sl',m,n,sm,sm',sn,sn'); atom sl' \<sharp> (s,v,i,m,n,sm,sm',sn,sn');
          atom m \<sharp> (s,n,sm,sm',sn,sn'); atom n \<sharp> (s,sm,sm',sn,sn');
          atom sm \<sharp> (s,sm',sn,sn'); atom sm' \<sharp> (s,sn,sn');
          atom sn \<sharp> (s,sn'); atom sn' \<sharp> s\<rbrakk> \<Longrightarrow>
    SeqStTermP v i t u s k =
      VarP v AND LstSeqP s k (HPair t u) AND
      All2 l (SUCC k) (Ex sl (Ex sl' (HPair (Var l) (HPair (Var sl) (Var sl')) IN s AND
                (((Var sl EQ v AND Var sl' EQ i) OR
                  ((IndP (Var sl) OR Var sl NEQ v) AND Var sl' EQ Var sl)) OR
                Ex m (Ex n (Ex sm (Ex sm' (Ex sn (Ex sn' (Var m IN Var l AND Var n IN Var l AND
                       HPair (Var m) (HPair (Var sm) (Var sm')) IN s AND
                       HPair (Var n) (HPair (Var sn) (Var sn')) IN s AND
                       Var sl EQ Q_Eats (Var sm) (Var sn) AND
                       Var sl' EQ Q_Eats (Var sm') (Var sn')))))))))))"
  apply (simp_all add: eqvt_def SeqStTermP_graph_aux_def flip_fresh_fresh)
  by auto (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows SeqStTermP_fresh_iff [simp]:
      "a \<sharp> SeqStTermP v i t u s k \<longleftrightarrow> a \<sharp> v \<and> a \<sharp> i \<and> a \<sharp> t \<and> a \<sharp> u \<and> a \<sharp> s \<and> a \<sharp> k"  (is ?thesis1)
    and SeqStTermP_sf [iff]:
      "Sigma_fm (SeqStTermP v i t u s k)"  (is ?thsf)
    and SeqStTermP_imp_OrdP:
      "{ SeqStTermP v i t u s k } \<turnstile> OrdP k"  (is ?thord)
    and SeqStTermP_imp_VarP:
      "{ SeqStTermP v i t u s k } \<turnstile> VarP v"  (is ?thvar)
    and SeqStTermP_imp_LstSeqP:
      "{ SeqStTermP v i t u s k } \<turnstile> LstSeqP s k (HPair t u)"  (is ?thlstseq)
proof -
  obtain l::name and sl::name and sl'::name and m::name and n::name and
         sm::name and sm'::name and sn::name and sn'::name
    where atoms:
       "atom l \<sharp> (s,k,v,i,sl,sl',m,n,sm,sm',sn,sn')"
       "atom sl \<sharp> (s,v,i,sl',m,n,sm,sm',sn,sn')" "atom sl' \<sharp> (s,v,i,m,n,sm,sm',sn,sn')"
       "atom m \<sharp> (s,n,sm,sm',sn,sn')" "atom n \<sharp> (s,sm,sm',sn,sn')"
       "atom sm \<sharp> (s,sm',sn,sn')" "atom sm' \<sharp> (s,sn,sn')"
       "atom sn \<sharp> (s,sn')" "atom sn' \<sharp> (s)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf ?thord ?thvar ?thlstseq
    by (auto intro: LstSeqP_OrdP)
qed

lemma SeqStTermP_subst [simp]:
      "(SeqStTermP v i t u s k)(j::=w) =
       SeqStTermP (subst j w v) (subst j w i) (subst j w t) (subst j w u) (subst j w s) (subst j w k)"
proof -
  obtain l::name and sl::name and sl'::name and m::name and n::name and
         sm::name and sm'::name and sn::name and sn'::name
    where "atom l \<sharp> (s,k,v,i,w,j,sl,sl',m,n,sm,sm',sn,sn')"
         "atom sl \<sharp> (s,v,i,w,j,sl',m,n,sm,sm',sn,sn')"
         "atom sl' \<sharp> (s,v,i,w,j,m,n,sm,sm',sn,sn')"
         "atom m \<sharp> (s,w,j,n,sm,sm',sn,sn')" "atom n \<sharp> (s,w,j,sm,sm',sn,sn')"
         "atom sm \<sharp> (s,w,j,sm',sn,sn')" "atom sm' \<sharp> (s,w,j,sn,sn')"
         "atom sn \<sharp> (s,w,j,sn')" "atom sn' \<sharp> (s,w,j)"
    by (metis obtain_fresh)
  thus ?thesis
    by (force simp add: SeqStTermP.simps [of l _ _ _ _ sl sl' m n sm sm' sn sn'])
qed

lemma SeqStTermP_cong:
  "\<lbrakk>H \<turnstile> t EQ t'; H \<turnstile> u EQ u'; H \<turnstile> s EQ s'; H \<turnstile> k EQ k'\<rbrakk>
   \<Longrightarrow> H \<turnstile> SeqStTermP v i t u s k IFF SeqStTermP v i t' u' s' k'"
   by (rule P4_cong [where tms="[v,i]"]) (auto simp: fresh_Cons)

declare SeqStTermP.simps [simp del]

subsection \<open>Defining the syntax: main predicate\<close>

nominal_function AbstTermP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom s \<sharp> (v,i,t,u,k); atom k \<sharp> (v,i,t,u)\<rbrakk> \<Longrightarrow>
    AbstTermP v i t u =
     OrdP i AND Ex s (Ex k (SeqStTermP v (Q_Ind i) t u (Var s) (Var k)))"
  by (auto simp: eqvt_def AbstTermP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows AbstTermP_fresh_iff [simp]:
      "a \<sharp> AbstTermP v i t u \<longleftrightarrow> a \<sharp> v \<and> a \<sharp> i \<and> a \<sharp> t \<and> a \<sharp> u"  (is ?thesis1)
    and AbstTermP_sf [iff]:
      "Sigma_fm (AbstTermP v i t u)"  (is ?thsf)
    and AbstTermP_imp_VarP:
       "{ AbstTermP v i t u } \<turnstile> VarP v"   (is ?thvar)
    and AbstTermP_imp_OrdP:
       "{ AbstTermP v i t u } \<turnstile> OrdP i"   (is ?thord)
proof -
  obtain s::name and k::name where "atom s \<sharp> (v,i,t,u,k)"  "atom k \<sharp> (v,i,t,u)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf ?thvar ?thord
    by (auto intro: SeqStTermP_imp_VarP thin2)
qed

lemma AbstTermP_subst [simp]:
      "(AbstTermP v i t u)(j::=w) = AbstTermP (subst j w v) (subst j w i) (subst j w t) (subst j w u)"
proof -
  obtain s::name and k::name  where "atom s \<sharp> (v,i,t,u,w,j,k)"  "atom k \<sharp> (v,i,t,u,w,j)"
    by (metis obtain_fresh)
  thus ?thesis
    by (simp add: AbstTermP.simps [of s _ _ _ _ k])
qed

declare AbstTermP.simps [simp del]

section \<open>Substitution over terms\<close>

subsection \<open>Defining the syntax\<close>

nominal_function SubstTermP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom s \<sharp> (v,i,t,u,k); atom k \<sharp> (v,i,t,u)\<rbrakk> \<Longrightarrow>
    SubstTermP v i t u = TermP i AND Ex s (Ex k (SeqStTermP v i t u (Var s) (Var k)))"
  by (auto simp: eqvt_def SubstTermP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows SubstTermP_fresh_iff [simp]:
       "a \<sharp> SubstTermP v i t u \<longleftrightarrow> a \<sharp> v \<and> a \<sharp> i \<and> a \<sharp> t \<and> a \<sharp> u"  (is ?thesis1)
    and SubstTermP_sf [iff]:
       "Sigma_fm (SubstTermP v i t u)"     (is ?thsf)
    and SubstTermP_imp_TermP:
       "{ SubstTermP v i t u } \<turnstile> TermP i"  (is ?thterm)
    and SubstTermP_imp_VarP:
       "{ SubstTermP v i t u } \<turnstile> VarP v"   (is ?thvar)
proof -
  obtain s::name and k::name  where "atom s \<sharp> (v,i,t,u,k)" "atom k \<sharp> (v,i,t,u)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf ?thterm ?thvar
    by (auto intro: SeqStTermP_imp_VarP thin2)
qed

lemma SubstTermP_subst [simp]:
      "(SubstTermP v i t u)(j::=w) = SubstTermP (subst j w v) (subst j w i) (subst j w t) (subst j w u)"
proof -
  obtain s::name and k::name
    where "atom s \<sharp> (v,i,t,u,w,j,k)"  "atom k \<sharp> (v,i,t,u,w,j)"
    by (metis obtain_fresh)
  thus ?thesis
    by (simp add: SubstTermP.simps [of s _ _ _ _ k])
qed

lemma SubstTermP_cong:
  "\<lbrakk>H \<turnstile> v EQ v'; H \<turnstile> i EQ i'; H \<turnstile> t EQ t'; H \<turnstile> u EQ u'\<rbrakk>
   \<Longrightarrow> H \<turnstile> SubstTermP v i t u IFF SubstTermP v' i' t' u'"
  by (rule P4_cong) auto

declare SubstTermP.simps [simp del]

section \<open>Abstraction over formulas\<close>

subsection \<open>The predicate \<open>AbstAtomicP\<close>\<close>

nominal_function AbstAtomicP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom t \<sharp> (v,i,y,y',t',u,u'); atom t' \<sharp> (v,i,y,y',u,u');
          atom u \<sharp> (v,i,y,y',u'); atom u' \<sharp> (v,i,y,y')\<rbrakk> \<Longrightarrow>
    AbstAtomicP v i y y' =
         Ex t (Ex u (Ex t' (Ex u'
           (AbstTermP v i (Var t) (Var t') AND AbstTermP v i (Var u) (Var u') AND
                      ((y EQ Q_Eq (Var t) (Var u) AND y' EQ Q_Eq (Var t') (Var u')) OR
                       (y EQ Q_Mem (Var t) (Var u) AND y' EQ Q_Mem (Var t') (Var u')))))))"
  by (auto simp: eqvt_def AbstAtomicP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows AbstAtomicP_fresh_iff [simp]:
       "a \<sharp> AbstAtomicP v i y y' \<longleftrightarrow> a \<sharp> v \<and> a \<sharp> i \<and> a \<sharp> y \<and> a \<sharp> y'"         (is ?thesis1)
    and AbstAtomicP_sf [iff]: "Sigma_fm (AbstAtomicP v i y y')"              (is ?thsf)
proof -
  obtain t::name and u::name and t'::name  and u'::name
    where "atom t \<sharp> (v,i,y,y',t',u,u')" "atom t' \<sharp> (v,i,y,y',u,u')"
          "atom u \<sharp> (v,i,y,y',u')" "atom u' \<sharp> (v,i,y,y')"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf
    by auto
qed

lemma AbstAtomicP_subst [simp]:
      "(AbstAtomicP v tm y y')(i::=w) = AbstAtomicP (subst i w v) (subst i w tm) (subst i w y) (subst i w y')"
proof -
  obtain t::name and u::name and t'::name  and u'::name
    where "atom t \<sharp> (v,tm,y,y',w,i,t',u,u')"  "atom t' \<sharp> (v,tm,y,y',w,i,u,u')"
          "atom u \<sharp> (v,tm,y,y',w,i,u')"       "atom u' \<sharp> (v,tm,y,y',w,i)"
    by (metis obtain_fresh)
  thus ?thesis
    by (simp add: AbstAtomicP.simps [of t _ _ _ _ t' u u'])
qed

declare AbstAtomicP.simps [simp del]

subsection \<open>The predicate \<open>AbsMakeForm\<close>\<close>

nominal_function SeqAbstFormP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom l \<sharp> (s,k,v,sli,sl,sl',m,n,smi,sm,sm',sni,sn,sn');
          atom sli \<sharp> (s,v,sl,sl',m,n,smi,sm,sm',sni,sn,sn');
          atom sl \<sharp> (s,v,sl',m,n,smi,sm,sm',sni,sn,sn');
          atom sl' \<sharp> (s,v,m,n,smi,sm,sm',sni,sn,sn');
          atom m \<sharp> (s,n,smi,sm,sm',sni,sn,sn');
          atom n \<sharp> (s,smi,sm,sm',sni,sn,sn'); atom smi \<sharp> (s,sm,sm',sni,sn,sn');
          atom sm \<sharp> (s,sm',sni,sn,sn'); atom sm' \<sharp> (s,sni,sn,sn');
          atom sni \<sharp> (s,sn,sn'); atom sn \<sharp> (s,sn'); atom sn' \<sharp> (s)\<rbrakk> \<Longrightarrow>
    SeqAbstFormP v i x x' s k =
      LstSeqP s k (HPair i (HPair x x')) AND
      All2 l (SUCC k) (Ex sli (Ex sl (Ex sl' (HPair (Var l) (HPair (Var sli) (HPair (Var sl) (Var sl'))) IN s AND
                (AbstAtomicP v (Var sli) (Var sl) (Var sl') OR
                OrdP (Var sli) AND
                Ex m (Ex n (Ex smi (Ex sm (Ex sm' (Ex sni (Ex sn (Ex sn'
                      (Var m IN Var l AND Var n IN Var l AND
                       HPair (Var m) (HPair (Var smi) (HPair (Var sm) (Var sm'))) IN s AND
                       HPair (Var n) (HPair (Var sni) (HPair (Var sn) (Var sn'))) IN s AND
                       ((Var sli EQ Var smi AND Var sli EQ Var sni AND
                         Var sl EQ Q_Disj (Var sm) (Var sn) AND
                         Var sl' EQ Q_Disj (Var sm') (Var sn')) OR
                        (Var sli EQ Var smi AND
                         Var sl EQ Q_Neg (Var sm) AND Var sl' EQ Q_Neg (Var sm')) OR
                        (SUCC (Var sli) EQ Var smi AND
                         Var sl EQ Q_Ex (Var sm) AND Var sl' EQ Q_Ex (Var sm'))))))))))))))))"
  by (auto simp: eqvt_def SeqAbstFormP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)


nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows SeqAbstFormP_fresh_iff [simp]:
       "a \<sharp> SeqAbstFormP v i x x' s k \<longleftrightarrow> a \<sharp> v \<and> a \<sharp> i \<and> a \<sharp> x \<and> a \<sharp> x' \<and> a \<sharp> s \<and> a \<sharp> k"  (is ?thesis1)
    and SeqAbstFormP_sf [iff]:
       "Sigma_fm (SeqAbstFormP v i x x' s k)"  (is ?thsf)
    and SeqAbstFormP_imp_OrdP:
       "{ SeqAbstFormP v u x x' s k } \<turnstile> OrdP k"  (is ?thOrd)
    and SeqAbstFormP_imp_LstSeqP:
       "{ SeqAbstFormP v u x x' s k } \<turnstile> LstSeqP s k (HPair u (HPair x x'))"  (is ?thLstSeq)
proof -
  obtain l::name and sli::name and sl::name and sl'::name and m::name and n::name and
         smi::name and sm::name and sm'::name and sni::name and sn::name and sn'::name
    where atoms:
         "atom l \<sharp> (s,k,v,sli,sl,sl',m,n,smi,sm,sm',sni,sn,sn')"
         "atom sli \<sharp> (s,v,sl,sl',m,n,smi,sm,sm',sni,sn,sn')"
         "atom sl \<sharp> (s,v,sl',m,n,smi,sm,sm',sni,sn,sn')"
         "atom sl' \<sharp> (s,v,m,n,smi,sm,sm',sni,sn,sn')"
         "atom m \<sharp> (s,n,smi,sm,sm',sni,sn,sn')" "atom n \<sharp> (s,smi,sm,sm',sni,sn,sn')"
         "atom smi \<sharp> (s,sm,sm',sni,sn,sn')"
         "atom sm \<sharp> (s,sm',sni,sn,sn')"
         "atom sm' \<sharp> (s,sni,sn,sn')"
         "atom sni \<sharp> (s,sn,sn')" "atom sn \<sharp> (s,sn')" "atom sn' \<sharp> s"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf ?thOrd ?thLstSeq
    by (auto intro: LstSeqP_OrdP)
qed

lemma SeqAbstFormP_subst [simp]:
      "(SeqAbstFormP v u x x' s k)(i::=t) =
       SeqAbstFormP (subst i t v) (subst i t u) (subst i t x) (subst i t x') (subst i t s) (subst i t k)"
proof -
  obtain l::name and sli::name and sl::name and sl'::name and m::name and n::name and
         smi::name and sm::name and sm'::name and sni::name and sn::name and sn'::name
   where "atom l \<sharp> (i,t,s,k,v,sli,sl,sl',m,n,smi,sm,sm',sni,sn,sn')"
         "atom sli \<sharp> (i,t,s,v,sl,sl',m,n,smi,sm,sm',sni,sn,sn')"
         "atom sl \<sharp> (i,t,s,v,sl',m,n,smi,sm,sm',sni,sn,sn')"
         "atom sl' \<sharp> (i,t,s,v,m,n,smi,sm,sm',sni,sn,sn')"
         "atom m \<sharp> (i,t,s,n,smi,sm,sm',sni,sn,sn')"
         "atom n \<sharp> (i,t,s,smi,sm,sm',sni,sn,sn')"
         "atom smi \<sharp> (i,t,s,sm,sm',sni,sn,sn')"
         "atom sm \<sharp> (i,t,s,sm',sni,sn,sn')" "atom sm' \<sharp> (i,t,s,sni,sn,sn')"
         "atom sni \<sharp> (i,t,s,sn,sn')" "atom sn \<sharp> (i,t,s,sn')" "atom sn' \<sharp> (i,t,s)"
    by (metis obtain_fresh)
  thus ?thesis
    by (force simp add: SeqAbstFormP.simps [of l _ _ _ sli sl sl' m n smi sm sm' sni sn sn'])
qed

declare SeqAbstFormP.simps [simp del]

subsection \<open>Defining the syntax: the main AbstForm predicate\<close>

nominal_function AbstFormP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom s \<sharp> (v,i,x,x',k);
          atom k \<sharp> (v,i,x,x')\<rbrakk> \<Longrightarrow>
    AbstFormP v i x x' = VarP v AND OrdP i AND Ex s (Ex k (SeqAbstFormP v i x x' (Var s) (Var k)))"
  by (auto simp: eqvt_def AbstFormP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows AbstFormP_fresh_iff [simp]:
       "a \<sharp> AbstFormP v i x x' \<longleftrightarrow> a \<sharp> v \<and> a \<sharp> i \<and> a \<sharp> x \<and> a \<sharp> x'" (is ?thesis1)
    and AbstFormP_sf [iff]:
       "Sigma_fm (AbstFormP v i x x')"    (is ?thsf)
proof -
  obtain s::name and k::name  where "atom s \<sharp> (v,i,x,x',k)" "atom k \<sharp> (v,i,x,x')"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf
    by auto
qed

lemma AbstFormP_subst [simp]:
     "(AbstFormP v i x x')(j::=t) = AbstFormP (subst j t v) (subst j t i) (subst j t x) (subst j t x')"
proof -
  obtain s::name and k::name  where "atom s \<sharp> (v,i,x,x',t,j,k)" "atom k \<sharp> (v,i,x,x',t,j)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: AbstFormP.simps [of s _ _ _ _ k])
qed

declare AbstFormP.simps [simp del]

section \<open>Substitution over formulas\<close>

subsection \<open>The predicate \<open>SubstAtomicP\<close>\<close>

nominal_function SubstAtomicP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom t \<sharp> (v,tm,y,y',t',u,u');
          atom t' \<sharp> (v,tm,y,y',u,u');
          atom u \<sharp> (v,tm,y,y',u');
          atom u' \<sharp> (v,tm,y,y')\<rbrakk> \<Longrightarrow>
    SubstAtomicP v tm y y' =
         Ex t (Ex u (Ex t' (Ex u'
           (SubstTermP v tm (Var t) (Var t') AND SubstTermP v tm (Var u) (Var u') AND
                      ((y EQ Q_Eq (Var t) (Var u) AND y' EQ Q_Eq (Var t') (Var u')) OR
                       (y EQ Q_Mem (Var t) (Var u) AND y' EQ Q_Mem (Var t') (Var u')))))))"
by (auto simp: eqvt_def SubstAtomicP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows SubstAtomicP_fresh_iff [simp]:
       "a \<sharp> SubstAtomicP v tm y y' \<longleftrightarrow> a \<sharp> v \<and> a \<sharp> tm \<and> a \<sharp> y \<and> a \<sharp> y'"           (is ?thesis1)
    and SubstAtomicP_sf [iff]: "Sigma_fm (SubstAtomicP v tm y y')"               (is ?thsf)
proof -
  obtain t::name and u::name and t'::name  and u'::name
    where "atom t \<sharp> (v,tm,y,y',t',u,u')" "atom t' \<sharp> (v,tm,y,y',u,u')"
          "atom u \<sharp> (v,tm,y,y',u')" "atom u' \<sharp> (v,tm,y,y')"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf
    by auto
qed

lemma SubstAtomicP_subst [simp]:
  "(SubstAtomicP v tm y y')(i::=w) = SubstAtomicP (subst i w v) (subst i w tm) (subst i w y) (subst i w y')"
proof -
  obtain t::name and u::name and t'::name  and u'::name
    where "atom t \<sharp> (v,tm,y,y',w,i,t',u,u')" "atom t' \<sharp> (v,tm,y,y',w,i,u,u')"
          "atom u \<sharp> (v,tm,y,y',w,i,u')" "atom u' \<sharp> (v,tm,y,y',w,i)"
    by (metis obtain_fresh)
  thus ?thesis
    by (simp add: SubstAtomicP.simps [of t _ _ _ _ t' u u'])
qed

lemma SubstAtomicP_cong:
  "\<lbrakk>H \<turnstile> v EQ v'; H \<turnstile> tm EQ tm'; H \<turnstile> x EQ x'; H \<turnstile> y EQ y'\<rbrakk>
   \<Longrightarrow> H \<turnstile> SubstAtomicP v tm x y IFF SubstAtomicP v' tm' x' y'"
  by (rule P4_cong) auto


subsection \<open>The predicate \<open>SubstMakeForm\<close>\<close>

nominal_function SeqSubstFormP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom l \<sharp> (s,k,v,u,sl,sl',m,n,sm,sm',sn,sn');
          atom sl \<sharp> (s,v,u,sl',m,n,sm,sm',sn,sn');
          atom sl' \<sharp> (s,v,u,m,n,sm,sm',sn,sn');
          atom m \<sharp> (s,n,sm,sm',sn,sn'); atom n \<sharp> (s,sm,sm',sn,sn');
          atom sm \<sharp> (s,sm',sn,sn'); atom sm' \<sharp> (s,sn,sn');
          atom sn \<sharp> (s,sn'); atom sn' \<sharp> s\<rbrakk> \<Longrightarrow>
    SeqSubstFormP v u x x' s k =
      LstSeqP s k (HPair x x') AND
      All2 l (SUCC k) (Ex sl (Ex sl' (HPair (Var l) (HPair (Var sl) (Var sl')) IN s AND
                (SubstAtomicP v u (Var sl) (Var sl') OR
                Ex m (Ex n (Ex sm (Ex sm' (Ex sn (Ex sn' (Var m IN Var l AND Var n IN Var l AND
                       HPair (Var m) (HPair (Var sm) (Var sm')) IN s AND
                       HPair (Var n) (HPair (Var sn) (Var sn')) IN s AND
                       ((Var sl EQ Q_Disj (Var sm) (Var sn) AND
                        Var sl' EQ Q_Disj (Var sm') (Var sn')) OR
                        (Var sl EQ Q_Neg (Var sm) AND Var sl' EQ Q_Neg (Var sm')) OR
                        (Var sl EQ Q_Ex (Var sm) AND Var sl' EQ Q_Ex (Var sm')))))))))))))"
  apply (simp_all add: eqvt_def SeqSubstFormP_graph_aux_def flip_fresh_fresh)
  by auto (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows SeqSubstFormP_fresh_iff [simp]:
       "a \<sharp> SeqSubstFormP v u x x' s k \<longleftrightarrow> a \<sharp> v \<and> a \<sharp> u \<and> a \<sharp> x \<and> a \<sharp> x' \<and> a \<sharp> s \<and> a \<sharp> k"  (is ?thesis1)
    and SeqSubstFormP_sf [iff]:
       "Sigma_fm (SeqSubstFormP v u x x' s k)"  (is ?thsf)
    and SeqSubstFormP_imp_OrdP:
       "{ SeqSubstFormP v u x x' s k } \<turnstile> OrdP k"  (is ?thOrd)
    and SeqSubstFormP_imp_LstSeqP:
       "{ SeqSubstFormP v u x x' s k } \<turnstile> LstSeqP s k (HPair x x')"  (is ?thLstSeq)
proof -
  obtain l::name and sl::name and sl'::name and m::name and n::name and
         sm::name and sm'::name and sn::name and sn'::name
    where atoms:
         "atom l \<sharp> (s,k,v,u,sl,sl',m,n,sm,sm',sn,sn')"
         "atom sl \<sharp> (s,v,u,sl',m,n,sm,sm',sn,sn')"
         "atom sl' \<sharp> (s,v,u,m,n,sm,sm',sn,sn')"
         "atom m \<sharp> (s,n,sm,sm',sn,sn')" "atom n \<sharp> (s,sm,sm',sn,sn')"
         "atom sm \<sharp> (s,sm',sn,sn')" "atom sm' \<sharp> (s,sn,sn')"
         "atom sn \<sharp> (s,sn')" "atom sn' \<sharp> (s)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf ?thOrd ?thLstSeq
    by (auto intro: LstSeqP_OrdP)
qed

lemma SeqSubstFormP_subst [simp]:
      "(SeqSubstFormP v u x x' s k)(i::=t) =
       SeqSubstFormP (subst i t v) (subst i t u) (subst i t x) (subst i t x') (subst i t s) (subst i t k)"
proof -
  obtain l::name and sl::name and sl'::name and m::name and n::name and
         sm::name and sm'::name and sn::name and sn'::name
   where "atom l \<sharp> (s,k,v,u,t,i,sl,sl',m,n,sm,sm',sn,sn')"
         "atom sl \<sharp> (s,v,u,t,i,sl',m,n,sm,sm',sn,sn')"
         "atom sl' \<sharp> (s,v,u,t,i,m,n,sm,sm',sn,sn')"
         "atom m \<sharp> (s,t,i,n,sm,sm',sn,sn')" "atom n \<sharp> (s,t,i,sm,sm',sn,sn')"
         "atom sm \<sharp> (s,t,i,sm',sn,sn')" "atom sm' \<sharp> (s,t,i,sn,sn')"
         "atom sn \<sharp> (s,t,i,sn')" "atom sn' \<sharp> (s,t,i)"
    by (metis obtain_fresh)
  thus ?thesis
    by (force simp add: SeqSubstFormP.simps [of l _ _ _ _ sl sl' m n sm sm' sn sn'])
qed

lemma SeqSubstFormP_cong:
  "\<lbrakk>H \<turnstile> t EQ t'; H \<turnstile> u EQ u'; H \<turnstile> s EQ s'; H \<turnstile> k EQ k'\<rbrakk>
   \<Longrightarrow> H \<turnstile> SeqSubstFormP v i t u s k IFF SeqSubstFormP v i t' u' s' k'"
   by (rule P4_cong [where tms="[v,i]"]) (auto simp: fresh_Cons)

declare SeqSubstFormP.simps [simp del]

subsection \<open>Defining the syntax: the main SubstForm predicate\<close>

nominal_function SubstFormP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom s \<sharp> (v,i,x,x',k); atom k \<sharp> (v,i,x,x')\<rbrakk> \<Longrightarrow>
    SubstFormP v i x x' =
      VarP v AND TermP i AND Ex s (Ex k (SeqSubstFormP v i x x' (Var s) (Var k)))"
  by (auto simp: eqvt_def SubstFormP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows SubstFormP_fresh_iff [simp]:
       "a \<sharp> SubstFormP v i x x' \<longleftrightarrow> a \<sharp> v \<and> a \<sharp> i \<and> a \<sharp> x \<and> a \<sharp> x'"  (is ?thesis1)
    and SubstFormP_sf [iff]:
       "Sigma_fm (SubstFormP v i x x')"  (is ?thsf)
proof -
  obtain s::name and k::name
    where "atom s \<sharp> (v,i,x,x',k)"  "atom k \<sharp> (v,i,x,x')"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf
    by auto
qed

lemma SubstFormP_subst [simp]:
     "(SubstFormP v i x x')(j::=t) = SubstFormP (subst j t v) (subst j t i) (subst j t x) (subst j t x')"
proof -
  obtain s::name and k::name  where "atom s \<sharp> (v,i,x,x',t,j,k)" "atom k \<sharp> (v,i,x,x',t,j)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: SubstFormP.simps [of s _ _ _ _ k])
qed

lemma SubstFormP_cong:
  "\<lbrakk>H \<turnstile> v EQ v'; H \<turnstile> i EQ i'; H \<turnstile> t EQ t'; H \<turnstile> u EQ u'\<rbrakk>
   \<Longrightarrow> H \<turnstile> SubstFormP v i t u IFF SubstFormP v' i' t' u'"
  by (rule P4_cong) auto

lemma ground_SubstFormP [simp]: "ground_fm (SubstFormP v y x x') \<longleftrightarrow> ground v \<and> ground y \<and> ground x \<and> ground x'"
  by (auto simp: ground_aux_def ground_fm_aux_def supp_conv_fresh)

declare SubstFormP.simps [simp del]

section \<open>The predicate \<open>AtomicP\<close>\<close>

nominal_function AtomicP :: "tm \<Rightarrow> fm"
  where "\<lbrakk>atom t \<sharp> (u,y); atom u \<sharp> y\<rbrakk> \<Longrightarrow>
    AtomicP y = Ex t (Ex u (TermP (Var t) AND TermP (Var u) AND
                      (y EQ Q_Eq (Var t) (Var u) OR
                       y EQ Q_Mem (Var t) (Var u))))"
  by (auto simp: eqvt_def AtomicP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows AtomicP_fresh_iff [simp]: "a \<sharp> AtomicP y \<longleftrightarrow> a \<sharp> y"    (is ?thesis1)
    and AtomicP_sf [iff]: "Sigma_fm (AtomicP y)"  (is ?thsf)
proof -
  obtain t::name and u::name  where "atom t \<sharp> (u,y)"  "atom u \<sharp> y"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf
    by auto
qed

lemma AtompicP_subst [simp]: "(AtomicP t)(j::=w) = AtomicP (subst j w t)"
proof -
  obtain x y :: name where "atom x \<sharp> (j,w,t,y)"   "atom y \<sharp> (j,w,t)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: AtomicP.simps [of x y])
qed


section \<open>The predicate \<open>MakeForm\<close>\<close>

nominal_function MakeFormP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom v \<sharp> (y,u,w,au); atom au \<sharp> (y,u,w)\<rbrakk> \<Longrightarrow>
    MakeFormP y u w =
      y EQ Q_Disj u w OR y EQ Q_Neg u OR
      Ex v (Ex au (AbstFormP (Var v) Zero u (Var au) AND y EQ Q_Ex (Var au)))"
  by (auto simp: eqvt_def MakeFormP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows MakeFormP_fresh_iff [simp]:
       "a \<sharp> MakeFormP y u w \<longleftrightarrow> a \<sharp> y \<and> a \<sharp> u \<and> a \<sharp> w"  (is ?thesis1)
    and MakeFormP_sf [iff]:
       "Sigma_fm (MakeFormP y u w)"  (is ?thsf)
proof -
  obtain v::name and au::name  where "atom v \<sharp> (y,u,w,au)"  "atom au \<sharp> (y,u,w)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf
    by auto
qed

declare MakeFormP.simps [simp del]

lemma MakeFormP_subst [simp]: "(MakeFormP y u t)(j::=w) = MakeFormP (subst j w y) (subst j w u) (subst j w t)"
proof -
  obtain a b :: name where "atom a \<sharp> (j,w,y,u,t,b)"   "atom b \<sharp> (j,w,y,u,t)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: MakeFormP.simps [of a _ _ _ b])
qed


section \<open>The predicate \<open>SeqFormP\<close>\<close>

(*SeqForm(s,k,t) \<equiv> LstSeq(s,k,t) \<and> (\<forall>n\<in>k)[Atomic (s n) \<or> (\<exists>m,l\<in>n)[MakeForm (s m) (s l) (s n)]]*)

nominal_function SeqFormP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom l \<sharp> (s,k,t,sl,m,n,sm,sn); atom sl \<sharp> (s,k,t,m,n,sm,sn);
          atom m \<sharp> (s,k,t,n,sm,sn); atom n \<sharp> (s,k,t,sm,sn);
          atom sm \<sharp> (s,k,t,sn); atom sn \<sharp> (s,k,t)\<rbrakk> \<Longrightarrow>
    SeqFormP s k t =
      LstSeqP s k t AND
      All2 n (SUCC k) (Ex sn (HPair (Var n) (Var sn) IN s AND (AtomicP (Var sn) OR
                Ex m (Ex l (Ex sm (Ex sl (Var m IN Var n AND Var l IN Var n AND
                       HPair (Var m) (Var sm) IN s AND HPair (Var l) (Var sl) IN s AND
                       MakeFormP (Var sn) (Var sm) (Var sl))))))))"
  by (auto simp: eqvt_def SeqFormP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows SeqFormP_fresh_iff [simp]:
       "a \<sharp> SeqFormP s k t \<longleftrightarrow> a \<sharp> s \<and> a \<sharp> k \<and> a \<sharp> t" (is ?thesis1)
    and SeqFormP_sf [iff]: "Sigma_fm (SeqFormP s k t)"          (is ?thsf)
    and SeqFormP_imp_OrdP:
       "{ SeqFormP s k t } \<turnstile> OrdP k"  (is ?thOrd)
    and SeqFormP_imp_LstSeqP:
       "{ SeqFormP s k t } \<turnstile> LstSeqP s k t"  (is ?thLstSeq)
proof -
  obtain l::name and sl::name and m::name and n::name and sm::name and sn::name
    where atoms: "atom l \<sharp> (s,k,t,sl,m,n,sm,sn)"   "atom sl \<sharp> (s,k,t,m,n,sm,sn)"
        "atom m \<sharp> (s,k,t,n,sm,sn)"   "atom n \<sharp> (s,k,t,sm,sn)"
        "atom sm \<sharp> (s,k,t,sn)"       "atom sn \<sharp> (s,k,t)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf ?thOrd ?thLstSeq
    by (auto intro: LstSeqP_OrdP)
qed

lemma SeqFormP_subst [simp]:
      "(SeqFormP s k t)(j::=w) = SeqFormP (subst j w s) (subst j w k) (subst j w t)"
proof -
  obtain l::name and sl::name and m::name and n::name and sm::name and sn::name
    where "atom l \<sharp> (j,w,s,t,k,sl,m,n,sm,sn)"   "atom sl \<sharp> (j,w,s,k,t,m,n,sm,sn)"
        "atom m \<sharp> (j,w,s,k,t,n,sm,sn)"   "atom n \<sharp> (j,w,s,k,t,sm,sn)"
        "atom sm \<sharp> (j,w,s,k,t,sn)"   "atom sn \<sharp> (j,w,s,k,t)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: SeqFormP.simps [of l _ _ _ sl m n sm sn])
qed

section \<open>The predicate \<open>FormP\<close>\<close>

subsection \<open>Definition\<close>

nominal_function FormP :: "tm \<Rightarrow> fm"
  where "\<lbrakk>atom k \<sharp> (s,y); atom s \<sharp> y\<rbrakk> \<Longrightarrow>
    FormP y = Ex k (Ex s (SeqFormP (Var s) (Var k) y))"
  by (auto simp: eqvt_def FormP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows FormP_fresh_iff [simp]: "a \<sharp> FormP y \<longleftrightarrow> a \<sharp> y"              (is ?thesis1)
    and FormP_sf [iff]:         "Sigma_fm (FormP y)"                 (is ?thsf)
proof -
  obtain k::name and s::name  where k: "atom k \<sharp> (s,y)" "atom s \<sharp> y"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf
    by auto
qed

lemma FormP_subst [simp]: "(FormP y)(j::=w) = FormP (subst j w y)"
proof -
  obtain k::name and s::name where "atom k \<sharp> (s,j,w,y)"  "atom s \<sharp> (j,w,y)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: FormP.simps [of k s])
qed


subsection \<open>The predicate \<open>VarNonOccFormP\<close> (Derived from \<open>SubstFormP\<close>)\<close>

nominal_function VarNonOccFormP :: "tm \<Rightarrow> tm \<Rightarrow> fm"
  where "VarNonOccFormP v x = FormP x AND SubstFormP v Zero x x"
  by (auto simp: eqvt_def VarNonOccFormP_graph_aux_def)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows VarNonOccFormP_fresh_iff [simp]: "a \<sharp> VarNonOccFormP v y \<longleftrightarrow> a \<sharp> v \<and> a \<sharp> y" (is ?thesis1)
    and VarNonOccFormP_sf [iff]: "Sigma_fm (VarNonOccFormP v y)" (is ?thsf)
proof -
  show ?thesis1 ?thsf
    by auto
qed

declare VarNonOccFormP.simps [simp del]

end

