chapter \<open>Section 6 Material and Gödel's First Incompleteness Theorem\<close>

theory Goedel_I
imports Pf_Predicates Functions II_Prelims
begin

section\<open>The Function W and Lemma 6.1\<close>

subsection\<open>Predicate form, defined on sequences\<close>

nominal_function SeqWRP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom l \<sharp> (s,k,sl); atom sl \<sharp> (s)\<rbrakk> \<Longrightarrow>
    SeqWRP s k y = LstSeqP s k y AND
          HPair Zero Zero IN s AND
          All2 l k (Ex sl (HPair (Var l) (Var sl) IN s AND
                           HPair (SUCC (Var l)) (Q_Succ (Var sl)) IN s))"
  by (auto simp: eqvt_def SeqWRP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows SeqWRP_fresh_iff [simp]: "a \<sharp> SeqWRP s k y \<longleftrightarrow> a \<sharp> s \<and> a \<sharp> k \<and> a \<sharp> y" (is ?thesis1)
    and SeqWRP_sf [iff]:         "Sigma_fm (SeqWRP s k y)"  (is ?thsf)
    and SeqWRP_imp_OrdP:         "{SeqWRP s k t} \<turnstile> OrdP k" (is ?thOrd)
    and SeqWRP_LstSeqP:          "{SeqWRP s k t} \<turnstile> LstSeqP s k t" (is ?thlstseq)
proof -
  obtain l::name and sl::name where "atom l \<sharp> (s,k,sl)" "atom sl \<sharp> (s)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf ?thOrd ?thlstseq
      by (auto intro: LstSeqP_OrdP[THEN cut1])
qed

lemma SeqWRP_subst [simp]:
      "(SeqWRP s k y)(i::=t) = SeqWRP (subst i t s) (subst i t k) (subst i t y)"
proof -
  obtain l::name and sl::name
    where "atom l \<sharp> (s,k,sl,t,i)" "atom sl \<sharp> (s,k,t,i)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: SeqWRP.simps [where l=l and sl=sl])
qed

lemma SeqWRP_cong:
  assumes "H \<turnstile> s EQ s'" and  "H \<turnstile> k EQ k'" and  "H \<turnstile> y EQ y'"
  shows "H \<turnstile> SeqWRP s k y IFF SeqWRP s' k' y'"
  by (rule P3_cong [OF _ assms], auto)

declare SeqWRP.simps [simp del]

subsection\<open>Predicate form of W\<close>

nominal_function WRP :: "tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom s \<sharp> (x,y)\<rbrakk> \<Longrightarrow>
    WRP x y = Ex s (SeqWRP (Var s) x y)"
  by (auto simp: eqvt_def WRP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows WRP_fresh_iff [simp]: "a \<sharp> WRP x y \<longleftrightarrow> a \<sharp> x \<and> a \<sharp> y" (is ?thesis1)
    and sigma_fm_WRP [simp]:  "Sigma_fm (WRP x y)"  (is ?thsf)
proof -
  obtain s::name where "atom s \<sharp> (x,y)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf
    by auto
qed

lemma WRP_subst [simp]: "(WRP x y)(i::=t) = WRP (subst i t x) (subst i t y)"
proof -
  obtain s::name where "atom s \<sharp> (x,y,t,i)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: WRP.simps [of s])
qed

lemma WRP_cong: "H \<turnstile> t EQ t' \<Longrightarrow> H \<turnstile> u EQ u' \<Longrightarrow> H \<turnstile> WRP t u IFF WRP t' u'"
  by (rule P2_cong) auto

declare WRP.simps [simp del]

lemma ground_WRP [simp]: "ground_fm (WRP x y) \<longleftrightarrow> ground x \<and> ground y"
  by (auto simp: ground_aux_def ground_fm_aux_def supp_conv_fresh)

lemma SeqWRP_Zero: "{} \<turnstile> SyntaxN.Ex s (SeqWRP (Var s) Zero Zero)"
proof -
  obtain l sl :: name where "atom l \<sharp> (s, sl)" "atom sl \<sharp> s" by (metis obtain_fresh)
  then show ?thesis
    apply (subst SeqWRP.simps[of l _ _ sl]; simp)
    apply (rule Ex_I[where x="(Eats Zero (HPair Zero Zero))"], simp)
    apply (auto intro!: Mem_Eats_I2)
    done
qed

lemma WRP_Zero: "{} \<turnstile> WRP Zero Zero"
  by (subst WRP.simps[of undefined]) (auto simp: SeqWRP_Zero)

lemma SeqWRP_HPair_Zero_Zero: "{SeqWRP s k y} \<turnstile> HPair Zero Zero IN s"
proof -
  let ?vs = "(s,k,y)"
  obtain l::name and sl::name
    where "atom l \<sharp> (?vs,sl)" "atom sl \<sharp> (?vs)" by (metis obtain_fresh)
  then show ?thesis
    by (subst SeqWRP.simps[of l _ _ sl]) auto
qed

lemma SeqWRP_Succ:
  assumes "atom s \<sharp> (s1,k1,y)"
  shows "{SeqWRP s1 k1 y} \<turnstile> SyntaxN.Ex s (SeqWRP (Var s) (SUCC k1) (Q_Succ y))"
proof -
  let ?vs = "(s,s1,k1,y)"
  obtain l::name and sl::name and l1::name and sl1::name
    where atoms:
      "atom l \<sharp> (?vs,sl1,l1,sl)"
      "atom sl \<sharp> (?vs,sl1,l1)"
      "atom l1 \<sharp> (?vs,sl1)"
      "atom sl1 \<sharp> (?vs)"
    by (metis obtain_fresh)
  let ?hyp = "{RestrictedP s1 (SUCC k1) (Var s), OrdP k1, SeqWRP s1 k1 y}"
  show ?thesis
    using assms atoms
    apply (auto simp: SeqWRP.simps [of l "Var s" _ sl])
    apply (rule cut_same [where A="OrdP k1"])
    apply (rule SeqWRP_imp_OrdP)
    apply (rule cut_same [OF exists_RestrictedP [of s s1 "SUCC k1"]])
     apply (rule AssumeH Ex_EH Conj_EH | simp)+
      apply (rule Ex_I [where x="Eats (Var s) (HPair (SUCC k1)  (Q_Succ y))"])
      apply (simp_all (no_asm_simp))
    apply (rule Conj_I)
    apply (blast intro: RestrictedP_LstSeqP_Eats[THEN cut2] SeqWRP_LstSeqP[THEN cut1])
    apply (rule Conj_I)
     apply (rule Mem_Eats_I1)
     apply (blast intro: RestrictedP_Mem[THEN cut3] SeqWRP_HPair_Zero_Zero[THEN cut1] Zero_In_SUCC[THEN cut1])
  proof (rule All2_SUCC_I, simp_all)
    show "?hyp \<turnstile>  SyntaxN.Ex sl
     (HPair k1 (Var sl) IN Eats (Var s) (HPair (SUCC k1) (Q_Succ y)) AND
      HPair (SUCC k1) (Q_Succ (Var sl)) IN
      Eats (Var s) (HPair (SUCC k1) (Q_Succ y)))"
      \<comment> \<open>verifying the final values\<close>
      apply (rule Ex_I [where x="y"])
      using assms atoms apply simp
      apply (rule Conj_I[rotated])
       apply (rule Mem_Eats_I2, rule Refl)
     apply (rule Mem_Eats_I1)
      apply (rule RestrictedP_Mem[THEN cut3])
        apply (rule AssumeH)
       apply (simp add: LstSeqP_imp_Mem SeqWRP_LstSeqP thin1)
      apply (rule Mem_SUCC_Refl)
      done
  next
    show "?hyp \<turnstile> All2 l k1
     (SyntaxN.Ex sl
       (HPair (Var l) (Var sl) IN
        Eats (Var s) (HPair (SUCC k1) (Q_Succ y)) AND
        HPair (SUCC (Var l)) (Q_Succ (Var sl)) IN
        Eats (Var s) (HPair (SUCC k1) (Q_Succ y))))"
      \<comment> \<open>verifying the sequence buildup\<close>
      apply (rule All_I Imp_I)+
      using assms atoms apply simp_all
        \<comment> \<open>... the sequence buildup via s1\<close>
    apply (simp add: SeqWRP.simps [of l s1 _ sl])
      apply (rule AssumeH Ex_EH Conj_EH)+
      apply (rule All2_E [THEN rotate2], auto del: Disj_EH)
      apply (rule Ex_I [where x="Var sl"], simp)
      apply (rule Conj_I)
       apply (blast intro: Mem_Eats_I1 [OF RestrictedP_Mem [THEN cut3]] Mem_SUCC_I1)
      apply (blast intro: Mem_Eats_I1 [OF RestrictedP_Mem [THEN cut3]] OrdP_IN_SUCC)
      done
  qed
qed (*>*)

lemma WRP_Succ: "{OrdP i, WRP i y} \<turnstile> WRP (SUCC i) (Q_Succ y)"
proof -
  obtain s t :: name where "atom s \<sharp> (i, y)" "atom t \<sharp> (s,i, y)" by (metis obtain_fresh)
  then show ?thesis
    by (subst WRP.simps[of s], simp, subst WRP.simps[of t], simp) (force intro: SeqWRP_Succ[THEN cut1])
qed

lemma WRP: "{} \<turnstile> WRP (ORD_OF i) \<guillemotleft>ORD_OF i\<guillemotright>"
  by (induct i)
    (auto simp: WRP_Zero quot_Succ intro!: WRP_Succ[THEN cut2])

lemma prove_WRP:  "{} \<turnstile> WRP \<guillemotleft>Var x\<guillemotright> \<guillemotleft>\<guillemotleft>Var x\<guillemotright>\<guillemotright>"
  unfolding quot_Var quot_Succ
  by (rule WRP_Succ[THEN cut2]) (auto simp: WRP)

subsection\<open>Proving that these relations are functions\<close>

lemma SeqWRP_Zero_E:
  assumes "insert (y EQ Zero) H \<turnstile> A"  "H \<turnstile> k EQ Zero"
  shows "insert (SeqWRP s k y) H \<turnstile> A"
proof -
  obtain l::name and sl::name
    where "atom l \<sharp> (s,k,sl)" "atom sl \<sharp> (s)"
    by (metis obtain_fresh)
  thus ?thesis
    apply (auto simp: SeqWRP.simps [where s=s and l=l and sl=sl])
    apply (rule cut_same [where A = "LstSeqP s Zero y"])
    apply (blast intro: thin1 assms  LstSeqP_cong [OF Refl _ Refl, THEN Iff_MP_same])
    apply (rule cut_same [where A = "y EQ Zero"])
    apply (blast intro: LstSeqP_EQ)
    apply (metis rotate2 assms(1) thin1)
    done
qed

lemma SeqWRP_SUCC_lemma:
  assumes y': "atom y' \<sharp> (s,k,y)"
  shows "{SeqWRP s (SUCC k) y} \<turnstile> Ex y' (SeqWRP s k (Var y') AND y EQ Q_Succ (Var y'))"
proof -
  obtain l::name and sl::name
    where atoms: "atom l \<sharp> (s,k,y,y',sl)" "atom sl \<sharp> (s,k,y,y')"
    by (metis obtain_fresh)
  thus ?thesis using y'
    apply (auto simp: SeqWRP.simps [where s=s and l=l and sl=sl])
    apply (rule All2_SUCC_E' [where t=k, THEN rotate2], auto)
    apply (rule Ex_I [where x = "Var sl"], auto)
    apply (blast intro: LstSeqP_SUCC) \<comment> \<open>showing @{term"SeqWRP s k (Var sl)"}\<close>
    apply (blast intro: ContraProve LstSeqP_EQ)
    done
qed

lemma SeqWRP_SUCC_E:
  assumes y': "atom y' \<sharp> (s,k,y)" and k': "H \<turnstile> k' EQ (SUCC k)"
  shows "insert (SeqWRP s k' y) H  \<turnstile> Ex y' (SeqWRP s k (Var y') AND y EQ Q_Succ (Var y'))"
  using SeqWRP_cong [OF Refl k' Refl] cut1 [OF SeqWRP_SUCC_lemma [of y' s k y]]
  by (metis Assume Iff_MP_left Iff_sym y')

lemma SeqWRP_unique: "{OrdP x, SeqWRP s x y, SeqWRP s' x y'} \<turnstile> y' EQ y"
proof -
  obtain i::name and j::name and j'::name and k::name and sl::name and sl'::name and l::name and pi::name
    where  i: "atom i \<sharp> (s,s',y,y')" and j: "atom j \<sharp> (s,s',i,x,y,y')" and j': "atom j' \<sharp> (s,s',i,j,x,y,y')"
      and atoms: "atom k \<sharp> (s,s',i,j,j')" "atom sl \<sharp> (s,s',i,j,j',k)" "atom sl' \<sharp> (s,s',i,j,j',k,sl)"
                 "atom pi \<sharp> (s,s',i,j,j',k,sl,sl')"
    by (metis obtain_fresh)
  have "{OrdP (Var i)} \<turnstile> All j (All j' (SeqWRP s (Var i) (Var j) IMP (SeqWRP s' (Var i) (Var j') IMP Var j' EQ Var j)))"
    apply (rule OrdIndH [where j=k])
    using i j j' atoms apply auto
    apply (rule rotate4)
    apply (rule OrdP_cases_E [where k=pi], simp_all)
    \<comment> \<open>Zero case\<close>
    apply (rule SeqWRP_Zero_E [THEN rotate3])
    prefer 2 apply blast
    apply (rule SeqWRP_Zero_E [THEN rotate4])
    prefer 2 apply blast
    apply (blast intro: ContraProve [THEN rotate4] Sym Trans)
    \<comment> \<open>SUCC case\<close>
    apply (rule Ex_I [where x = "Var pi"], auto)
    apply (metis ContraProve EQ_imp_SUBS2 Mem_SUCC_I2 Refl Subset_D)
    apply (rule cut_same)
    apply (rule SeqWRP_SUCC_E [of sl' s' "Var pi", THEN rotate4], auto)
    apply (rule cut_same)
    apply (rule SeqWRP_SUCC_E [of sl s "Var pi", THEN rotate7], auto)
    apply (rule All_E [where x = "Var sl", THEN rotate5], simp)
    apply (rule All_E [where x = "Var sl'"], simp)
    apply (rule Imp_E, blast)+
    apply (rule cut_same [OF Q_Succ_cong [OF Assume]])
    apply (blast intro: Trans [OF Hyp Sym] HPair_cong)
    done
  hence "{OrdP (Var i)} \<turnstile> (All j' (SeqWRP s (Var i) (Var j) IMP (SeqWRP s' (Var i) (Var j') IMP Var j' EQ Var j)))(j::=y)"
    by (metis All_D)
  hence "{OrdP (Var i)} \<turnstile> (SeqWRP s (Var i) y IMP (SeqWRP s' (Var i) (Var j') IMP Var j' EQ y))(j'::=y')"
    using j j'
    by simp (drule All_D [where x=y'], simp)
  hence "{} \<turnstile> OrdP (Var i) IMP (SeqWRP s (Var i) y IMP (SeqWRP s' (Var i) y' IMP y' EQ y))"
    using j j'
    by simp (metis Imp_I)
  hence "{} \<turnstile> (OrdP (Var i) IMP (SeqWRP s (Var i) y IMP (SeqWRP s' (Var i) y' IMP y' EQ y)))(i::=x)"
    by (metis Subst emptyE)
  thus ?thesis using i
    by simp (metis anti_deduction insert_commute)
qed

theorem WRP_unique: "{OrdP x, WRP x y, WRP x y'} \<turnstile> y' EQ y"
proof -
  obtain s::name and s'::name
    where "atom s \<sharp> (x,y,y')"  "atom s' \<sharp> (x,y,y',s)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: SeqWRP_unique [THEN rotate3] WRP.simps [of s _ y]  WRP.simps [of s' _ y'])
qed

section\<open>The Function HF and Lemma 6.2\<close>

subsection \<open>Defining the syntax: quantified body\<close>

nominal_function SeqHRP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom l \<sharp> (s,k,sl,sl',m,n,sm,sm',sn,sn');
          atom sl \<sharp> (s,sl',m,n,sm,sm',sn,sn');
          atom sl' \<sharp> (s,m,n,sm,sm',sn,sn');
          atom m \<sharp> (s,n,sm,sm',sn,sn');
          atom n \<sharp> (s,sm,sm',sn,sn');
          atom sm \<sharp> (s,sm',sn,sn');
          atom sm' \<sharp> (s,sn,sn');
          atom sn \<sharp> (s,sn');
          atom sn' \<sharp> (s)\<rbrakk> \<Longrightarrow>
    SeqHRP x x' s k =
      LstSeqP s k (HPair x x') AND
      All2 l (SUCC k) (Ex sl (Ex sl' (HPair (Var l) (HPair (Var sl) (Var sl')) IN s AND
                ((OrdP (Var sl) AND WRP (Var sl) (Var sl')) OR
                 Ex m (Ex n (Ex sm (Ex sm' (Ex sn (Ex sn' (Var m IN Var l AND Var n IN Var l AND
                       HPair (Var m) (HPair (Var sm) (Var sm')) IN s AND
                       HPair (Var n) (HPair (Var sn) (Var sn')) IN s AND
                       Var sl EQ HPair (Var sm) (Var sn) AND
                       Var sl' EQ Q_HPair (Var sm') (Var sn')))))))))))"
by (auto simp: eqvt_def SeqHRP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
 shows SeqHRP_fresh_iff [simp]:
      "a \<sharp> SeqHRP x x' s k \<longleftrightarrow> a \<sharp> x \<and> a \<sharp> x' \<and> a \<sharp> s \<and> a \<sharp> k"  (is ?thesis1)
  and SeqHRP_sf [iff]:  "Sigma_fm (SeqHRP x x' s k)"  (is ?thsf)
  and SeqHRP_imp_OrdP: "{ SeqHRP x y s k } \<turnstile> OrdP k"  (is ?thord)
  and SeqHRP_imp_LstSeqP: "{ SeqHRP x y s k } \<turnstile> LstSeqP s k (HPair x y)"  (is ?thlstseq)
proof -
  obtain l::name and sl::name and sl'::name and m::name and n::name and
         sm::name and sm'::name and sn::name and sn'::name
    where atoms:
         "atom l \<sharp> (s,k,sl,sl',m,n,sm,sm',sn,sn')"
         "atom sl \<sharp> (s,sl',m,n,sm,sm',sn,sn')" "atom sl' \<sharp> (s,m,n,sm,sm',sn,sn')"
         "atom m \<sharp> (s,n,sm,sm',sn,sn')" "atom n \<sharp> (s,sm,sm',sn,sn')"
         "atom sm \<sharp> (s,sm',sn,sn')" "atom sm' \<sharp> (s,sn,sn')"
         "atom sn \<sharp> (s,sn')" "atom sn' \<sharp> (s)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf ?thord ?thlstseq
    by (auto intro: LstSeqP_OrdP)
qed

lemma SeqHRP_subst [simp]:
      "(SeqHRP x x' s k)(i::=t) = SeqHRP (subst i t x) (subst i t x') (subst i t s) (subst i t k)"
proof -
  obtain l::name and sl::name and sl'::name and m::name and n::name and
         sm::name and sm'::name and sn::name and sn'::name
    where "atom l \<sharp> (s,k,t,i,sl,sl',m,n,sm,sm',sn,sn')"
          "atom sl \<sharp> (s,t,i,sl',m,n,sm,sm',sn,sn')"
          "atom sl' \<sharp> (s,t,i,m,n,sm,sm',sn,sn')"
          "atom m \<sharp> (s,t,i,n,sm,sm',sn,sn')" "atom n \<sharp> (s,t,i,sm,sm',sn,sn')"
          "atom sm \<sharp> (s,t,i,sm',sn,sn')" "atom sm' \<sharp> (s,t,i,sn,sn')"
          "atom sn \<sharp> (s,t,i,sn')" "atom sn' \<sharp> (s,t,i)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: SeqHRP.simps [of l _ _ sl sl' m n sm sm' sn sn'])
qed

lemma SeqHRP_cong:
  assumes "H \<turnstile> x EQ x'" and "H \<turnstile> y EQ y'" "H \<turnstile> s EQ s'" and  "H \<turnstile> k EQ k'"
  shows "H \<turnstile> SeqHRP x y s k IFF SeqHRP x' y' s' k'"
  by (rule P4_cong [OF _ assms], auto)

subsection \<open>Defining the syntax: main predicate\<close>

nominal_function HRP :: "tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom s \<sharp> (x,x',k); atom k \<sharp> (x,x')\<rbrakk> \<Longrightarrow>
         HRP x x' = Ex s (Ex k (SeqHRP x x' (Var s) (Var k)))"
  by (auto simp: eqvt_def HRP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
 shows HRP_fresh_iff [simp]: "a \<sharp> HRP x x' \<longleftrightarrow> a \<sharp> x \<and> a \<sharp> x'"  (is ?thesis1)
   and HRP_sf [iff]:         "Sigma_fm (HRP x x')"  (is ?thsf)
proof -
  obtain s::name and k::name  where "atom s \<sharp> (x,x',k)"  "atom k \<sharp> (x,x')"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf
    by auto
qed

lemma HRP_subst [simp]: "(HRP x x')(i::=t) = HRP (subst i t x) (subst i t x')"
proof -
  obtain s::name and k::name where "atom s \<sharp> (x,x',t,i,k)"  "atom k \<sharp> (x,x',t,i)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: HRP.simps [of s _ _ k])
qed

subsection\<open>Proving that these relations are functions\<close>

lemma SeqHRP_lemma:
  assumes "atom m \<sharp> (x,x',s,k,n,sm,sm',sn,sn')" "atom n \<sharp> (x,x',s,k,sm,sm',sn,sn')"
          "atom sm \<sharp> (x,x',s,k,sm',sn,sn')" "atom sm' \<sharp> (x,x',s,k,sn,sn')"
          "atom sn \<sharp> (x,x',s,k,sn')" "atom sn' \<sharp> (x,x',s,k)"
    shows "{ SeqHRP x x' s k }
         \<turnstile> (OrdP x AND WRP x x') OR
             Ex m (Ex n (Ex sm (Ex sm' (Ex sn (Ex sn' (Var m IN k AND Var n IN k AND
                       SeqHRP (Var sm) (Var sm') s (Var m) AND
                       SeqHRP (Var sn) (Var sn') s (Var n) AND
                       x EQ HPair (Var sm) (Var sn) AND
                       x' EQ Q_HPair (Var sm') (Var sn')))))))"
proof -
  obtain l::name and sl::name and sl'::name
    where atoms:
          "atom l \<sharp> (x,x',s,k,sl,sl',m,n,sm,sm',sn,sn')"
          "atom sl \<sharp> (x,x',s,k,sl',m,n,sm,sm',sn,sn')"
          "atom sl' \<sharp> (x,x',s,k,m,n,sm,sm',sn,sn')"
    by (metis obtain_fresh)
  thus ?thesis using atoms assms
    apply (simp add: SeqHRP.simps [of l s k sl sl' m n sm sm' sn sn'])
    apply (rule Conj_E)
    apply (rule All2_SUCC_E' [where t=k, THEN rotate2], simp_all)
    apply (rule rotate2)
    apply (rule Ex_E Conj_E)+
    apply (rule cut_same [where A = "HPair x x' EQ HPair (Var sl) (Var sl')"])
    apply (metis Assume LstSeqP_EQ rotate4, simp_all, clarify)
    apply (rule Disj_E [THEN rotate4])
    apply (rule Disj_I1)
    apply (metis Assume AssumeH(3) Sym thin1  Iff_MP_same [OF Conj_cong [OF OrdP_cong WRP_cong] Assume])
    \<comment> \<open>auto could be used but is VERY SLOW\<close>
    apply (rule Disj_I2)
    apply (rule Ex_E Conj_EH)+
    apply simp_all
    apply (rule Ex_I [where x = "Var m"], simp)
    apply (rule Ex_I [where x = "Var n"], simp)
    apply (rule Ex_I [where x = "Var sm"], simp)
    apply (rule Ex_I [where x = "Var sm'"], simp)
    apply (rule Ex_I [where x = "Var sn"], simp)
    apply (rule Ex_I [where x = "Var sn'"], simp)
    apply (simp add: SeqHRP.simps [of l _ _ sl sl' m n sm sm' sn sn'])
    apply (rule Conj_I, blast)+
    \<comment> \<open>first SeqHRP subgoal\<close>
    apply (rule Conj_I)+
    apply (blast intro: LstSeqP_Mem)
    apply (rule All2_Subset [OF Hyp], blast)
    apply (blast intro!: SUCC_Subset_Ord LstSeqP_OrdP, blast, simp)
    \<comment> \<open>next SeqHRP subgoal\<close>
    apply (rule Conj_I)+
    apply (blast intro: LstSeqP_Mem)
    apply (rule All2_Subset [OF Hyp], blast)
    apply (auto intro!: SUCC_Subset_Ord LstSeqP_OrdP)
    \<comment> \<open>finally, the equality pair\<close>
    apply (blast intro: Trans)+
    done
qed

lemma SeqHRP_unique: "{SeqHRP x y s u, SeqHRP x y' s' u'} \<turnstile> y' EQ y"
proof -
  obtain i::name and j::name and j'::name and k::name and k'::name and l::name
     and m::name and n::name and sm::name and sn::name and sm'::name and sn'::name
     and m2::name and n2::name and sm2::name and sn2::name and sm2'::name and sn2'::name
    where atoms:  "atom i \<sharp> (s,s',y,y')"   "atom j \<sharp> (s,s',i,x,y,y')"  "atom j' \<sharp> (s,s',i,j,x,y,y')"
                  "atom k \<sharp> (s,s',x,y,y',u',i,j,j')" "atom k' \<sharp> (s,s',x,y,y',k,i,j,j')" "atom l \<sharp> (s,s',i,j,j',k,k')"
                  "atom m \<sharp> (s,s',i,j,j',k,k',l)"   "atom n \<sharp> (s,s',i,j,j',k,k',l,m)"
                  "atom sm \<sharp> (s,s',i,j,j',k,k',l,m,n)"  "atom sn \<sharp> (s,s',i,j,j',k,k',l,m,n,sm)"
                  "atom sm' \<sharp> (s,s',i,j,j',k,k',l,m,n,sm,sn)"   "atom sn' \<sharp> (s,s',i,j,j',k,k',l,m,n,sm,sn,sm')"
                  "atom m2 \<sharp> (s,s',i,j,j',k,k',l,m,n,sm,sn,sm',sn')"   "atom n2 \<sharp> (s,s',i,j,j',k,k',l,m,n,sm,sn,sm',sn',m2)"
                  "atom sm2 \<sharp> (s,s',i,j,j',k,k',l,m,n,sm,sn,sm',sn',m2,n2)"  "atom sn2 \<sharp> (s,s',i,j,j',k,k',l,m,n,sm,sn,sm',sn',m2,n2,sm2)"
                  "atom sm2' \<sharp> (s,s',i,j,j',k,k',l,m,n,sm,sn,sm',sn',m2,n2,sm2,sn2)"   "atom sn2' \<sharp> (s,s',i,j,j',k,k',l,m,n,sm,sn,sm',sn',m2,n2,sm2,sn2,sm2')"
    by (metis obtain_fresh)
  have "{OrdP (Var k)}
       \<turnstile> All i (All j (All j' (All k' (SeqHRP (Var i) (Var j) s (Var k) IMP (SeqHRP (Var i) (Var j') s' (Var k') IMP Var j' EQ Var j)))))"
    apply (rule OrdIndH [where j=l])
    using atoms apply auto
    apply (rule Swap)
    apply (rule cut_same)
    apply (rule cut1 [OF SeqHRP_lemma [of m "Var i" "Var j" s "Var k" n sm sm' sn sn']], simp_all, blast)
    apply (rule cut_same)
    apply (rule cut1 [OF SeqHRP_lemma [of m2 "Var i" "Var j'" s' "Var k'" n2 sm2 sm2' sn2 sn2']], simp_all, blast)
    apply (rule Disj_EH Conj_EH)+
    \<comment> \<open>case 1, both are ordinals\<close>
    apply (blast intro: cut3 [OF WRP_unique])
    \<comment> \<open>case 2, @{term "OrdP (Var i)"} but also a pair\<close>
    apply (rule Conj_EH Ex_EH)+
    apply simp_all
    apply (rule cut_same [where A = "OrdP (HPair (Var sm) (Var sn))"])
    apply (blast intro: OrdP_cong [OF Hyp, THEN Iff_MP_same], blast)
    \<comment> \<open>towards second two cases\<close>
    apply (rule Ex_E Disj_EH Conj_EH)+
    \<comment> \<open>case 3, @{term "OrdP (Var i)"} but also a pair\<close>
    apply (rule cut_same [where A = "OrdP (HPair (Var sm2) (Var sn2))"])
    apply (blast intro: OrdP_cong [OF Hyp, THEN Iff_MP_same], blast)
    \<comment> \<open>case 4, two pairs\<close>
    apply (rule Ex_E Disj_EH Conj_EH)+
    apply (rule All_E' [OF Hyp, where x="Var m"], blast)
    apply (rule All_E' [OF Hyp, where x="Var n"], blast, simp_all)
    apply (rule Disj_EH, blast intro: thin1 ContraProve)+
    apply (rule All_E [where x="Var sm"], simp)
    apply (rule All_E [where x="Var sm'"], simp)
    apply (rule All_E [where x="Var sm2'"], simp)
    apply (rule All_E [where x="Var m2"], simp)
    apply (rule All_E [where x="Var sn", THEN rotate2], simp)
    apply (rule All_E [where x="Var sn'"], simp)
    apply (rule All_E [where x="Var sn2'"], simp)
    apply (rule All_E [where x="Var n2"], simp)
    apply (rule cut_same [where A = "HPair (Var sm) (Var sn) EQ HPair (Var sm2) (Var sn2)"])
    apply (blast intro: Sym Trans)
    apply (rule cut_same [where A = "SeqHRP (Var sn) (Var sn2') s' (Var n2)"])
    apply (blast intro: SeqHRP_cong [OF Hyp Refl Refl, THEN Iff_MP2_same])
    apply (rule cut_same [where A = "SeqHRP (Var sm) (Var sm2') s' (Var m2)"])
    apply (blast intro: SeqHRP_cong [OF Hyp Refl Refl, THEN Iff_MP2_same])
    apply (rule Disj_EH, blast intro: thin1 ContraProve)+
    apply (blast intro: Trans [OF Hyp Sym] intro!: HPair_cong)
    done
  hence "{OrdP (Var k)}
         \<turnstile> All j (All j' (All k' (SeqHRP x (Var j) s (Var k)
               IMP (SeqHRP x (Var j') s' (Var k') IMP Var j' EQ Var j))))"
    apply (rule All_D [where x = x, THEN cut_same])
    using atoms by auto
  hence "{OrdP (Var k)}
         \<turnstile> All j' (All k' (SeqHRP x y s (Var k) IMP (SeqHRP x (Var j') s' (Var k') IMP Var j' EQ y)))"
    apply (rule All_D [where x = y, THEN cut_same])
    using atoms by auto
  hence "{OrdP (Var k)}
          \<turnstile> All k' (SeqHRP x y s (Var k) IMP (SeqHRP x y' s' (Var k') IMP y' EQ y))"
    apply (rule All_D [where x = y', THEN cut_same])
    using atoms by auto
  hence "{OrdP (Var k)} \<turnstile> SeqHRP x y s (Var k) IMP (SeqHRP x y' s' u' IMP y' EQ y)"
    apply (rule All_D [where x = u', THEN cut_same])
    using atoms by auto
  hence "{SeqHRP x y s (Var k)} \<turnstile> SeqHRP x y s (Var k) IMP (SeqHRP x y' s' u' IMP y' EQ y)"
    by (metis SeqHRP_imp_OrdP cut1)
  hence "{} \<turnstile> ((SeqHRP x y s (Var k) IMP (SeqHRP x y' s' u' IMP y' EQ y)))(k::=u)"
    by (metis Subst emptyE Assume MP_same Imp_I)
  hence "{} \<turnstile> SeqHRP x y s u IMP (SeqHRP x y' s' u' IMP y' EQ y)"
    using atoms by simp
  thus ?thesis
    by (metis anti_deduction insert_commute)
qed

theorem HRP_unique: "{HRP x y, HRP x y'} \<turnstile> y' EQ y"
proof -
  obtain s::name and s'::name and k::name and k'::name
    where "atom s \<sharp> (x,y,y')" "atom s' \<sharp> (x,y,y',s)"
          "atom k \<sharp> (x,y,y',s,s')" "atom k' \<sharp> (x,y,y',s,s',k)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: SeqHRP_unique HRP.simps [of s x y k]  HRP.simps [of s' x y' k'])
qed

lemma HRP_ORD_OF: "{} \<turnstile> HRP (ORD_OF i) \<guillemotleft>ORD_OF i\<guillemotright>"
proof -
  let ?vs = "(i)"
  obtain s k l::name and sl::name and sl'::name and m::name and n::name and
    sm::name and sm'::name and sn::name and sn'::name
    where atoms:
      "atom s \<sharp> (?vs,sl,sl',m,n,sm,sm',sn,sn',l,k)"
      "atom k \<sharp> (?vs,sl,sl',m,n,sm,sm',sn,sn',l)"
      "atom l \<sharp> (?vs,sl,sl',m,n,sm,sm',sn,sn')"
      "atom sl \<sharp> (?vs,sl',m,n,sm,sm',sn,sn')" "atom sl' \<sharp> (?vs,m,n,sm,sm',sn,sn')"
      "atom m \<sharp> (?vs,n,sm,sm',sn,sn')" "atom n \<sharp> (?vs,sm,sm',sn,sn')"
      "atom sm \<sharp> (?vs,sm',sn,sn')" "atom sm' \<sharp> (?vs,sn,sn')"
      "atom sn \<sharp> (?vs,sn')" "atom sn' \<sharp> ?vs"
    by (metis obtain_fresh)
  then show ?thesis
  apply (subst HRP.simps[of s _ _ k]; simp)
    apply (subst SeqHRP.simps[of l _ _ sl sl' m n sm sm' sn sn']; simp?)
    apply (rule Ex_I[where x="Eats Zero (HPair Zero (HPair (ORD_OF i) \<guillemotleft>ORD_OF i\<guillemotright>))"]; simp)
    apply (rule Ex_I[where x="Zero"]; simp)
    apply (rule Conj_I[OF LstSeqP_single])
    apply (rule All2_SUCC_I, simp)
     apply auto [2]
    apply (rule Ex_I[where x="ORD_OF i"], simp)
    apply (rule Ex_I[where x="\<guillemotleft>ORD_OF i\<guillemotright>"], simp)
    apply (auto intro!: Disj_I1 WRP Mem_Eats_I2)
    done
qed

lemma SeqHRP_HPair:
  assumes "atom s \<sharp> (k,s1,s2,k1,k2,x,y,x',y')" "atom k \<sharp> (s1,s2,k1,k2,x,y,x',y')"
  shows "{SeqHRP x x' s1 k1,
            SeqHRP y y' s2 k2}
           \<turnstile> Ex s (Ex k (SeqHRP (HPair x y) (Q_HPair x' y') (Var s) (Var k)))" (*<*)
proof -
  let ?vs = "(s1,s2,s,k1,k2,k,x,y,x',y')"
  obtain km::name and kn::name and j::name and k'::name
    and l::name and sl::name and sl'::name and m::name and n::name
    and sm::name and sm'::name and sn::name and sn'::name
    where atoms2: "atom km \<sharp> (kn,j,k',l,s1,s2,s,k1,k2,k,x,y,x',y',sl,sl',m,n,sm,sm',sn,sn')"
      "atom kn \<sharp> (j,k',l,s1,s2,s,k1,k2,k,x,y,x',y',sl,sl',m,n,sm,sm',sn,sn')"
      "atom j \<sharp> (k',l,s1,s2,s,k1,k2,k,x,y,x',y',sl,sl',m,n,sm,sm',sn,sn')"
      and atoms: "atom k' \<sharp> (l,s1,s2,s,k1,k2,k,x,y,x',y',sl,sl',m,n,sm,sm',sn,sn')"
      "atom l \<sharp> (s1,s2,s,k1,k2,k,x,y,x',y',sl,sl',m,n,sm,sm',sn,sn')"
      "atom sl \<sharp> (s1,s2,s,k1,k2,k,x,y,x',y',sl',m,n,sm,sm',sn,sn')"
      "atom sl' \<sharp> (s1,s2,s,k1,k2,k,x,y,x',y',m,n,sm,sm',sn,sn')"
      "atom m \<sharp> (s1,s2,s,k1,k2,k,x,y,x',y',n,sm,sm',sn,sn')"
      "atom n \<sharp> (s1,s2,s,k1,k2,k,x,y,x',y',sm,sm',sn,sn')"
      "atom sm \<sharp> (s1,s2,s,k1,k2,k,x,y,x',y',sm',sn,sn')"
      "atom sm' \<sharp> (s1,s2,s,k1,k2,k,x,y,x',y',sn,sn')"
      "atom sn \<sharp> (s1,s2,s,k1,k2,k,x,y,x',y',sn')"
      "atom sn' \<sharp> (s1,s2,s,k1,k2,k,x,y,x',y')"
    by (metis obtain_fresh)
  let ?hyp = "{HaddP k1 k2 (Var k'), OrdP k1, OrdP k2, SeqAppendP s1 (SUCC k1) s2 (SUCC k2) (Var s),
               SeqHRP x x' s1 k1, SeqHRP y y' s2 k2}"
  show ?thesis
    using assms atoms
    apply (auto simp: SeqHRP.simps [of l "Var s" _ sl sl' m n sm sm' sn sn'])
    apply (rule cut_same [where A="OrdP k1 AND OrdP k2"])
     apply (metis Conj_I SeqHRP_imp_OrdP thin1 thin2)
    apply (rule cut_same [OF exists_SeqAppendP [of s s1 "SUCC k1" s2 "SUCC k2"]])
     apply (rule AssumeH Ex_EH Conj_EH | simp)+
      apply (rule cut_same [OF exists_HaddP [where j=k' and x=k1 and y=k2]])
        apply (rule AssumeH Ex_EH Conj_EH | simp)+
        apply (rule Ex_I [where x="Eats (Var s) (HPair (SUCC(SUCC(Var k'))) (HPair(HPair x y)(Q_HPair x' y')))"])
        apply (simp_all (no_asm_simp))
    apply (rule Ex_I [where x="SUCC (SUCC (Var k'))"], simp)
    apply (rule Conj_I)
     apply (blast intro: LstSeqP_SeqAppendP_Eats SeqHRP_imp_LstSeqP [THEN cut1])
  proof (rule All2_SUCC_I, simp_all)
    show "?hyp \<turnstile>     SyntaxN.Ex sl
     (SyntaxN.Ex sl'
       (HPair (SUCC (SUCC (Var k'))) (HPair (Var sl) (Var sl')) IN
        Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (HPair (HPair x y) (Q_HPair x' y'))) AND
        (OrdP (Var sl) AND WRP (Var sl) (Var sl') OR
         SyntaxN.Ex m
          (SyntaxN.Ex n
            (SyntaxN.Ex sm
              (SyntaxN.Ex sm'
                (SyntaxN.Ex sn
                  (SyntaxN.Ex sn'
                    (Var m IN SUCC (SUCC (Var k')) AND
                     Var n IN SUCC (SUCC (Var k')) AND
                     HPair (Var m) (HPair (Var sm) (Var sm')) IN
                     Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (HPair (HPair x y) (Q_HPair x' y'))) AND
                     HPair (Var n) (HPair (Var sn) (Var sn')) IN
                     Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (HPair (HPair x y) (Q_HPair x' y'))) AND
                     Var sl EQ HPair (Var sm) (Var sn) AND Var sl' EQ Q_HPair (Var sm') (Var sn'))))))))))"
      \<comment> \<open>verifying the final values\<close>
      apply (rule Ex_I [where x="HPair x y"])
      using assms atoms apply simp
      apply (rule Ex_I [where x="Q_HPair x' y'"], simp)
      apply (rule Conj_I, metis Mem_Eats_I2 Refl)
      apply (rule Disj_I2)
      apply (rule Ex_I [where x=k1], simp)
      apply (rule Ex_I [where x="SUCC (Var k')"], simp)
      apply (rule Ex_I [where x=x], simp)
      apply (rule_tac x=x' in Ex_I, simp)
      apply (rule Ex_I [where x=y], simp)
      apply (rule_tac x=y' in Ex_I, simp)
      apply (rule Conj_I)
       apply (blast intro: HaddP_Mem_I LstSeqP_OrdP Mem_SUCC_I1)
      apply (rule Conj_I [OF Mem_SUCC_Refl])
      apply (blast intro: Disj_I1 Mem_Eats_I1 Mem_SUCC_Refl SeqHRP_imp_LstSeqP [THEN cut1]
          LstSeqP_imp_Mem SeqAppendP_Mem1 [THEN cut3] SeqAppendP_Mem2 [THEN cut4] HaddP_SUCC1 [THEN cut1])
      done
  next
    show "?hyp \<turnstile>  All2 l (SUCC (SUCC (Var k')))
     (SyntaxN.Ex sl
       (SyntaxN.Ex sl'
         (HPair (Var l) (HPair (Var sl) (Var sl')) IN
          Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (HPair (HPair x y) (Q_HPair x' y'))) AND
          (OrdP (Var sl) AND WRP (Var sl) (Var sl') OR
           SyntaxN.Ex m
            (SyntaxN.Ex n
              (SyntaxN.Ex sm
                (SyntaxN.Ex sm'
                  (SyntaxN.Ex sn
                    (SyntaxN.Ex sn'
                      (Var m IN Var l AND
                       Var n IN Var l AND
                       HPair (Var m) (HPair (Var sm) (Var sm')) IN
                       Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (HPair (HPair x y) (Q_HPair x' y'))) AND
                       HPair (Var n) (HPair (Var sn) (Var sn')) IN
                       Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (HPair (HPair x y) (Q_HPair x' y'))) AND
                       Var sl EQ HPair (Var sm) (Var sn) AND Var sl' EQ Q_HPair (Var sm') (Var sn')))))))))))"
      \<comment> \<open>verifying the sequence buildup\<close>
      apply (rule cut_same [where A="HaddP (SUCC k1) (SUCC k2) (SUCC (SUCC (Var k')))"])
       apply (blast intro: HaddP_SUCC1 [THEN cut1] HaddP_SUCC2 [THEN cut1])
      apply (rule All_I Imp_I)+
       apply (rule HaddP_Mem_cases [where i=j])
      using assms atoms atoms2 apply simp_all
          apply (rule AssumeH)
         apply (blast intro: OrdP_SUCC_I LstSeqP_OrdP)
        \<comment> \<open>... the sequence buildup via s1\<close>
        apply (simp add: SeqHRP.simps [of l s1 _ sl sl' m n sm sm' sn sn'])
        apply (rule AssumeH Ex_EH Conj_EH)+
        apply (rule All2_E [THEN rotate2])
          apply (simp | rule AssumeH Ex_EH Conj_EH)+
            apply (rule Ex_I [where x="Var sl"], simp)
            apply (rule Ex_I [where x="Var sl'"], simp)
            apply (rule Conj_I [OF Mem_Eats_I1])
             apply (metis SeqAppendP_Mem1 rotate3 thin2 thin4)
            apply (rule AssumeH Disj_IE1H Ex_EH Conj_EH)+
                        apply (rule Ex_I [where x="Var m"], simp)
                        apply (rule Ex_I [where x="Var n"], simp)
                        apply (rule Ex_I [where x="Var sm"], simp)
                        apply (rule Ex_I [where x="Var sm'"], simp)
                        apply (rule Ex_I [where x="Var sn"], simp)
                        apply (rule Ex_I [where x="Var sn'"], simp_all (no_asm_simp))
       apply (rule Conj_I, rule AssumeH)+
       apply (rule Conj_I)
        apply (blast intro: OrdP_Trans [OF OrdP_SUCC_I] Mem_Eats_I1 [OF SeqAppendP_Mem1 [THEN cut3]] Hyp)
       apply (blast intro: Disj_I1 Disj_I2 OrdP_Trans [OF OrdP_SUCC_I] Mem_Eats_I1 [OF SeqAppendP_Mem1 [THEN cut3]] Hyp)
        \<comment> \<open>... the sequence buildup via s2\<close>
      apply (simp add: SeqHRP.simps [of l s2 _ sl sl' m n sm sm' sn sn'])
      apply (rule AssumeH Ex_EH Conj_EH)+
      apply (rule All2_E [THEN rotate2])
        apply (simp | rule AssumeH Ex_EH Conj_EH)+
          apply (rule Ex_I [where x="Var sl"], simp)
          apply (rule Ex_I [where x="Var sl'"], simp)
          apply (rule cut_same [where A="OrdP (Var j)"])
           apply (metis HaddP_imp_OrdP rotate2 thin2)
          apply (rule Conj_I)
           apply (blast intro: Mem_Eats_I1 SeqAppendP_Mem2 [THEN cut4] del: Disj_EH)
          apply (rule AssumeH Disj_IE1H Ex_EH Conj_EH)+
                      apply (rule cut_same [OF exists_HaddP [where j=km and x="SUCC k1" and y="Var m"]])
                        apply (blast intro: Ord_IN_Ord, simp)
                      apply (rule cut_same [OF exists_HaddP [where j=kn and x="SUCC k1" and y="Var n"]])
                        apply (metis AssumeH(6) Ord_IN_Ord0 rotate8, simp)
                      apply (rule AssumeH Ex_EH Conj_EH | simp)+
                          apply (rule Ex_I [where x="Var km"], simp)
                          apply (rule Ex_I [where x="Var kn"], simp)
                          apply (rule Ex_I [where x="Var sm"], simp)
                          apply (rule Ex_I [where x="Var sm'"], simp)
                          apply (rule Ex_I [where x="Var sn"], simp)
                          apply (rule Ex_I [where x="Var sn'"], simp_all (no_asm_simp))
      apply (rule Conj_I [OF _ Conj_I])
        apply (blast intro!: HaddP_Mem_cancel_left [THEN Iff_MP2_same] OrdP_SUCC_I intro: LstSeqP_OrdP Hyp)+
      apply (blast del: Disj_EH  intro: OrdP_Trans Hyp
          intro!: Mem_Eats_I1 SeqAppendP_Mem2 [THEN cut4] HaddP_imp_OrdP [THEN cut1])
      done
  qed
qed (*>*)

lemma HRP_HPair: "{HRP x x', HRP y y'} \<turnstile> HRP (HPair x y) (Q_HPair x' y')"
proof -
  obtain k1::name and s1::name and k2::name and s2::name and k::name and s::name
    where "atom s1 \<sharp> (x,y,x',y')"        "atom k1 \<sharp> (x,y,x',y',s1)"
      "atom s2 \<sharp> (x,y,x',y',k1,s1)"  "atom k2 \<sharp> (x,y,x',y',s2,k1,s1)"
      "atom s  \<sharp> (x,y,x',y',k2,s2,k1,s1)" "atom k  \<sharp> (x,y,x',y',s,k2,s2,k1,s1)"
    by (metis obtain_fresh)
  thus ?thesis
    by (force simp: HRP.simps [of s "HPair x y" _ k]
        HRP.simps [of s1 x _ k1]
        HRP.simps [of s2 y _ k2]
        intro: SeqHRP_HPair [THEN cut2])
qed

lemma HRP_HPair_quot: "{HRP x \<guillemotleft>x\<guillemotright>, HRP y \<guillemotleft>y\<guillemotright>} \<turnstile> HRP (HPair x y) \<guillemotleft>HPair x y\<guillemotright>"
  using HRP_HPair[of x "\<guillemotleft>x\<guillemotright>" y "\<guillemotleft>y\<guillemotright>"]
  unfolding HPair_def quot_simps by auto

lemma prove_HRP_coding_tm: fixes t::tm shows "coding_tm t \<Longrightarrow> {} \<turnstile> HRP t \<guillemotleft>t\<guillemotright>"
  by (induct t rule: coding_tm.induct)
    (auto simp: quot_simps HRP_ORD_OF HRP_HPair_quot[THEN cut2])

lemmas prove_HRP = prove_HRP_coding_tm[OF quot_fm_coding]

section\<open>The Function K and Lemma 6.3\<close>

nominal_function KRP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "atom y \<sharp> (v,x,x') \<Longrightarrow>
         KRP v x x' = Ex y (HRP x (Var y) AND SubstFormP v (Var y) x x')"
  by (auto simp: eqvt_def KRP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma KRP_fresh_iff [simp]: "a \<sharp> KRP v x x' \<longleftrightarrow> a \<sharp> v \<and> a \<sharp> x \<and> a \<sharp> x'"
proof -
  obtain y::name where "atom y \<sharp> (v,x,x')"
    by (metis obtain_fresh)
  thus ?thesis
    by auto
qed

lemma KRP_subst [simp]: "(KRP v x x')(i::=t) = KRP (subst i t v) (subst i t x) (subst i t x')"
proof -
  obtain y::name where "atom y \<sharp> (v,x,x',t,i)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: KRP.simps [of y])
qed

declare KRP.simps [simp del]

lemma prove_SubstFormP: "{} \<turnstile> SubstFormP \<guillemotleft>Var i\<guillemotright> \<guillemotleft>\<guillemotleft>A\<guillemotright>\<guillemotright> \<guillemotleft>A\<guillemotright> \<guillemotleft>A(i::=\<guillemotleft>A\<guillemotright>)\<guillemotright>"
  using SubstFormP by blast

lemma prove_KRP: "{} \<turnstile> KRP \<guillemotleft>Var i\<guillemotright> \<guillemotleft>A\<guillemotright> \<guillemotleft>A(i::=\<guillemotleft>A\<guillemotright>)\<guillemotright>"
  by (auto simp: KRP.simps [of y]
           intro!: Ex_I [where x="\<guillemotleft>\<guillemotleft>A\<guillemotright>\<guillemotright>"] prove_HRP prove_SubstFormP)

lemma KRP_unique: "{KRP v x y, KRP v x y'} \<turnstile> y' EQ y"
proof -
  obtain u::name and u'::name where "atom u \<sharp> (v,x,y,y')" "atom u' \<sharp> (v,x,y,y',u)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: KRP.simps [of u v x y] KRP.simps [of u' v x y']
             intro: SubstFormP_cong [THEN Iff_MP2_same]
                    SubstFormP_unique [THEN cut2] HRP_unique [THEN cut2])
qed

lemma KRP_subst_fm: "{KRP \<guillemotleft>Var i\<guillemotright> \<guillemotleft>\<beta>\<guillemotright> (Var j)} \<turnstile> Var j EQ \<guillemotleft>\<beta>(i::=\<guillemotleft>\<beta>\<guillemotright>)\<guillemotright>"
  by (metis KRP_unique cut0 prove_KRP)

end

