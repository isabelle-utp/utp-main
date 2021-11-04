chapter\<open>Formalizing Provability\<close>

theory Pf_Predicates
imports Coding_Predicates
begin

section \<open>Section 4 Predicates (Leading up to Pf)\<close>

subsection \<open>The predicate \<open>SentP\<close>, for the Sentiential (Boolean) Axioms\<close>

nominal_function SentP :: "tm \<Rightarrow> fm"
  where "\<lbrakk>atom y \<sharp> (z,w,x); atom z \<sharp> (w,x); atom w \<sharp> x\<rbrakk> \<Longrightarrow>
    SentP x = Ex y (Ex z (Ex w (FormP (Var y) AND FormP (Var z) AND FormP (Var w) AND
               ( (x EQ Q_Imp (Var y) (Var y)) OR
                 (x EQ Q_Imp (Var y) (Q_Disj (Var y) (Var z)) OR
                 (x EQ Q_Imp (Q_Disj (Var y) (Var y)) (Var y)) OR
                 (x EQ Q_Imp (Q_Disj (Var y) (Q_Disj (Var z) (Var w)))
                             (Q_Disj (Q_Disj (Var y) (Var z)) (Var w))) OR
                 (x EQ Q_Imp (Q_Disj (Var y) (Var z))
                             (Q_Imp (Q_Disj (Q_Neg (Var y)) (Var w)) (Q_Disj (Var z) (Var w)))))))))"
  by (auto simp: eqvt_def SentP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
 shows SentP_fresh_iff [simp]: "a \<sharp> SentP x \<longleftrightarrow> a \<sharp> x"                  (is ?thesis1)
   and SentP_sf [iff]:         "Sigma_fm (SentP x)"                     (is ?thsf)
proof -
  obtain y::name and z::name and w::name  where "atom y \<sharp> (z,w,x)" "atom z \<sharp> (w,x)" "atom w \<sharp> x"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf
    by auto
qed

subsection \<open>The predicate \<open>Equality_axP\<close>, for the Equality Axioms\<close>

function Equality_axP :: "tm \<Rightarrow> fm"
  where "Equality_axP x =
    x EQ \<guillemotleft>refl_ax\<guillemotright> OR x EQ \<guillemotleft>eq_cong_ax\<guillemotright> OR x EQ \<guillemotleft>mem_cong_ax\<guillemotright> OR x EQ \<guillemotleft>eats_cong_ax\<guillemotright>"
by auto

termination
  by lexicographic_order

subsection \<open>The predicate \<open>HF_axP\<close>, for the HF Axioms\<close>

function HF_axP :: "tm \<Rightarrow> fm"
  where "HF_axP x = x EQ \<guillemotleft>HF1\<guillemotright> OR x EQ \<guillemotleft>HF2\<guillemotright>"
by auto

termination
  by lexicographic_order

lemma HF_axP_sf [iff]: "Sigma_fm (HF_axP t)"
  by auto


subsection \<open>The specialisation axioms\<close>

subsubsection \<open>Defining the syntax\<close>

nominal_function Special_axP :: "tm \<Rightarrow> fm" where
  "\<lbrakk>atom v \<sharp> (p,sx,y,ax,x); atom x \<sharp> (p,sx,y,ax);
    atom ax \<sharp> (p,sx,y); atom y \<sharp> (p,sx); atom sx \<sharp> p\<rbrakk> \<Longrightarrow>
  Special_axP p = Ex v (Ex x (Ex ax (Ex y (Ex sx
                   (FormP (Var x) AND VarP (Var v) AND TermP (Var y) AND
                    AbstFormP (Var v) Zero (Var x) (Var ax) AND
                    SubstFormP (Var v) (Var y) (Var x) (Var sx) AND
                    p EQ Q_Imp (Var sx) (Q_Ex (Var ax)))))))"
  by (auto simp: eqvt_def Special_axP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
 shows Special_axP_fresh_iff [simp]: "a \<sharp> Special_axP p \<longleftrightarrow> a \<sharp> p" (is ?thesis1)
   and Special_axP_sf [iff]:       "Sigma_fm (Special_axP p)" (is ?thesis3)
proof -
  obtain v::name and x::name and ax::name and y::name and sx::name
    where "atom v \<sharp> (p,sx,y,ax,x)" "atom x \<sharp> (p,sx,y,ax)"
          "atom ax \<sharp> (p,sx,y)" "atom y \<sharp> (p,sx)" "atom sx \<sharp> p"
    by (metis obtain_fresh)
  thus ?thesis1 ?thesis3
    by auto
qed

subsection \<open>The induction axioms\<close>

subsubsection \<open>Defining the syntax\<close>

nominal_function Induction_axP :: "tm \<Rightarrow> fm" where
  "\<lbrakk>atom ax \<sharp> (p,v,w,x,x0,xw,xevw,allw,allvw);
    atom allvw \<sharp> (p,v,w,x,x0,xw,xevw,allw); atom allw \<sharp> (p,v,w,x,x0,xw,xevw);
    atom xevw \<sharp> (p,v,w,x,x0,xw); atom xw \<sharp> (p,v,w,x,x0);
    atom x0 \<sharp> (p,v,w,x); atom x \<sharp> (p,v,w);
    atom w \<sharp> (p,v); atom v \<sharp> p\<rbrakk> \<Longrightarrow>
  Induction_axP p = Ex v (Ex w (Ex x (Ex x0 (Ex xw (Ex xevw (Ex allw (Ex allvw (Ex ax
               ((Var v NEQ Var w) AND VarNonOccFormP (Var w) (Var x) AND
                SubstFormP (Var v) Zero (Var x) (Var x0) AND
                SubstFormP (Var v) (Var w) (Var x) (Var xw) AND
                SubstFormP (Var v) (Q_Eats (Var v) (Var w)) (Var x) (Var xevw) AND
                AbstFormP (Var w) Zero (Q_Imp (Var x) (Q_Imp (Var xw) (Var xevw))) (Var allw) AND
                AbstFormP (Var v) Zero (Q_All (Var allw)) (Var allvw) AND
                AbstFormP (Var v) Zero (Var x) (Var ax) AND
                p EQ Q_Imp (Var x0) (Q_Imp (Q_All (Var allvw)) (Q_All (Var ax))))))))))))"
  by (auto simp: eqvt_def Induction_axP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
 shows Induction_axP_fresh_iff [simp]: "a \<sharp> Induction_axP p \<longleftrightarrow> a \<sharp> p" (is ?thesis1)
   and Induction_axP_sf [iff]: "Sigma_fm (Induction_axP p)" (is ?thesis3)
proof -
  obtain v::name and w::name and x::name and x0::name and xw::name and xevw::name
                 and allw::name and allvw::name and ax::name
    where atoms: "atom ax \<sharp> (p,v,w,x,x0,xw,xevw,allw,allvw)"
                 "atom allvw \<sharp> (p,v,w,x,x0,xw,xevw,allw)" "atom allw \<sharp> (p,v,w,x,x0,xw,xevw)"
                 "atom xevw \<sharp> (p,v,w,x,x0,xw)" "atom xw \<sharp> (p,v,w,x,x0)" "atom x0 \<sharp> (p,v,w,x)"
                 "atom x \<sharp> (p,v,w)" "atom w \<sharp> (p,v)" "atom v \<sharp> p"
    by (metis obtain_fresh)
  thus ?thesis1 ?thesis3
    by auto
qed

subsection \<open>The predicate \<open>AxiomP\<close>, for any Axioms\<close>

definition AxiomP :: "tm \<Rightarrow> fm"
  where "AxiomP x \<equiv> x EQ \<guillemotleft>extra_axiom\<guillemotright> OR SentP x OR Equality_axP x OR
                    HF_axP x OR Special_axP x OR Induction_axP x"

lemma AxiomP_I:
  "{} \<turnstile> AxiomP \<guillemotleft>extra_axiom\<guillemotright>"
  "{} \<turnstile> SentP x \<Longrightarrow> {} \<turnstile> AxiomP x"
  "{} \<turnstile> Equality_axP x \<Longrightarrow> {} \<turnstile> AxiomP x"
  "{} \<turnstile> HF_axP x \<Longrightarrow> {} \<turnstile> AxiomP x"
  "{} \<turnstile> Special_axP x \<Longrightarrow> {} \<turnstile> AxiomP x"
  "{} \<turnstile> Induction_axP x \<Longrightarrow> {} \<turnstile> AxiomP x"
  unfolding AxiomP_def
  by (rule Disj_I1, rule Refl,
      rule Disj_I2, rule Disj_I1, assumption,
      rule Disj_I2, rule Disj_I2, rule Disj_I1, assumption,
      rule Disj_I2, rule Disj_I2, rule Disj_I2, rule Disj_I1, assumption,
      rule Disj_I2, rule Disj_I2, rule Disj_I2, rule Disj_I2, rule Disj_I1, assumption,
      rule Disj_I2, rule Disj_I2, rule Disj_I2, rule Disj_I2, rule Disj_I2, assumption)

lemma AxiomP_eqvt [eqvt]: "(p \<bullet> AxiomP x) = AxiomP (p \<bullet> x)"
  by (simp add: AxiomP_def)

lemma AxiomP_fresh_iff [simp]: "a \<sharp> AxiomP x \<longleftrightarrow> a \<sharp> x"
  by (auto simp: AxiomP_def)

lemma AxiomP_sf [iff]: "Sigma_fm (AxiomP t)"
  by (auto simp: AxiomP_def)


subsection \<open>The predicate \<open>ModPonP\<close>, for the inference rule Modus Ponens\<close>

definition ModPonP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "ModPonP x y z = (y EQ Q_Imp x z)"

lemma ModPonP_eqvt [eqvt]: "(p \<bullet> ModPonP x y z) = ModPonP (p \<bullet> x) (p \<bullet> y) (p \<bullet> z)"
  by (simp add: ModPonP_def)

lemma ModPonP_fresh_iff [simp]: "a \<sharp> ModPonP x y z \<longleftrightarrow> a \<sharp> x \<and> a \<sharp> y \<and> a \<sharp> z"
  by (auto simp: ModPonP_def)

lemma ModPonP_sf [iff]: "Sigma_fm (ModPonP t u v)"
  by (auto simp: ModPonP_def)

lemma ModPonP_subst [simp]:
  "(ModPonP t u v)(i::=w) = ModPonP (subst i w t) (subst i w u) (subst i w v)"
  by (auto simp: ModPonP_def)


subsection \<open>The predicate \<open>ExistsP\<close>, for the existential rule\<close>
subsubsection \<open>Definition\<close>

(*  "\<turnstile> A IMP B \<Longrightarrow> atom i \<sharp> B \<Longrightarrow>  \<turnstile> (Ex i A) IMP B" *)
nominal_function ExistsP :: "tm \<Rightarrow> tm \<Rightarrow> fm" where
  "\<lbrakk>atom x \<sharp> (p,q,v,y,x'); atom x' \<sharp> (p,q,v,y);
    atom y \<sharp> (p,q,v); atom v \<sharp> (p,q)\<rbrakk> \<Longrightarrow>
  ExistsP p q = Ex x (Ex x' (Ex y (Ex v (FormP (Var x) AND
                    VarNonOccFormP (Var v) (Var y) AND
                    AbstFormP (Var v) Zero (Var x) (Var x') AND
                    p EQ Q_Imp (Var x) (Var y) AND
                    q EQ Q_Imp (Q_Ex (Var x')) (Var y)))))"
  by (auto simp: eqvt_def ExistsP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
 shows ExistsP_fresh_iff [simp]: "a \<sharp> ExistsP p q \<longleftrightarrow> a \<sharp> p \<and> a \<sharp> q"    (is ?thesis1)
   and ExistsP_sf [iff]:       "Sigma_fm (ExistsP p q)"   (is ?thesis3)
proof -
  obtain x::name and x'::name and y::name and v::name
    where "atom x \<sharp> (p,q,v,y,x')"  "atom x' \<sharp> (p,q,v,y)" "atom y \<sharp> (p,q,v)"  "atom v \<sharp> (p,q)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thesis3
    by auto
qed

lemma ExistsP_subst [simp]: "(ExistsP p q)(j::=w) = ExistsP (subst j w p) (subst j w q)"
proof -
  obtain x::name and x'::name and y::name and v::name
    where "atom x \<sharp> (j,w,p,q,v,y,x')"   "atom x' \<sharp> (j,w,p,q,v,y)"
          "atom y \<sharp> (j,w,p,q,v)"   "atom v \<sharp> (j,w,p,q)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: ExistsP.simps [of x _ _ x' y v])
qed

subsection \<open>The predicate \<open>SubstP\<close>, for the substitution rule\<close>

text\<open>Although the substitution rule is derivable in the calculus, the derivation is
too complicated to reproduce within the proof function. It is much easier to
provide it as an immediate inference step, justifying its soundness in terms
of other inference rules.\<close>

subsubsection \<open>Definition\<close>

nominal_function SubstP :: "tm \<Rightarrow> tm \<Rightarrow> fm" where
  "\<lbrakk>atom u \<sharp> (p,q,v); atom v \<sharp> (p,q)\<rbrakk> \<Longrightarrow>
   SubstP p q = Ex v (Ex u (SubstFormP (Var v) (Var u) p q))"
  by (auto simp: eqvt_def SubstP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
 shows SubstP_fresh_iff [simp]: "a \<sharp> SubstP p q \<longleftrightarrow> a \<sharp> p \<and> a \<sharp> q"        (is ?thesis1)
   and SubstP_sf [iff]: "Sigma_fm (SubstP p q)"                           (is ?thesis3)
proof -
  obtain u::name and v::name  where "atom u \<sharp> (p,q,v)" "atom v \<sharp> (p,q)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thesis3
    by auto
qed

lemma SubstP_subst [simp]: "(SubstP p q)(j::=w) = SubstP (subst j w p) (subst j w q)"
proof -
  obtain u::name and v::name  where "atom u \<sharp> (j,w,p,q,v)"  "atom v \<sharp> (j,w,p,q)"
    by (metis obtain_fresh)
  thus ?thesis
    by (simp add: SubstP.simps [of u _ _ v])
qed


subsection \<open>The predicate \<open>PrfP\<close>\<close>

(*Prf(s,k,t) \<equiv> LstSeq(s,k,t) \<and> (\<forall>n\<in>k)[Sent (s n) \<or> (\<exists>m,l\<in>n)[ModPon (s m) (s l) (s n)]]*)
nominal_function PrfP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom l \<sharp> (s,sl,m,n,sm,sn); atom sl \<sharp> (s,m,n,sm,sn);
          atom m \<sharp> (s,n,sm,sn); atom n \<sharp> (s,k,sm,sn);
          atom sm \<sharp> (s,sn); atom sn \<sharp> (s)\<rbrakk> \<Longrightarrow>
    PrfP s k t =
      LstSeqP s k t AND
      All2 n (SUCC k) (Ex sn (HPair (Var n) (Var sn) IN s AND (AxiomP (Var sn) OR
                Ex m (Ex l (Ex sm (Ex sl (Var m IN Var n AND Var l IN Var n AND
                       HPair (Var m) (Var sm) IN s AND HPair (Var l) (Var sl) IN s AND
                       (ModPonP (Var sm) (Var sl) (Var sn) OR
                        ExistsP (Var sm) (Var sn) OR
                        SubstP (Var sm) (Var sn)))))))))"
  by (auto simp: eqvt_def PrfP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows PrfP_fresh_iff [simp]: "a \<sharp> PrfP s k t \<longleftrightarrow> a \<sharp> s \<and> a \<sharp> k \<and> a \<sharp> t"      (is ?thesis1)
  and PrfP_imp_OrdP [simp]:    "{PrfP s k t} \<turnstile> OrdP k"         (is ?thord)
  and PrfP_imp_LstSeqP [simp]: "{PrfP s k t} \<turnstile> LstSeqP s k t"  (is ?thlstseq)
  and PrfP_sf [iff]:           "Sigma_fm (PrfP s k t)"         (is ?thsf)
proof -
  obtain l::name and sl::name and m::name and n::name and sm::name and sn::name
    where atoms: "atom l \<sharp> (s,sl,m,n,sm,sn)"   "atom sl \<sharp> (s,m,n,sm,sn)"
        "atom m \<sharp> (s,n,sm,sn)"   "atom n \<sharp> (s,k,sm,sn)"
        "atom sm \<sharp> (s,sn)"   "atom sn \<sharp> (s)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thord ?thlstseq ?thsf
    by (auto intro: LstSeqP_OrdP)
qed

lemma PrfP_subst [simp]:
     "(PrfP t u v)(j::=w) = PrfP (subst j w t) (subst j w u) (subst j w v)"
proof -
  obtain l::name and sl::name and m::name and n::name and sm::name and sn::name
    where "atom l \<sharp> (t,u,v,j,w,sl,m,n,sm,sn)"   "atom sl \<sharp> (t,u,v,j,w,m,n,sm,sn)"
          "atom m \<sharp> (t,u,v,j,w,n,sm,sn)"   "atom n \<sharp> (t,u,v,j,w,sm,sn)"
          "atom sm \<sharp> (t,u,v,j,w,sn)"   "atom sn \<sharp> (t,u,v,j,w)"
    by (metis obtain_fresh)
  thus ?thesis
    by (simp add: PrfP.simps [of l _ sl m n sm sn])
qed


subsection \<open>The predicate \<open>PfP\<close>\<close>

nominal_function PfP :: "tm \<Rightarrow> fm"
  where "\<lbrakk>atom k \<sharp> (s,y); atom s \<sharp> y\<rbrakk> \<Longrightarrow>
    PfP y = Ex k (Ex s (PrfP (Var s) (Var k) y))"
  by (auto simp: eqvt_def PfP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
 shows PfP_fresh_iff [simp]: "a \<sharp> PfP y \<longleftrightarrow> a \<sharp> y"           (is ?thesis1)
   and PfP_sf [iff]: "Sigma_fm (PfP y)"                      (is ?thsf)
proof -
  obtain k::name and s::name where "atom k \<sharp> (s,y)" "atom s \<sharp> y"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf
    by auto
qed

lemma PfP_subst [simp]: "(PfP t)(j::=w) = PfP (subst j w t)"
proof -
  obtain k::name and s::name where "atom k \<sharp> (s,t,j,w)" "atom s \<sharp> (t,j,w)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: PfP.simps [of k s])
qed

lemma ground_PfP [simp]: "ground_fm (PfP y) = ground y"
  by (simp add: ground_aux_def ground_fm_aux_def supp_conv_fresh)

end

