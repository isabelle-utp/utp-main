chapter \<open>Rosser Formulas\<close>

text \<open>The Rosser formula is a modification of the Gödel formula that
is undecidable assuming consistency only (not $\omega$-consistency).\<close>

(*<*)
theory Rosser_Formula
  imports Diagonalization Goedel_Formula
begin
(*>*)

locale Rosser_Form =
Deduct2_with_PseudoOrder
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
  prv bprv
  Lq
  +
Repr_Neg
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  num
  prv bprv
  enc
  N
  +
Repr_SelfSubst
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi
  prv bprv
  enc
  S
  +
HBL1
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi
  prv bprv
  enc
  P
  for
    var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
    and Var FvarsT substT Fvars subst
    and num
    and eql cnj imp all exi
    and fls
    and prv bprv
    and Lq
    and dsj
    and enc ("\<langle>_\<rangle>")
    and N S P


locale Rosser_Form_Proofs =
Deduct2_with_PseudoOrder
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
  prv bprv
  Lq
  +
Repr_Neg
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  num
  prv bprv
  enc
  N
  +
Repr_SelfSubst
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi
  prv bprv
  enc
  S
  +
CleanRepr_Proofs
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi
  prv bprv
  enc
  fls
  dsj
  "proof" prfOf
  encPf
  Pf
  for
    var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
    and Var FvarsT substT Fvars subst
    and num
    and eql cnj imp all exi
    and fls
    and prv bprv
    and Lq
    and dsj and "proof" :: "'proof set" and prfOf
    and enc ("\<langle>_\<rangle>")
    and N
    and S
    and encPf Pf

context Rosser_Form_Proofs
begin

definition R where "R = all zz (imp (LLq (Var zz) (Var yy))
                                     (all xx' (imp (NN (Var xx) (Var xx'))
                                                   (neg (PPf (Var zz) (Var xx'))))))"

definition RR where "RR t1 t2 = psubst R [(t1,yy), (t2,xx)]"

lemma R[simp,intro!]: "R \<in> fmla" unfolding R_def by auto

lemma RR_def2:
  "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> xx \<notin> FvarsT t1 \<Longrightarrow> RR t1 t2 = subst (subst R t1 yy) t2 xx"
  unfolding RR_def by (rule psubst_eq_rawpsubst2[simplified]) auto

definition P' where "P' = exi yy (cnj (PPf (Var yy) (Var xx)) (RR (Var yy) (Var xx)))"

definition PP' where "PP' t = subst P' t xx"

lemma Fvars_R[simp]: "Fvars R = {xx,yy}" unfolding R_def by auto

lemma [simp]: "Fvars (RR (Var yy) (Var xx)) = {yy,xx}" by (auto simp: RR_def2)

lemma P'[simp,intro!]: "P' \<in> fmla" unfolding P'_def by (auto simp: PPf_def2 RR_def2)

lemma Fvars_P'[simp]: "Fvars P' = {xx}" unfolding P'_def by (auto simp: PPf_def2 RR_def2)

lemma PP'[simp,intro!]: "t \<in> trm \<Longrightarrow> PP' t \<in> fmla"
  unfolding PP'_def by auto

lemma RR[simp,intro]: "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> RR t1 t2 \<in> fmla"
  by (auto simp: RR_def)

lemma RR_simps[simp]:
   "n \<in> num \<Longrightarrow> subst (RR (Var yy) (Var xx)) n xx = RR (Var yy) n"
   "m \<in> num \<Longrightarrow> n \<in> num \<Longrightarrow> subst (RR (Var yy) m) n yy = RR n m"
  by (simp add: RR_def2 subst2_fresh_switch)+


text \<open>The Rosser modification of the Gödel formula\<close>
definition \<phi>R :: 'fmla where "\<phi>R \<equiv> diag (neg P')"

lemma \<phi>R[simp,intro!]: "\<phi>R \<in> fmla" and Fvars_\<phi>R[simp]: "Fvars \<phi>R = {}"
  unfolding \<phi>R_def wrepr.PP_def by auto

lemma bprv_\<phi>R_eqv:
  "bprv (eqv \<phi>R (neg (PP' \<langle>\<phi>R\<rangle>)))"
  unfolding \<phi>R_def PP'_def using bprv_diag_eqv[of "neg P'"] by simp

lemma bprv_imp_\<phi>R:
  "bprv (imp (neg (PP' \<langle>\<phi>R\<rangle>)) \<phi>R)"
  by (rule B.prv_imp_eqvER) (auto intro: bprv_\<phi>R_eqv)

lemma prv_\<phi>R_eqv:
  "prv (eqv \<phi>R (neg (PP' \<langle>\<phi>R\<rangle>)))"
  using dwf_dwfd.d_dwf.bprv_prv'[OF _ bprv_\<phi>R_eqv, simplified] .

lemma prv_imp_\<phi>R:
  "prv (imp (neg (PP' \<langle>\<phi>R\<rangle>)) \<phi>R)"
  by (rule prv_imp_eqvER) (auto intro: prv_\<phi>R_eqv)

end \<comment> \<open>context @{locale Rosser_Form}\<close>


sublocale Rosser_Form_Proofs < Rosser_Form where P = P
  by standard

sublocale Rosser_Form_Proofs < Goedel_Form where P = P
  by standard

(*<*)
end
(*>*)
