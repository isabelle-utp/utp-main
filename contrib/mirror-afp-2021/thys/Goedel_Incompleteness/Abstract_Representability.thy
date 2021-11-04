chapter \<open>Representability Assumptions\<close>

(*<*)
theory Abstract_Representability imports Abstract_Encoding
begin
(*>*)

text \<open>Here we make assumptions about various functions or relations being
representable.\<close>


section \<open>Representability of Negation\<close>

text \<open>The negation function neg is assumed to be representable by a
two-variable formula N.\<close>

locale Repr_Neg =
Deduct2_with_False
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  num
  prv bprv
+
Encode
  var trm fmla Var FvarsT substT Fvars subst
  num
  enc
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and eql cnj imp all exi
and fls
and num
and prv bprv
and enc ("\<langle>_\<rangle>")
+
fixes N :: 'fmla
assumes
N[simp,intro!]: "N \<in> fmla"
and
Fvars_N[simp]: "Fvars N = {xx,yy}"
and
neg_implies_prv_N:
"\<And> \<phi>.
  let NN = (\<lambda> t1 t2. psubst N [(t1,xx), (t2,yy)]) in
   \<phi> \<in> fmla \<longrightarrow> Fvars \<phi> = {} \<longrightarrow> bprv (NN \<langle>\<phi>\<rangle> \<langle>neg \<phi>\<rangle>)"
and
N_unique:
"\<And> \<phi>.
  let NN = (\<lambda> t1 t2. psubst N [(t1,xx), (t2,yy)]) in
  \<phi> \<in> fmla \<longrightarrow> Fvars \<phi> = {} \<longrightarrow>
  bprv (all yy (all yy'
    (imp (cnj (NN \<langle>\<phi>\<rangle> (Var yy)) (NN \<langle>\<phi>\<rangle> (Var yy')))
         (eql (Var yy) (Var yy')))))"
begin

text \<open>NN is a notation for the predicate that takes terms and returns corresponding instances
of N, obtained by substituting its free variables with these terms. This is very convenient
for reasoning, and will be done for all the representing formulas we will consider.\<close>

definition NN where "NN \<equiv> \<lambda> t1 t2. psubst N [(t1,xx), (t2,yy)]"

lemma NN_def2: "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> yy \<notin> FvarsT t1 \<Longrightarrow>
 NN t1 t2 = subst (subst N t1 xx) t2 yy"
  unfolding NN_def by (rule psubst_eq_rawpsubst2[simplified]) auto

lemma NN_neg:
"\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> bprv (NN \<langle>\<phi>\<rangle> \<langle>neg \<phi>\<rangle>)"
  using neg_implies_prv_N unfolding Let_def NN_def by meson

lemma NN_unique:
  assumes "\<phi> \<in> fmla" "Fvars \<phi> = {}"
  shows "bprv (all yy (all yy'
    (imp (cnj (NN \<langle>\<phi>\<rangle> (Var yy)) (NN \<langle>\<phi>\<rangle> (Var yy')))
         (eql (Var yy) (Var yy')))))"
  using assms N_unique unfolding Let_def NN_def by meson

lemma NN[simp,intro]:
"t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> NN t1 t2 \<in> fmla"
unfolding NN_def by auto

lemma Fvars_NN[simp]: "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> yy \<notin> FvarsT t1 \<Longrightarrow>
Fvars (NN t1 t2) = FvarsT t1 \<union> FvarsT t2"
by (auto simp add: NN_def2 subst2_fresh_switch)

(* Here and elsewhere: hard to make into one or two uniform statements,
given that we don't assume sufficiently powerful properties for trm substitution.
So such lists would need to be maintained on an ad hoc basis, keeping adding instances
when needed. *)
lemma [simp]:
"m \<in> num \<Longrightarrow> n \<in> num \<Longrightarrow> subst (NN m (Var yy)) n yy = NN m n"
"m \<in> num \<Longrightarrow> n \<in> num \<Longrightarrow> subst (NN m (Var yy')) n yy = NN m (Var yy')"
"m \<in> num \<Longrightarrow> subst (NN m (Var yy')) (Var yy) yy' = NN m (Var yy)"
"n \<in> num \<Longrightarrow> subst (NN (Var xx) (Var yy)) n xx = NN n (Var yy)"
"n \<in> num \<Longrightarrow> subst (NN (Var xx) (Var xx')) n xx = NN n (Var xx')"
"m \<in> num \<Longrightarrow> n \<in> num \<Longrightarrow> subst (NN m (Var xx')) n zz = NN m (Var xx')"
"n \<in> num \<Longrightarrow> subst (NN n (Var yy)) (Var xx') yy = NN n (Var xx')"
"m \<in> num \<Longrightarrow> n \<in> num \<Longrightarrow> subst (NN m (Var xx')) n xx' = NN m n"
  by (auto simp add: NN_def2 subst2_fresh_switch)

lemma NN_unique2:
assumes [simp]:"\<phi> \<in> fmla" "Fvars \<phi> = {}"
shows
"bprv (all yy
     (imp (NN \<langle>\<phi>\<rangle> (Var yy))
          (eql \<langle>neg \<phi>\<rangle> (Var yy))))"
proof-
  have 1: "bprv (NN \<langle>\<phi>\<rangle> \<langle>neg \<phi>\<rangle>)"
    using NN_neg[OF assms] .
  have 2: "bprv (all yy' (
             imp (cnj (NN \<langle>\<phi>\<rangle> \<langle>neg \<phi>\<rangle>)
                      (NN \<langle>\<phi>\<rangle> (Var yy')))
                 (eql \<langle>neg \<phi>\<rangle> (Var yy'))))"
    using B.prv_allE[of yy, OF _ _ _ NN_unique, of "\<phi>" "\<langle>neg \<phi>\<rangle>"]
    by fastforce
  have 31: "bprv (all yy' (
             imp (NN \<langle>\<phi>\<rangle> \<langle>neg \<phi>\<rangle>)
                 (imp (NN \<langle>\<phi>\<rangle> (Var yy'))
                      (eql \<langle>neg \<phi>\<rangle> (Var yy')))))"
    using B.prv_all_imp_cnj_rev[OF _ _ _ _ 2] by simp
  have 32: "bprv (imp (NN \<langle>\<phi>\<rangle> \<langle>neg \<phi>\<rangle>)
                      (all yy' (imp (NN \<langle>\<phi>\<rangle> (Var yy'))
                                    (eql \<langle>neg \<phi>\<rangle> (Var yy')))))"
    by (rule B.prv_all_imp[OF _ _ _ _ 31]) (auto simp: NN_def2)
  have 33: "bprv (all yy' (imp (NN \<langle>\<phi>\<rangle> (Var yy'))
                              (eql \<langle>neg \<phi>\<rangle> (Var yy'))))"
    by (rule B.prv_imp_mp [OF _ _ 32 1]) auto
  thus ?thesis using B.all_subst_rename_prv[OF _ _ _ _ 33, of yy] by simp
qed

lemma NN_neg_unique:
assumes [simp]:"\<phi> \<in> fmla" "Fvars \<phi> = {}"
shows
"bprv (imp (NN \<langle>\<phi>\<rangle> (Var yy))
           (eql \<langle>neg \<phi>\<rangle> (Var yy)))" (is "bprv ?A")
proof-
  have 0: "bprv (all yy ?A)"
    using NN_unique2[of "\<phi>"] by simp
  show ?thesis by (rule B.allE_id[OF _ _ 0]) auto
qed

lemma NN_exi_cnj:
assumes \<phi>[simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}" and \<chi>[simp]: "\<chi> \<in> fmla"
assumes f: "Fvars \<chi> = {yy}"
shows "bprv (eqv (subst \<chi> \<langle>neg \<phi>\<rangle> yy)
                 (exi yy (cnj \<chi> (NN \<langle>\<phi>\<rangle> (Var yy)))))"
(is "bprv (eqv ?A ?B)")
proof(intro B.prv_eqvI)
  have yy: "yy \<in> var" by simp
  let ?N = "NN \<langle>\<phi>\<rangle> (Var yy)"
  have "bprv (imp (subst \<chi> \<langle>neg \<phi>\<rangle> yy) ((subst (cnj \<chi> ?N) \<langle>neg \<phi>\<rangle> yy)))" using NN_neg[OF \<phi>]
    by (simp add: B.prv_imp_cnj B.prv_imp_refl B.prv_imp_triv)
  thus "bprv (imp ?A ?B)"
    by (elim B.prv_prv_imp_trans[rotated 3], intro B.prv_exi_inst) auto
next
  have 00: "bprv (imp (eql \<langle>neg \<phi>\<rangle> (Var yy)) (imp \<chi> (subst \<chi> \<langle>neg \<phi>\<rangle> yy)))"
    by (rule B.prv_eql_subst_trm_id_rev) auto
  have 11: "bprv (imp (NN \<langle>\<phi>\<rangle> (Var yy)) (imp \<chi> (subst \<chi> \<langle>neg \<phi>\<rangle> yy)))"
    using 00 NN_neg_unique[OF \<phi>]
    using NN num Var Variable \<phi> \<chi> eql imp subst B.prv_prv_imp_trans
    by (metis (no_types, lifting) enc in_num neg)
  hence "bprv (imp (cnj \<chi> (NN \<langle>\<phi>\<rangle> (Var yy))) (subst \<chi> \<langle>neg \<phi>\<rangle> yy))"
    by (simp add: 11 B.prv_cnj_imp_monoR2 B.prv_imp_com)
  hence 1: "bprv (all yy (imp (cnj \<chi> (NN \<langle>\<phi>\<rangle> (Var yy))) (subst \<chi> \<langle>neg \<phi>\<rangle> yy)))"
    by (simp add: B.prv_all_gen)
  have 2: "Fvars (subst \<chi> \<langle>neg \<phi>\<rangle> yy) = {}" using f by simp
  show "bprv (imp ?B ?A)" using 1 2
    by (simp add: B.prv_exi_imp)
qed auto

end \<comment> \<open>context @{locale Repr_Neg}\<close>


section \<open>Representability of Self-Substitution\<close>

text \<open>Self-substitution is the function that takes a formula @{term \<phi>}
and returns $\phi[\langle\phi\rangle/\mathit{xx}]$ (for the fixed variable @{term xx}). This is all that
will be needed for the diagonalization lemma.\<close>

locale Repr_SelfSubst =
Encode
  var trm fmla Var FvarsT substT Fvars subst
  num
  enc
+
Deduct2
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi
  prv bprv
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and num
and eql cnj imp all exi
and prv bprv
and enc ("\<langle>_\<rangle>")
+
fixes S :: 'fmla
assumes
S[simp,intro!]: "S \<in> fmla"
and
Fvars_S[simp]: "Fvars S = {xx,yy}"
and
subst_implies_prv_S:
"\<And> \<phi>.
  let SS = (\<lambda> t1 t2. psubst S [(t1,xx), (t2,yy)]) in
  \<phi> \<in> fmla \<longrightarrow> Fvars \<phi> = {xx} \<longrightarrow>
  bprv (SS \<langle>\<phi>\<rangle> \<langle>subst \<phi> \<langle>\<phi>\<rangle> xx\<rangle>)"
and
S_unique:
"\<And> \<phi>.
  let SS = (\<lambda> t1 t2. psubst S [(t1,xx), (t2,yy)]) in
  \<phi> \<in> fmla \<longrightarrow> Fvars \<phi> = {xx} \<longrightarrow>
  bprv (all yy (all yy'
     (imp (cnj (SS \<langle>\<phi>\<rangle> (Var yy)) (SS \<langle>\<phi>\<rangle> (Var yy')))
          (eql (Var yy) (Var yy')))))"
begin

text \<open>SS is the instantiation combinator of S:\<close>
definition SS where "SS \<equiv> \<lambda> t1 t2. psubst S [(t1,xx), (t2,yy)]"

lemma SS_def2: "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow>
 yy \<notin> FvarsT t1 \<Longrightarrow>
 SS t1 t2 = subst (subst S t1 xx) t2 yy"
  unfolding SS_def by (rule psubst_eq_rawpsubst2[simplified]) auto

lemma subst_implies_prv_SS:
"\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {xx} \<Longrightarrow> bprv (SS \<langle>\<phi>\<rangle> \<langle>subst \<phi> \<langle>\<phi>\<rangle> xx\<rangle>)"
using subst_implies_prv_S unfolding Let_def SS_def by meson

lemma SS_unique:
"\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {xx} \<Longrightarrow>
 bprv (all yy (all yy'
      (imp (cnj (SS \<langle>\<phi>\<rangle> (Var yy)) (SS \<langle>\<phi>\<rangle> (Var yy')))
           (eql (Var yy) (Var yy')))))"
using S_unique unfolding Let_def SS_def by meson

lemma SS[simp,intro]:
"t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> SS t1 t2 \<in> fmla"
unfolding SS_def by auto

lemma Fvars_SS[simp]: "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> yy \<notin> FvarsT t1 \<Longrightarrow>
Fvars (SS t1 t2) = FvarsT t1 \<union> FvarsT t2"
by (auto simp add: SS_def2 subst2_fresh_switch)

lemma [simp]:
"m \<in> num \<Longrightarrow> p \<in> num \<Longrightarrow> subst (SS m (Var yy)) p yy = SS m p"
"m \<in> num \<Longrightarrow> subst (SS m (Var yy')) (Var yy) yy' = SS m (Var yy)"
"m \<in> num \<Longrightarrow> p \<in> num \<Longrightarrow> subst (SS m (Var yy')) p yy' = SS m p"
"m \<in> num \<Longrightarrow> p \<in> num \<Longrightarrow> subst (SS m (Var yy')) p yy = SS m (Var yy')"
"m \<in> num \<Longrightarrow> subst (SS (Var xx) (Var yy)) m xx = SS m (Var yy)"
by (auto simp add: SS_def2 subst_comp_num Let_def)

end \<comment> \<open>context @{locale Repr_SelfSubst}\<close>


section \<open>Representability of Self-Soft-Substitution\<close>

text \<open>The soft substitution function performs substitution logically instead of
syntactically. In particular, its "self" version sends @{term \<phi>} to
@{term "exi xx (cnj (eql (Var xx) (enc \<phi>)) \<phi>)"}. Representability of self-soft-substitution will be
an alternative assumption in the diagonalization lemma.\<close>

locale Repr_SelfSoftSubst =
Encode
  var trm fmla Var FvarsT substT Fvars subst
  num
  enc
+
Deduct2
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi
  prv bprv
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and num
and eql cnj imp all exi
and prv bprv
and enc ("\<langle>_\<rangle>")
+
fixes S :: 'fmla
assumes
S[simp,intro!]: "S \<in> fmla"
and
Fvars_S[simp]: "Fvars S = {xx,yy}"
and
softSubst_implies_prv_S:
"\<And> \<phi>.
  let SS = (\<lambda> t1 t2. psubst S [(t1,xx), (t2,yy)]) in
  \<phi> \<in> fmla \<longrightarrow> Fvars \<phi> = {xx} \<longrightarrow>
  bprv (SS \<langle>\<phi>\<rangle> \<langle>softSubst \<phi> \<langle>\<phi>\<rangle> xx\<rangle>)"
and
S_unique:
"\<And> \<phi>.
  let SS = (\<lambda> t1 t2. psubst S [(t1,xx), (t2,yy)]) in
  \<phi> \<in> fmla \<longrightarrow> Fvars \<phi> = {xx} \<longrightarrow>
  bprv (all yy (all yy'
     (imp (cnj (SS \<langle>\<phi>\<rangle> (Var yy)) (SS \<langle>\<phi>\<rangle> (Var yy')))
          (eql (Var yy) (Var yy')))))"
begin

text \<open>SS is the instantiation combinator of S:\<close>
definition SS where "SS \<equiv> \<lambda> t1 t2. psubst S [(t1,xx), (t2,yy)]"

lemma SS_def2: "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow>
 yy \<notin> FvarsT t1 \<Longrightarrow>
 SS t1 t2 = subst (subst S t1 xx) t2 yy"
  unfolding SS_def by (rule psubst_eq_rawpsubst2[simplified]) auto

lemma softSubst_implies_prv_SS:
"\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {xx} \<Longrightarrow> bprv (SS \<langle>\<phi>\<rangle> \<langle>softSubst \<phi> \<langle>\<phi>\<rangle> xx\<rangle>)"
using softSubst_implies_prv_S unfolding Let_def SS_def by meson

lemma SS_unique:
"\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {xx} \<Longrightarrow>
 bprv (all yy (all yy'
     (imp (cnj (SS \<langle>\<phi>\<rangle> (Var yy)) (SS \<langle>\<phi>\<rangle> (Var yy')))
          (eql (Var yy) (Var yy')))))"
using S_unique unfolding Let_def SS_def by meson

lemma SS[simp,intro]:
"t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> SS t1 t2 \<in> fmla"
unfolding SS_def by auto

lemma Fvars_SS[simp]: "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> yy \<notin> FvarsT t1 \<Longrightarrow>
Fvars (SS t1 t2) = FvarsT t1 \<union> FvarsT t2"
by (auto simp add: SS_def2 subst2_fresh_switch)

lemma [simp]:
"m \<in> num \<Longrightarrow> p \<in> num \<Longrightarrow> subst (SS m (Var yy)) p yy = SS m p"
"m \<in> num \<Longrightarrow> subst (SS m (Var yy')) (Var yy) yy' = SS m (Var yy)"
"m \<in> num \<Longrightarrow> p \<in> num \<Longrightarrow> subst (SS m (Var yy')) p yy' = SS m p"
"m \<in> num \<Longrightarrow> p \<in> num \<Longrightarrow> subst (SS m (Var yy')) p yy = SS m (Var yy')"
"m \<in> num \<Longrightarrow> subst (SS (Var xx) (Var yy)) m xx = SS m (Var yy)"
by (auto simp add: SS_def2 subst_comp_num Let_def)

end \<comment> \<open>context @{locale Repr_SelfSoftSubst}\<close>


section \<open>Clean Representability of the "Proof-of" Relation\<close>


text\<open>For the proof-of relation, we must assume a stronger version of
representability, namely clean representability on the first argument, which
is dedicated to encoding the proof component. The property asks that the
representation predicate is provably false on numerals that do not encode
proofs; it would hold trivially for surjective proof encodings.

Cleanness is not a standard concept in the literature -- we have
introduced it in our CADE 2019 paper~\cite{DBLP:conf/cade/0001T19}.\<close>

locale CleanRepr_Proofs =
Encode_Proofs
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi
  prv bprv
  enc
  fls
  dsj
  "proof" prfOf
  encPf
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and num
and eql cnj imp all exi
and prv bprv
and enc ("\<langle>_\<rangle>")
and fls dsj
and "proof" :: "'proof set" and prfOf
and encPf
+
fixes Pf :: 'fmla
assumes
Pf[simp,intro!]: "Pf \<in> fmla"
and
Fvars_Pf[simp]: "Fvars Pf = {yy,xx}"
and
prfOf_Pf:
"\<And> prf \<phi>.
  let PPf = (\<lambda> t1 t2. psubst Pf [(t1,yy), (t2,xx)]) in
  (prf \<in> proof \<and> \<phi> \<in> fmla \<and> Fvars \<phi> = {} \<longrightarrow>
   prfOf prf \<phi>
   \<longrightarrow>
   bprv (PPf (encPf prf) \<langle>\<phi>\<rangle>))"
and
not_prfOf_Pf:
"\<And> prf \<phi>.
  let PPf = (\<lambda> t1 t2. psubst Pf [(t1,yy), (t2,xx)]) in
  (prf \<in> proof \<and> \<phi> \<in> fmla \<and> Fvars \<phi> = {} \<longrightarrow>
   \<not> prfOf prf \<phi>
   \<longrightarrow>
   bprv (neg (PPf (encPf prf) \<langle>\<phi>\<rangle>)))"
and
Clean_Pf_encPf:
"\<And> p \<phi>. let PPf = (\<lambda> t1 t2. psubst Pf [(t1,yy), (t2,xx)]) in
  p \<in> num \<and> \<phi> \<in> fmla \<and> Fvars \<phi> = {} \<longrightarrow> p \<notin> encPf ` proof \<longrightarrow> bprv (neg (PPf p \<langle>\<phi>\<rangle>))"
begin

text \<open>PPf is the instantiation combinator of Pf:\<close>
definition PPf where "PPf \<equiv> \<lambda> t1 t2. psubst Pf [(t1,yy), (t2,xx)]"

lemma prfOf_PPf:
assumes "prf \<in> proof" "\<phi> \<in> fmla" "Fvars \<phi> = {}" "prfOf prf \<phi>"
shows "bprv (PPf (encPf prf) \<langle>\<phi>\<rangle>)"
  using assms prfOf_Pf unfolding PPf_def by auto

lemma not_prfOf_PPf:
assumes "prf \<in> proof" "\<phi> \<in> fmla" "Fvars \<phi> = {}" "\<not> prfOf prf \<phi>"
shows "bprv (neg (PPf (encPf prf) \<langle>\<phi>\<rangle>))"
  using assms not_prfOf_Pf unfolding PPf_def by auto

lemma Clean_PPf_encPf:
  assumes "\<phi> \<in> fmla" "Fvars \<phi> = {}" and "p \<in> num" "p \<notin> encPf ` proof"
  shows "bprv (neg (PPf p \<langle>\<phi>\<rangle>))"
using assms Clean_Pf_encPf unfolding PPf_def by auto

lemma PPf[simp,intro!]: "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> xx \<notin> FvarsT t1 \<Longrightarrow> PPf t1 t2 \<in> fmla"
  unfolding PPf_def by auto

lemma PPf_def2: "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> xx \<notin> FvarsT t1 \<Longrightarrow>
  PPf t1 t2 = subst (subst Pf t1 yy) t2 xx"
  unfolding PPf_def by (rule psubst_eq_rawpsubst2[simplified]) auto

lemma Fvars_PPf[simp]:
"t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> xx \<notin> FvarsT t1 \<Longrightarrow>
 Fvars (PPf t1 t2) = FvarsT t1 \<union> FvarsT t2"
by (auto simp add: PPf_def2 subst2_fresh_switch)

lemma [simp]:
"n \<in> num \<Longrightarrow> subst (PPf (Var yy) (Var xx)) n xx = PPf (Var yy) n"
"m \<in> num \<Longrightarrow> n \<in> num \<Longrightarrow> subst (PPf (Var yy) m) n yy = PPf n m"
"n \<in> num \<Longrightarrow> subst (PPf (Var yy) (Var xx)) n yy = PPf n (Var xx)"
"m \<in> num \<Longrightarrow> n \<in> num \<Longrightarrow> subst (PPf m (Var xx)) n xx = PPf m n"
"m \<in> num \<Longrightarrow> subst (PPf (Var zz) (Var xx')) m zz = PPf m (Var xx')"
"m \<in> num \<Longrightarrow> n \<in> num \<Longrightarrow> subst (PPf m (Var xx')) n xx' = PPf m n"
"n \<in> num \<Longrightarrow> subst (PPf (Var zz) (Var xx')) n xx' = PPf (Var zz) n"
"m \<in> num \<Longrightarrow> n \<in> num \<Longrightarrow> subst (PPf (Var zz) n) m zz = PPf m n"
by (auto simp add: PPf_def2 subst2_fresh_switch)

lemma B_consistent_prfOf_iff_PPf:
"B.consistent \<Longrightarrow> prf \<in> proof \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<longrightarrow> prfOf prf \<phi> \<longleftrightarrow> bprv (PPf (encPf prf) \<langle>\<phi>\<rangle>)"
  unfolding B.consistent_def3 using not_prfOf_PPf[of "prf" \<phi>] prfOf_PPf[of "prf" \<phi>] by force

lemma consistent_prfOf_iff_PPf:
"consistent \<Longrightarrow> prf \<in> proof \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<longrightarrow> prfOf prf \<phi> \<longleftrightarrow> bprv (PPf (encPf prf) \<langle>\<phi>\<rangle>)"
  using B_consistent_prfOf_iff_PPf[OF dwf_dwfd.consistent_B_consistent] .

end \<comment> \<open>context @{locale CleanRepr_Proofs}\<close>

(*<*)
end
(*>*)
