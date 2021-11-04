chapter \<open>Standard Models with Two Provability Relations\<close>

(*<*)
(* Abstract notion of standard model and truth  *)
theory Standard_Model_More
imports Derivability_Conditions "Syntax_Independent_Logic.Standard_Model"
begin
(*>*)

locale Minimal_Truth_Soundness_Proof_Repr =
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
+ \<comment> \<open>The label "B" stands for "basic", as a reminder that soundness
refers to the basic provability relation:\<close>
B: Minimal_Truth_Soundness
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
  bprv
  isTrue
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and eql cnj imp all exi
and fls
and dsj
and num
and prv bprv
and isTrue
and enc ("\<langle>_\<rangle>")
and "proof" :: "'proof set" and prfOf
and encPf Pf
begin

lemmas prfOf_iff_PPf = B_consistent_prfOf_iff_PPf[OF B.consistent]

text \<open>The provability predicate is decided by basic provability on encodings:\<close>
lemma isTrue_prv_PPf_prf_or_neg:
"prf \<in> proof \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow>
    bprv (PPf (encPf prf) \<langle>\<phi>\<rangle>) \<or> bprv (neg (PPf (encPf prf) \<langle>\<phi>\<rangle>))"
  using not_prfOf_PPf prfOf_PPf by blast

text \<open>... hence that predicate is complete w.r.t. truth:\<close>
lemma isTrue_PPf_Implies_bprv_PPf:
"prf \<in> proof \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow>
   isTrue (PPf (encPf prf) \<langle>\<phi>\<rangle>) \<Longrightarrow> bprv (PPf (encPf prf) \<langle>\<phi>\<rangle>)"
  by (metis FvarsT_num Fvars_PPf Fvars_fls PPf
Un_empty empty_iff enc encPf fls in_num isTrue_prv_PPf_prf_or_neg
neg_def B.not_isTrue_fls B.prv_imp_implies_isTrue)

text \<open>... and thanks cleanness we can replace encoded proofs
with arbitrary numerals in the completeness property:\<close>
lemma isTrue_implies_bprv_PPf:
assumes [simp]: "n \<in> num" "\<phi> \<in> fmla" "Fvars \<phi> = {}"
and iT: "isTrue (PPf n \<langle>\<phi>\<rangle>)"
shows "bprv (PPf n \<langle>\<phi>\<rangle>)"
proof(cases "n \<in> encPf ` proof")
  case True
  thus ?thesis
    using iT isTrue_PPf_Implies_bprv_PPf by auto
next
  case False
  hence "bprv (neg (PPf n \<langle>\<phi>\<rangle>))" by (simp add: Clean_PPf_encPf)
  hence "isTrue (neg (PPf n \<langle>\<phi>\<rangle>))" by (intro B.sound_isTrue) auto
  hence False using iT by (intro B.isTrue_neg_excl) auto
  thus ?thesis by auto
qed

text \<open>... in fact, by @{locale Minimal_Truth_Soundness} we even have an iff:\<close>
lemma isTrue_iff_bprv_PPf:
"\<And> n \<phi>. n \<in> num \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> isTrue (PPf n \<langle>\<phi>\<rangle>) \<longleftrightarrow> bprv (PPf n \<langle>\<phi>\<rangle>)"
using isTrue_implies_bprv_PPf
using exists_no_Fvars B.not_isTrue_fls B.sound_isTrue by auto

text \<open>Truth of the provability representation implies provability (TIP):\<close>
lemma TIP:
assumes \<phi>[simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}"
and iPP: "isTrue (wrepr.PP \<langle>\<phi>\<rangle>)"
shows "prv \<phi>"
proof-
  have "isTrue (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>))" using iPP unfolding PP_PPf[OF \<phi>(1)] .
  from B.isTrue_exi[OF _ _ _ this]
  obtain n where n[simp]: "n \<in> num" and "isTrue (PPf n \<langle>\<phi>\<rangle>)" by auto
  hence pP: "bprv (PPf n \<langle>\<phi>\<rangle>)" using isTrue_implies_bprv_PPf by auto
  hence "\<not> bprv (neg (PPf n \<langle>\<phi>\<rangle>))"
  using B.prv_neg_excl[of "PPf n \<langle>\<phi>\<rangle>"] by auto
  then obtain "prf" where "prf"[simp]: "prf \<in> proof" and nn: "n = encPf prf"
  using assms n Clean_PPf_encPf \<phi>(1) by blast
  have "prfOf prf \<phi>" using pP unfolding nn using prfOf_iff_PPf by auto
  thus ?thesis using prv_prfOf by auto
qed

text \<open>The reverse HBL1 -- now without the $\omega$-consistency assumption which holds here
thanks to our truth-in-standard-model assumption:\<close>

lemmas HBL1_rev = \<omega>consistentStd1_HBL1_rev[OF B.\<omega>consistentStd1]
text \<open>Note that the above would also follow by @{locale Minimal_Truth_Soundness} from TIP:\<close>
lemma TIP_implies_HBL1_rev:
assumes TIP: "\<forall>\<phi>. \<phi> \<in> fmla \<and> Fvars \<phi> = {} \<and> isTrue (wrepr.PP \<langle>\<phi>\<rangle>) \<longrightarrow> prv \<phi>"
shows "\<forall>\<phi>. \<phi> \<in> fmla \<and> Fvars \<phi> = {} \<and> bprv (wrepr.PP \<langle>\<phi>\<rangle>) \<longrightarrow> prv \<phi>"
using B.sound_isTrue[of "wrepr.PP \<langle>_\<rangle>"] TIP by auto

end \<comment> \<open>context @{locale Minimal_Truth_Soundness_Proof_Repr}\<close>


section \<open>Proof recovery from $\mathit{HBL1\_iff}$\<close>

locale Minimal_Truth_Soundness_HBL1iff_Compl_Pf =
HBL1
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi
  prv bprv
  enc
  P
+
B : Minimal_Truth_Soundness
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
  bprv
  isTrue
+
Deduct_with_False_Disj
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
  prv
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and eql cnj imp all exi
and fls
and dsj
and num
and enc ("\<langle>_\<rangle>")
and prv bprv
and P
and isTrue
+
fixes Pf :: 'fmla
assumes
\<comment> \<open>@{term Pf} is a formula with free variables @{term xx} @{term yy}:\<close>
Pf[simp,intro!]: "Pf \<in> fmla"
and
Fvars_Pf[simp]: "Fvars Pf = {yy,xx}"
and
\<comment> \<open>@{term P} relates to @{term Pf} internally (inside basic provability)
just like a @{term prv} and a @{term prfOf} would relate---via an existential:\<close>
P_Pf:
"\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow>
 let PPf = (\<lambda> t1 t2. psubst Pf [(t1,yy), (t2,xx)]) in
 bprv (eqv (subst P \<langle>\<phi>\<rangle> xx) (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>)))"
assumes
\<comment> \<open>We assume both $\mathit{HBL1}$ and $\mathit{HBL1\_rev}$, i.e., an iff version:\<close>
HBL1_iff: "\<And> \<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> bprv (PP \<langle>\<phi>\<rangle>) \<longleftrightarrow> prv \<phi>"
and
Compl_Pf:
"\<And> n \<phi>. n \<in> num \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow>
 let PPf = (\<lambda> t1 t2. psubst Pf [(t1,yy), (t2,xx)]) in
 isTrue (PPf n \<langle>\<phi>\<rangle>) \<longrightarrow> bprv (PPf n \<langle>\<phi>\<rangle>)"
begin

definition PPf where "PPf \<equiv> \<lambda> t1 t2. psubst Pf [(t1,yy), (t2,xx)]"

lemma PP_deff: "PP t = subst P t xx" using PP_def by auto

lemma PP_PPf_eqv:
  "\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> bprv (eqv (PP \<langle>\<phi>\<rangle>) (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>)))"
  using PP_deff PPf_def P_Pf by auto

(*  *)

lemma PPf[simp,intro!]: "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> xx \<notin> FvarsT t1 \<Longrightarrow> PPf t1 t2 \<in> fmla"
  unfolding PPf_def by auto

lemma PPf_def2: "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> xx \<notin> FvarsT t1 \<Longrightarrow>
  PPf t1 t2 = subst (subst Pf t1 yy) t2 xx"
  unfolding PPf_def by (rule psubst_eq_rawpsubst2[simplified]) auto

lemma Fvars_PPf[simp]:
  "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> xx \<notin> FvarsT t1 \<Longrightarrow> Fvars (PPf t1 t2) = FvarsT t1 \<union> FvarsT t2"
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
  by (auto simp: PPf_def2 subst2_fresh_switch)

(* *)

lemma PP_PPf:
assumes "\<phi> \<in> fmla" "Fvars \<phi> = {}" shows "bprv (PP \<langle>\<phi>\<rangle>) \<longleftrightarrow> bprv (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>))"
  using assms PP_PPf_eqv[OF assms] B.prv_eqv_sym[OF _ _ PP_PPf_eqv[OF assms]]
  by (auto intro!: B.prv_eqv_prv[of "PP \<langle>\<phi>\<rangle>" "exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>)"]
    B.prv_eqv_prv[of "exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>)" "PP \<langle>\<phi>\<rangle>"])

lemma isTrue_implies_bprv_PPf:
"\<And> n \<phi>. n \<in> num \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow>
 isTrue (PPf n \<langle>\<phi>\<rangle>) \<Longrightarrow> bprv (PPf n \<langle>\<phi>\<rangle>)"
  using Compl_Pf by(simp add: PPf_def)

lemma isTrue_iff_bprv_PPf:
"\<And> n \<phi>. n \<in> num \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> isTrue (PPf n \<langle>\<phi>\<rangle>) \<longleftrightarrow> bprv (PPf n \<langle>\<phi>\<rangle>)"
using isTrue_implies_bprv_PPf
  using exists_no_Fvars B.not_isTrue_fls B.sound_isTrue by auto

text \<open>Preparing to instantiate this "proof recovery" alternative into our
mainstream locale hierarchy, which assumes proofs.
We define the "missing" proofs to be numerals, we encode them as the identity,
and we "copy" @{term prfOf} from the corresponding predicate one-level-up, @{term PPf}:\<close>

definition "proof" :: "'trm set" where [simp]: "proof = num"
definition prfOf :: "'trm \<Rightarrow> 'fmla \<Rightarrow> bool" where
  "prfOf n \<phi> \<equiv> bprv (PPf n \<langle>\<phi>\<rangle>)"
definition encPf :: "'trm \<Rightarrow> 'trm" where [simp]: "encPf \<equiv> id"
(*  *)

lemma prv_exi_PPf_iff_isTrue:
assumes [simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}"
shows "bprv (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>)) \<longleftrightarrow> isTrue (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>))" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L thus ?R by (intro B.sound_isTrue) auto
next
  assume ?R
  obtain n where n[simp]: "n \<in> num" and i: "isTrue (PPf n \<langle>\<phi>\<rangle>)" using B.isTrue_exi[OF _ _ _ \<open>?R\<close>] by auto
  hence "bprv (PPf n \<langle>\<phi>\<rangle>)" by (auto simp: isTrue_iff_bprv_PPf)
  thus ?L by (intro B.prv_exiI[of _ _ n]) auto
qed

lemma isTrue_exi_iff:
assumes [simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}"
shows "isTrue (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>)) \<longleftrightarrow> (\<exists>n\<in>num. isTrue (PPf n \<langle>\<phi>\<rangle>))" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L thus ?R using B.isTrue_exi[OF _ _ _ \<open>?L\<close>] by auto
next
  assume ?R
  then obtain n where n[simp]: "n \<in> num" and i: "isTrue (PPf n \<langle>\<phi>\<rangle>)" by auto
  hence "bprv (PPf n \<langle>\<phi>\<rangle>)" by (auto simp: isTrue_iff_bprv_PPf)
  hence "bprv (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>))" by (intro B.prv_exiI[of _ _ n]) auto
  thus ?L by (intro B.sound_isTrue) auto
qed

lemma prv_prfOf:
assumes "\<phi> \<in> fmla" "Fvars \<phi> = {}"
shows "prv \<phi> \<longleftrightarrow> (\<exists>n\<in>num. prfOf n \<phi>)"
proof-
  have "prv \<phi> \<longleftrightarrow> bprv (PP \<langle>\<phi>\<rangle>)" using HBL1_iff[OF assms] by simp
  also have "\<dots> \<longleftrightarrow> bprv (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>))" unfolding PP_PPf[OF assms] ..
  also have "\<dots> \<longleftrightarrow> isTrue (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>))" using prv_exi_PPf_iff_isTrue[OF assms] .
  also have "\<dots> \<longleftrightarrow> (\<exists>n\<in>num. isTrue (PPf n \<langle>\<phi>\<rangle>))" using isTrue_exi_iff[OF assms] .
  also have "\<dots> \<longleftrightarrow> (\<exists>n\<in>num. bprv (PPf n \<langle>\<phi>\<rangle>))" using isTrue_iff_bprv_PPf[OF _ assms] by auto
  also have "\<dots> \<longleftrightarrow> (\<exists>n\<in>num. prfOf n \<phi>)" unfolding prfOf_def ..
  finally show ?thesis .
qed

lemma prfOf_prv_Pf:
assumes "n \<in> num" and "\<phi> \<in> fmla" "Fvars \<phi> = {}" and "prfOf n \<phi>"
shows "bprv (psubst Pf [(n, yy), (\<langle>\<phi>\<rangle>, xx)])"
using assms unfolding prfOf_def by (auto simp: PPf_def2 psubst_eq_rawpsubst2)

lemma isTrue_exi_iff_PP:
assumes [simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}"
shows "isTrue (PP \<langle>\<phi>\<rangle>) \<longleftrightarrow> (\<exists>n\<in>num. isTrue (PPf n \<langle>\<phi>\<rangle>))"
proof-
  have "bprv (eqv (PP \<langle>\<phi>\<rangle>) (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>)))"
    using PP_PPf_eqv by auto
  hence "bprv (imp (PP \<langle>\<phi>\<rangle>) (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>)))"
  and "bprv (imp (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>)) (PP \<langle>\<phi>\<rangle>))"
  by (simp_all add: B.prv_imp_eqvEL B.prv_imp_eqvER)
  thus ?thesis unfolding isTrue_exi_iff[OF assms, symmetric]
    by (intro iffI) (rule B.prv_imp_implies_isTrue; simp)+
qed

lemma bprv_compl_isTrue_PP_enc:
assumes 1: "\<phi> \<in> fmla" "Fvars \<phi> = {}" and 2: "isTrue (PP \<langle>\<phi>\<rangle>)"
shows "bprv (PP \<langle>\<phi>\<rangle>)"
proof-
  obtain n where nn: "n \<in> num" and i: "isTrue (PPf n \<langle>\<phi>\<rangle>)"
   using 2 unfolding isTrue_exi_iff_PP[OF 1] ..
  hence "bprv (PPf n \<langle>\<phi>\<rangle>)"
    using i using nn assms isTrue_iff_bprv_PPf by blast
  hence "bprv (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>))"
  using 2 assms isTrue_exi_iff isTrue_exi_iff_PP prv_exi_PPf_iff_isTrue by auto
  thus ?thesis using PP_PPf 1 by blast
qed

lemma TIP:
assumes 1: "\<phi> \<in> fmla" "Fvars \<phi> = {}" and 2: "isTrue (PP \<langle>\<phi>\<rangle>)"
shows "prv \<phi>"
using bprv_compl_isTrue_PP_enc[OF assms] HBL1_iff assms by blast


end \<comment> \<open>context @{locale Minimal_Truth_Soundness_HBL1iff_Compl_Pf}\<close>


locale Minimal_Truth_Soundness_HBL1iff_Compl_Pf_Compl_NegPf =
Minimal_Truth_Soundness_HBL1iff_Compl_Pf
+
assumes
Compl_NegPf:
"\<And> n \<phi>. n \<in> num \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow>
 let PPf = (\<lambda> t1 t2. psubst Pf [(t1,yy), (t2,xx)]) in
 isTrue (B.neg (PPf n \<langle>\<phi>\<rangle>)) \<longrightarrow> bprv (B.neg (PPf n \<langle>\<phi>\<rangle>))"
begin

lemma isTrue_implies_prv_neg_PPf:
"\<And> n \<phi>. n \<in> num \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow>
 isTrue (B.neg (PPf n \<langle>\<phi>\<rangle>)) \<Longrightarrow> bprv (B.neg (PPf n \<langle>\<phi>\<rangle>))"
  using Compl_NegPf by(simp add: PPf_def)

lemma isTrue_iff_prv_neg_PPf:
"\<And> n \<phi>. n \<in> num \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> isTrue (B.neg (PPf n \<langle>\<phi>\<rangle>)) \<longleftrightarrow> bprv (B.neg (PPf n \<langle>\<phi>\<rangle>))"
using isTrue_implies_prv_neg_PPf
  using exists_no_Fvars B.not_isTrue_fls B.sound_isTrue by auto

lemma prv_PPf_decide:
assumes [simp]: "n \<in> num" "\<phi> \<in> fmla" "Fvars \<phi> = {}"
and np: "\<not> bprv (PPf n \<langle>\<phi>\<rangle>)"
shows "bprv (B.neg (PPf n \<langle>\<phi>\<rangle>))"
proof-
  have "\<not> isTrue (PPf n \<langle>\<phi>\<rangle>)" using assms by (auto simp: isTrue_iff_bprv_PPf)
  hence "isTrue (B.neg (PPf n \<langle>\<phi>\<rangle>))" using B.isTrue_neg[of "PPf n \<langle>\<phi>\<rangle>"] by auto
  thus ?thesis by (auto simp: isTrue_iff_prv_neg_PPf)
qed

lemma not_prfOf_prv_neg_Pf:
assumes n\<phi>: "n \<in> num" "\<phi> \<in> fmla" "Fvars \<phi> = {}" and "\<not> prfOf n \<phi>"
shows "bprv (B.neg (psubst Pf [(n, yy), (\<langle>\<phi>\<rangle>, xx)]))"
  using assms prv_PPf_decide[OF n\<phi>] by (auto simp: prfOf_def PPf_def2 psubst_eq_rawpsubst2)

end \<comment> \<open>context @{locale Minimal_Truth_Soundness_HBL1iff_Compl_Pf_Compl_NegPf}\<close>

sublocale Minimal_Truth_Soundness_HBL1iff_Compl_Pf_Compl_NegPf <
   repr: CleanRepr_Proofs
(* added label to avoid duplicated constant P, which is assumed
in Minimal_Truth_Soundness_HBL1iff_Compl_Pf but defined in CleanRepr_Proofs
(they are of course extensionally equal).
*)
  where "proof" = "proof" and prfOf = prfOf and encPf = encPf
  by standard (auto simp: bprv_prv prv_prfOf prfOf_prv_Pf not_prfOf_prv_neg_Pf)

(* Lemma 6 ("proof recovery") from the JAR paper: *)
sublocale Minimal_Truth_Soundness_HBL1iff_Compl_Pf_Compl_NegPf <
  min_truth: Minimal_Truth_Soundness_Proof_Repr
where "proof" = "proof" and prfOf = prfOf and encPf = encPf
  by standard



(* FOR THE CLASSICAL REASONING VERSION *)

locale Minimal_Truth_Soundness_HBL1iff_prv_Compl_Pf =
HBL1
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi
  prv bprv
  enc
  P
+
B: Minimal_Truth_Soundness
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
  bprv
  isTrue
+
Deduct_with_False_Disj
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
  prv
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and eql cnj imp all exi
and fls
and dsj
and num
and enc ("\<langle>_\<rangle>")
and prv bprv
and P
and isTrue
+
fixes Pf :: 'fmla
assumes
(* Pf is a formula with free variables xx yy  *)
Pf[simp,intro!]: "Pf \<in> fmla"
and
Fvars_Pf[simp]: "Fvars Pf = {yy,xx}"
and
(* P relates to Pf internally just like a prv and a proofOf would
relate: via an existential *)
P_Pf:
"\<phi> \<in> fmla \<Longrightarrow>
 let PPf = (\<lambda> t1 t2. psubst Pf [(t1,yy), (t2,xx)]) in
 bprv (eqv (subst P \<langle>\<phi>\<rangle> xx) (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>)))"
assumes
(* We assume, in addition to HBL1, the strong form of HBL1_rev: *)
HBL1_rev_prv: "\<And> \<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> prv (PP \<langle>\<phi>\<rangle>) \<Longrightarrow> prv \<phi>"
and
Compl_Pf:
"\<And> n \<phi>. n \<in> num \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow>
 let PPf = (\<lambda> t1 t2. psubst Pf [(t1,yy), (t2,xx)]) in
 isTrue (PPf n \<langle>\<phi>\<rangle>) \<longrightarrow> bprv (PPf n \<langle>\<phi>\<rangle>)"
begin

lemma HBL1_rev:
  assumes f: "\<phi> \<in> fmla" and fv: "Fvars \<phi> = {}" and bp: "bprv (PP \<langle>\<phi>\<rangle>)"
  shows "prv \<phi>"
  using assms by (auto intro!: HBL1_rev_prv bprv_prv[OF _ _ bp])

lemma HBL1_iff: "\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> bprv (PP \<langle>\<phi>\<rangle>) \<longleftrightarrow> prv \<phi>"
  using HBL1 HBL1_rev unfolding PP_def by auto

lemma HBL1_iff_prv: "\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> prv (PP \<langle>\<phi>\<rangle>) \<longleftrightarrow> prv \<phi>"
  by (intro iffI bprv_prv[OF _ _ HBL1_PP], elim HBL1_rev_prv[rotated -1]) auto

end \<comment> \<open>context @{locale Minimal_Truth_Soundness_HBL1iff_prv_Compl_Pf}\<close>

sublocale Minimal_Truth_Soundness_HBL1iff_prv_Compl_Pf <
  mts_prv_mts: Minimal_Truth_Soundness_HBL1iff_Compl_Pf where Pf = Pf
  using P_Pf HBL1_rev HBL1_PP Compl_Pf
  by unfold_locales auto

locale Minimal_Truth_Soundness_HBL1iff_prv_Compl_Pf_Classical =
Minimal_Truth_Soundness_HBL1iff_prv_Compl_Pf
+
assumes
\<comment> \<open>NB: we don't really need to assume classical reasoning (double negation) all throughout,
but only for the provability predicate:\<close>
classical_P: "\<And> \<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> let PP = (\<lambda>t. subst P t xx) in
  prv (B.neg (B.neg (PP \<langle>\<phi>\<rangle>))) \<Longrightarrow> prv (PP \<langle>\<phi>\<rangle>)"
begin

lemma classical_PP: "\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> prv (B.neg (B.neg (PP \<langle>\<phi>\<rangle>))) \<Longrightarrow> prv (PP \<langle>\<phi>\<rangle>)"
  using classical_P unfolding PP_def by auto

end \<comment> \<open>context @{locale Minimal_Truth_Soundness_HBL1iff_prv_Compl_Pf_Classical}\<close>

(*<*)
end
(*>*)
