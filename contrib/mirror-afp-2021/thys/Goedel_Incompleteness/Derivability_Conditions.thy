chapter \<open>The Hilbert-Bernays-Löb (HBL) Derivability Conditions\<close>

(*<*)
theory Derivability_Conditions imports Abstract_Representability
begin
(*>*)

section \<open>First Derivability Condition\<close>

(* Assume the provability predicate is "very-weakly" representable,
in that one implication of the weak representability condition holds.   *)
locale HBL1 =
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
(* Very-weak represenatbility of provability, as a one-variable formula P, usually called the provability predicate: *)
fixes P :: 'fmla
assumes
P[intro!,simp]: "P \<in> fmla"
and
Fvars_P[simp]: "Fvars P = {xx}"
and
HBL1: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> prv \<phi> \<Longrightarrow> bprv (subst P \<langle>\<phi>\<rangle> xx)"
begin

(* For all our (very-weak) representability assumptions, in addition to
 the representing formulas,
here, P, we define a corresponding instantiation combinator, here the
predicate PP.
If we think of P as P(xx), then PP t is the instance PP(t)  *)
definition PP where "PP \<equiv> \<lambda>t. subst P t xx"

lemma PP[simp]: "\<And>t. t \<in> trm \<Longrightarrow> PP t \<in> fmla"
  unfolding PP_def by auto

lemma Fvars_PP[simp]: "\<And>t. t \<in> trm \<Longrightarrow> Fvars (PP t) = FvarsT t"
  unfolding PP_def by auto

lemma [simp]:
"n \<in> num \<Longrightarrow> subst (PP (Var yy)) n yy = PP n"
"n \<in> num \<Longrightarrow> subst (PP (Var xx)) n xx = PP n"
  unfolding PP_def by auto

lemma HBL1_PP:
"\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> prv \<phi> \<Longrightarrow> bprv (PP \<langle>\<phi>\<rangle>)"
  using HBL1 unfolding PP_def by auto

end \<comment> \<open>context @{locale HBL1}\<close>


section \<open>Connections between Proof Representability,
First Derivability Condition, and Its Converse\<close>

context CleanRepr_Proofs
begin

text \<open>Defining @{term P}, the internal notion of provability,
from @{term Pf} (in its predicate form @{term PPf}), the internal notion of "proof-of".
NB: In the technical sense of the term "represents", we have that
@{term Pf} represents @{term pprv}, whereas @{term P} will not represent @{term prv}, but satisfy a weaker
condition (weaker than weak representability), namely HBL1.\<close>

subsection \<open>HBL1 from "proof-of" representability\<close>

definition P :: "'fmla" where "P \<equiv> exi yy (PPf (Var yy) (Var xx))"

lemma P[simp,intro!]: "P \<in> fmla" and Fvars_P[simp]: "Fvars P = {xx}"
  unfolding P_def by (auto simp: PPf_def2)

text \<open>We infer HBL1 from Pf representing prv:\<close>
lemma HBL1:
assumes \<phi>: "\<phi> \<in> fmla" "Fvars \<phi> = {}" and p\<phi>: "prv \<phi>"
shows "bprv (subst P \<langle>\<phi>\<rangle> xx)"
proof-
  obtain "prf" where pf: "prf \<in> proof" and "prfOf prf \<phi>" using prv_prfOf assms by auto
  hence 0: "bprv (PPf (encPf prf) (enc \<phi>))"
    using prfOf_PPf \<phi> by auto
  have 1: "subst (subst Pf (encPf prf) yy) \<langle>\<phi>\<rangle> xx = subst (subst Pf \<langle>\<phi>\<rangle> xx) (substT (encPf prf) \<langle>\<phi>\<rangle> xx) yy"
     using assms pf by (intro subst_compose_diff) auto
  show ?thesis using 0 unfolding P_def using assms
    by (auto simp: PPf_def2 1 pf intro!: B.prv_exiI[of _ _ "encPf prf"])
qed

text \<open>This is used in several places, including for the hard half of
Gödel's First and the truth of Gödel formulas (and also for the Rosser variants
of these).\<close>
lemma not_prv_prv_neg_PPf:
assumes [simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}" and p: "\<not> prv \<phi>" and n[simp]: "n \<in> num"
shows "bprv (neg (PPf n \<langle>\<phi>\<rangle>))"
proof-
  have "\<forall>prf\<in>proof. \<not> prfOf prf \<phi>" using prv_prfOf p by auto
  hence "\<forall>prf\<in>proof. bprv (neg (PPf (encPf prf) \<langle>\<phi>\<rangle>))" using not_prfOf_PPf by auto
  thus ?thesis using not_prfOf_PPf using Clean_PPf_encPf by (cases "n \<in> encPf ` proof") auto
qed

lemma consistent_not_prv_not_prv_PPf:
assumes c: consistent
and 0[simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}" "\<not> prv \<phi>" "n \<in> num"
shows "\<not> bprv (PPf n \<langle>\<phi>\<rangle>)"
  using not_prv_prv_neg_PPf[OF 0] c[THEN dwf_dwfd.consistent_B_consistent] unfolding B.consistent_def3 by auto

end \<comment> \<open>context @{locale CleanRepr_Proofs}\<close>

text \<open>The inference of HBL1 from "proof-of" representability, in locale form:\<close>
sublocale CleanRepr_Proofs < wrepr: HBL1
  where P = P
  using HBL1 by unfold_locales auto


subsection \<open>Sufficient condition for the converse of HBL1\<close>

context CleanRepr_Proofs
begin

lemma PP_PPf:
assumes "\<phi> \<in> fmla"
shows "wrepr.PP \<langle>\<phi>\<rangle> = exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>)"
  unfolding wrepr.PP_def using assms
  by (auto simp: PPf_def2 P_def)

text \<open>The converse of HLB1 condition follows from (the standard notion of)
$\omega$-consistency for @{term bprv} and strong representability of proofs:\<close>
lemma \<omega>consistentStd1_HBL1_rev:
assumes oc: "B.\<omega>consistentStd1"
and \<phi>[simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}"
and iPP: "bprv (wrepr.PP \<langle>\<phi>\<rangle>)"
shows "prv \<phi>"
proof-
  have 0: "bprv (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>))" using iPP by (simp add: PP_PPf)
  {assume "\<not> prv \<phi>"
   hence "\<forall>n \<in> num. bprv (neg (PPf n \<langle>\<phi>\<rangle>))" using not_prv_prv_neg_PPf by auto
   hence "\<not> bprv (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>))"
   using oc unfolding B.\<omega>consistentStd1_def using \<phi> by auto
   hence False using 0 by simp
  }
  thus ?thesis by auto
qed

end \<comment> \<open>context @{locale CleanRepr_Proofs}\<close>


section \<open>Second and Third Derivability Conditions\<close>

text \<open>These are only needed for Gödel's Second.\<close>

locale HBL1_2_3 =
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
and prv bprv
and enc ("\<langle>_\<rangle>")
and P
+
assumes
HBL2: "\<And>\<phi> \<chi>. \<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> Fvars \<chi> = {} \<Longrightarrow>
  bprv (imp (cnj (PP \<langle>\<phi>\<rangle>) (PP \<langle>imp \<phi> \<chi>\<rangle>))
           (PP \<langle>\<chi>\<rangle>))"
and
HBL3: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> bprv (imp (PP \<langle>\<phi>\<rangle>) (PP \<langle>PP \<langle>\<phi>\<rangle>\<rangle>))"
begin

text \<open>The implicational form of HBL2:\<close>
lemma HBL2_imp:
 "\<And>\<phi> \<chi>. \<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> Fvars \<chi> = {} \<Longrightarrow>
  bprv (imp (PP \<langle>imp \<phi> \<chi>\<rangle>) (imp (PP \<langle>\<phi>\<rangle>) (PP \<langle>\<chi>\<rangle>)))"
using HBL2 by (simp add: B.prv_cnj_imp B.prv_imp_com)

text \<open>... and its weaker, "detached" version:\<close>
lemma HBL2_imp2:
assumes "\<phi> \<in> fmla" and "\<chi> \<in> fmla" "Fvars \<phi> = {}" "Fvars \<chi> = {}"
assumes "bprv (PP \<langle>imp \<phi> \<chi>\<rangle>)"
shows "bprv (imp (PP \<langle>\<phi>\<rangle>) (PP \<langle>\<chi>\<rangle>))"
using assms by (meson HBL2_imp PP enc imp num B.prv_imp_mp subsetCE)

end \<comment> \<open>context @{locale HBL1_2_3}\<close>

(*<*)
end
(*>*)


