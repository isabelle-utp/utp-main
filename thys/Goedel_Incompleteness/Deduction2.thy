chapter \<open>Deduction with Two Provability Relations\<close>
(*<*)
theory Deduction2 imports "Syntax_Independent_Logic.Deduction"
begin
(*>*)

text \<open>We work with two provability relations:
provability @{term prv} and basic provability @{term bprv}.\<close>

section \<open>From Deduction with One Provability Relation to Two\<close>

locale Deduct2 =
Deduct
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi
  prv
+
B: Deduct
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi
  bprv
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and num
and eql cnj imp all exi
and prv bprv
+
assumes bprv_prv: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> bprv \<phi> \<Longrightarrow> prv \<phi>"
begin

(* Removing the sentence (empty Fvars) hypothesis from bprv_prv *)
lemma bprv_prv':
  assumes \<phi>: "\<phi> \<in> fmla" and b: "bprv \<phi>"
  shows "prv \<phi>"
proof-
  obtain V where V: "Fvars \<phi> = V" by blast
  have VV: "V \<subseteq> var" using Fvars V \<phi> by blast
  have f: "finite V" using V finite_Fvars[OF \<phi>] by auto
  thus ?thesis using \<phi> b V VV
  proof(induction V arbitrary: \<phi> rule: finite.induct)
    case (emptyI \<phi>)
    then show ?case by (simp add: bprv_prv)
  next
    case (insertI W v \<phi>)
    show ?case proof(cases "v \<in> W")
      case True
      thus ?thesis
      using insertI.IH[OF \<open>\<phi> \<in> fmla\<close>] insertI.prems
      by (simp add: insert_absorb)
    next
      case False
      hence 1: "Fvars (all v \<phi>) = W"
        using insertI.prems by auto
      moreover have "bprv (all v \<phi>)"
        using B.prv_all_gen insertI.prems by auto
      ultimately have "prv (all v \<phi>)" using insertI by auto
      thus ?thesis using allE_id insertI.prems by blast
    qed
  qed
qed

end \<comment> \<open>context @{locale Deduct2}\<close>


locale Deduct2_with_False =
Deduct_with_False
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  num
  prv
+
B: Deduct_with_False
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  num
  bprv
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and eql cnj imp all exi
and fls
and num
and prv bprv
+
assumes bprv_prv: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> bprv \<phi> \<Longrightarrow> prv \<phi>"

sublocale Deduct2_with_False < d_dwf: Deduct2
  by standard (fact bprv_prv)

context Deduct2_with_False begin

lemma consistent_B_consistent: "consistent \<Longrightarrow> B.consistent"
  using B.consistent_def bprv_prv consistent_def by blast

end \<comment> \<open>context @{locale Deduct2_with_False}\<close>

locale Deduct2_with_False_Disj =
Deduct_with_False_Disj
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
  prv
+
B: Deduct_with_False_Disj
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
  bprv
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and eql cnj imp all exi
and fls
and dsj
and num
and prv bprv
+
assumes bprv_prv: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> bprv \<phi> \<Longrightarrow> prv \<phi>"

sublocale Deduct2_with_False_Disj < dwf_dwfd: Deduct2_with_False
  by standard (fact bprv_prv)

(* Factoring in a strict-order-like relation (not actually required to be an order): *)
locale Deduct2_with_PseudoOrder =
Deduct2_with_False_Disj
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
  prv bprv
+
Syntax_PseudoOrder
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
  Lq
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and eql cnj imp all exi
and fls
and dsj
and num
and prv bprv
and Lq
+
assumes
(* We do not assume any ordering properties, but only these two axioms, Lq_num and Lq_num2,
which (interestingly) would be satisfied by both \<le> and < within a sufficiently strong
arithmetic such as Robinson's Q *)
(* For each formula \<phi>(z) and numeral q, if \<phi>(p) is provable for all p
then \<forall> z \<le> q. \<phi>(z) is provable.
(Note that a more natural property would assume \<phi>(p) is provable for all p\<le>q,
but we can get away with the stronger assumption (on the left of the implication). )
*)
Lq_num:
"let LLq = (\<lambda> t1 t2. psubst Lq [(t1,zz), (t2,yy)]) in
 \<forall> \<phi> \<in> fmla. \<forall> q \<in> num. Fvars \<phi> = {zz} \<and> (\<forall> p \<in> num. bprv (subst \<phi> p zz))
    \<longrightarrow> prv (all zz (imp (LLq (Var zz) q) \<phi>))"
and
(* For each numeral p, there exists a finite set P such that it is provable that
\<forall> y. (\<Or>p\<in>P. x = p) \<or> y \<le> p
(where we write \<le> instead of Lq, but could also think of <):
*)
Lq_num2:
"let LLq = (\<lambda> t1 t2. psubst Lq [(t1,zz), (t2,yy)]) in
 \<forall> p \<in> num. \<exists> P \<subseteq> num. finite P \<and> prv (dsj (sdsj {eql (Var yy) r | r. r \<in> P}) (LLq p (Var yy)))"
begin

lemma LLq_num:
assumes "\<phi> \<in> fmla" "q \<in> num" "Fvars \<phi> = {zz}" "\<forall> p \<in> num. bprv (subst \<phi> p zz)"
shows "prv (all zz (imp (LLq (Var zz) q) \<phi>))"
using assms Lq_num unfolding LLq_def by auto

lemma LLq_num2:
assumes "p \<in> num"
shows "\<exists> P \<subseteq> num. finite P \<and> prv (dsj (sdsj {eql (Var yy) r | r. r \<in> P}) (LLq p (Var yy)))"
using assms Lq_num2 unfolding LLq_def by auto

end \<comment> \<open>context @{locale Deduct2_with_PseudoOrder}\<close>

section \<open>Factoring In Explicit Proofs\<close>

locale Deduct_with_Proofs =
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
and prv
+
fixes
"proof" :: "'proof set"
and
prfOf :: "'proof \<Rightarrow> 'fmla \<Rightarrow> bool"
assumes
\<comment> \<open>Provability means there exists a proof (only needed for sentences):\<close>
prv_prfOf: "\<And> \<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> prv \<phi> \<longleftrightarrow> (\<exists> prf \<in> proof. prfOf prf \<phi>)"

(* We consider proof structure only for prv, not for bprv *)
locale Deduct2_with_Proofs =
Deduct2_with_False_Disj
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
  prv bprv
+
Deduct_with_Proofs
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
  prv
  "proof" prfOf
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and eql cnj imp all exi
and fls
and dsj
and num
and prv bprv
and "proof" :: "'proof set" and prfOf

locale Deduct2_with_Proofs_PseudoOrder =
Deduct2_with_Proofs
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
  prv bprv
  "proof" prfOf
+
Deduct2_with_PseudoOrder
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
  prv bprv
  Lq
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and eql cnj imp all exi
and fls
and dsj
and num
and prv bprv
and "proof" :: "'proof set" and prfOf
and Lq

(*<*)
end
(*>*)