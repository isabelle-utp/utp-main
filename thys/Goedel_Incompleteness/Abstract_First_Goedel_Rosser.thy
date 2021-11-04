chapter \<open>Abstract Formulations of Gödel-Rosser's First Incompleteness Theorem\<close>

(*<*)
theory Abstract_First_Goedel_Rosser
  imports Rosser_Formula Standard_Model_More
begin
(*>*)

text \<open>The development here is very similar to that of Gödel First Incompleteness Theorem.
It lacks classical logical variants, since for them Rosser's trick does bring
any extra value.\<close>

section \<open>Proof-Theoretic Versions\<close>

context Rosser_Form_Proofs
begin

lemma NN_neg_unique_xx':
  assumes [simp]:"\<phi> \<in> fmla" "Fvars \<phi> = {}"
  shows
    "bprv (imp (NN \<langle>\<phi>\<rangle> (Var xx'))
          (eql \<langle>neg \<phi>\<rangle> (Var xx')))"
  using B.prv_subst[of yy _ "Var xx'", OF _ _ _ NN_neg_unique[OF assms]] by fastforce

lemma NN_imp_xx':
  assumes [simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}" "\<chi> \<in> fmla"
  shows "bprv (imp (subst \<chi> \<langle>neg \<phi>\<rangle> xx')
                   (all xx' (imp (NN \<langle>\<phi>\<rangle> (Var xx')) \<chi>)))"
proof-
  have 2: "bprv (imp (eql \<langle>neg \<phi>\<rangle> (Var xx')) (imp (subst \<chi> \<langle>neg \<phi>\<rangle> xx') \<chi>))"
    using B.prv_eql_subst_trm[of xx' \<chi> "\<langle>neg \<phi>\<rangle>" "Var xx'", simplified] .
  have 1: "bprv (imp (subst \<chi> \<langle>neg \<phi>\<rangle> xx') (imp (eql \<langle>neg \<phi>\<rangle> (Var xx')) \<chi>))"
    by (simp add: "2" B.prv_imp_com)
  have 0: "bprv (imp (subst \<chi> \<langle>neg \<phi>\<rangle> xx') (imp (NN \<langle>\<phi>\<rangle> (Var xx')) \<chi>))"
    using 1
    by (elim B.prv_prv_imp_trans[rotated 3])
      (auto simp add: B.prv_imp_com B.prv_imp_monoR NN_neg_unique_xx')
  show ?thesis by (rule B.prv_all_imp_gen) (auto simp: 0)
qed

lemma goedel_rosser_first_theEasyHalf:
  assumes c: "consistent"
  shows "\<not> prv \<phi>R"
proof
  assume 0: "prv \<phi>R"
  then obtain "prf" where [simp]: "prf \<in> proof" and "prfOf prf \<phi>R" using prv_prfOf by auto
  hence 00: "bprv (PPf (encPf prf) \<langle>\<phi>R\<rangle>)" using prfOf_PPf by auto
  from dwf_dwfd.d_dwf.bprv_prv'[OF _ 00, simplified] have b00: "prv (PPf (encPf prf) \<langle>\<phi>R\<rangle>)" .
  have "\<not> prv (neg \<phi>R)" using 0 c unfolding consistent_def3 by auto
  hence "\<forall> prf \<in> proof.  \<not> prfOf prf (neg \<phi>R)" using 00 prv_prfOf by auto
  hence "bprv (neg (PPf p \<langle>neg \<phi>R\<rangle>))" if "p \<in> num" for p using not_prfOf_PPf Clean_PPf_encPf that
    by (cases "p \<in> encPf ` proof") auto
  hence 1: "prv (all zz (imp (LLq (Var zz) (encPf prf)) (neg (PPf (Var zz) \<langle>neg \<phi>R\<rangle>))))"
    (* here use locale assumption about the order-like relation: *)
    by (intro LLq_num) auto
  have 11: "prv (RR (encPf prf) \<langle>\<phi>R\<rangle>)"
    using NN_imp_xx'[of \<phi>R "neg (PPf (Var zz) (Var xx'))", simplified]
    by (auto simp add: RR_def2 R_def
      intro!: prv_all_congW[OF _ _ _ _ 1] prv_imp_monoL[OF _ _ _ dwf_dwfd.d_dwf.bprv_prv'])
  have 3: "prv (cnj (PPf (encPf prf) \<langle>\<phi>R\<rangle>) (RR (encPf prf) \<langle>\<phi>R\<rangle>))"
    by (rule prv_cnjI[OF _ _ b00 11]) auto
  have "prv ((PP' \<langle>\<phi>R\<rangle>))" unfolding PP'_def P'_def
     using 3 by (auto intro: prv_exiI[of _ _ "encPf prf"])
  moreover have "prv (neg (PP' \<langle>\<phi>R\<rangle>))"
    using prv_eqv_prv[OF _ _ 0 prv_\<phi>R_eqv] by auto
  ultimately show False using c unfolding consistent_def3 by auto
qed

lemma goedel_rosser_first_theHardHalf:
  assumes c: "consistent"
  shows "\<not> prv (neg \<phi>R)"
proof
  assume 0: "prv (neg \<phi>R)"
  then obtain "prf" where [simp,intro!]: "prf \<in> proof" and pr: "prfOf prf (neg \<phi>R)" using prv_prfOf by auto
  define p where p: "p = encPf prf"
  have [simp,intro!]: "p \<in> num" unfolding p by auto
  have 11: "bprv (PPf p \<langle>neg \<phi>R\<rangle>)" using pr prfOf_PPf unfolding p by auto
  have 1: "bprv (NN \<langle>\<phi>R\<rangle> \<langle>neg \<phi>R\<rangle>)" using NN_neg by simp

  have "\<not> prv \<phi>R" using 0 c unfolding consistent_def3 by auto
  from not_prv_prv_neg_PPf[OF _ _ this]
  have b2: "\<forall> r \<in> num. bprv (neg (PPf r \<langle>\<phi>R\<rangle>))" by auto
  hence 2: "\<forall> r \<in> num. prv (neg (PPf r \<langle>\<phi>R\<rangle>))"
    by (auto intro: dwf_dwfd.d_dwf.bprv_prv')

  obtain P where P[simp,intro!]: "P \<subseteq>num" "finite P"
    and 3: "prv (dsj (sdsj {eql (Var yy) r |r. r \<in> P}) (LLq p (Var yy)))"
    (* here use the other locale assumption about the order-like relation: *)
    using LLq_num2 by auto

  have "prv (imp (cnj (PPf (Var yy) \<langle>\<phi>R\<rangle>) (RR (Var yy) \<langle>\<phi>R\<rangle>)) fls)"
  proof(rule prv_dsj_cases[OF _ _ _ 3])
    {fix r assume r: "r \<in> P" hence rn[simp]: "r \<in> num" using P(1) by blast
      have "prv (imp (cnj (PPf r \<langle>\<phi>R\<rangle>) (RR r \<langle>\<phi>R\<rangle>)) fls)"
        using 2 unfolding neg_def
        by (metis FvarsT_num PPf RR rn \<phi>R all_not_in_conv cnj enc fls imp in_num prv_imp_cnj3L prv_imp_mp)
      hence "prv (imp (eql (Var yy) r)
                (imp (cnj (PPf (Var yy) \<langle>\<phi>R\<rangle>) (RR (Var yy) \<langle>\<phi>R\<rangle>)) fls))"
        using prv_eql_subst_trm_id[of yy "cnj (PPf (Var yy) \<langle>\<phi>R\<rangle>) (RR (Var yy) \<langle>\<phi>R\<rangle>)" r,simplified]
        unfolding neg_def[symmetric]
        by (intro prv_neg_imp_imp_trans) auto
    }
    thus "prv (imp (sdsj {eql (Var yy) r |r. r \<in> P})
              (imp (cnj (PPf (Var yy) \<langle>\<phi>R\<rangle>) (RR (Var yy) \<langle>\<phi>R\<rangle>)) fls))"
       using Var P(1) eql by (intro prv_sdsj_imp) (auto 0 0 simp: set_rev_mp)
  next
    let ?\<phi> = "all xx' (imp (NN \<langle>\<phi>R\<rangle> (Var xx')) (neg (PPf p (Var xx'))))"
    have "bprv (neg ?\<phi>)"
      using 1 11 by (intro B.prv_imp_neg_allWI[where t = "\<langle>neg \<phi>R\<rangle>"]) (auto intro: B.prv_prv_neg_imp_neg)
    hence "prv (neg ?\<phi>)" by (auto intro: dwf_dwfd.d_dwf.bprv_prv')
    hence 00: "prv (imp (LLq p (Var yy))
                       (imp (imp (LLq p (Var yy)) ?\<phi>) fls))"
      unfolding neg_def[symmetric] by (intro prv_imp_neg_imp_neg_imp) auto
    have "prv (imp (LLq p (Var yy))
              (imp (RR (Var yy) \<langle>\<phi>R\<rangle>) fls))"
      unfolding neg_def[symmetric] using 00[folded neg_def]
      by (auto simp add: RR_def2 R_def intro!: prv_imp_neg_allI[where t = p])
    thus "prv (imp (LLq p (Var yy))
              (imp (cnj (PPf (Var yy) \<langle>\<phi>R\<rangle>) (RR (Var yy) \<langle>\<phi>R\<rangle>)) fls))"
      unfolding neg_def[symmetric] by (intro prv_imp_neg_imp_cnjR) auto
  qed(auto, insert Var P(1) eql, simp_all add: set_rev_mp)
  hence "prv (neg (exi yy (cnj (PPf (Var yy) \<langle>\<phi>R\<rangle>) (RR (Var yy) \<langle>\<phi>R\<rangle>))))"
    unfolding neg_def[symmetric] by (intro prv_neg_neg_exi) auto
  hence "prv (neg (PP' \<langle>\<phi>R\<rangle>))" unfolding PP'_def P'_def by simp
  hence "prv \<phi>R" using prv_\<phi>R_eqv by (meson PP' \<phi>R enc in_num neg prv_eqv_prv_rev)
  with \<open>\<not> prv \<phi>R\<close> show False using c unfolding consistent_def3 by auto
qed

theorem goedel_rosser_first:
  assumes "consistent"
  shows "\<not> prv \<phi>R \<and> \<not> prv (neg \<phi>R)"
  using assms goedel_rosser_first_theEasyHalf goedel_rosser_first_theHardHalf by blast

theorem goedel_rosser_first_ex:
  assumes "consistent"
  shows "\<exists> \<phi>. \<phi> \<in> fmla \<and> \<not> prv \<phi> \<and> \<not> prv (neg \<phi>)"
  using assms goedel_rosser_first by (intro exI[of _ \<phi>R]) blast

end \<comment> \<open>context @{locale Rosser_Form}\<close>


section \<open>Model-Theoretic Versions\<close>

subsection \<open>First model-theoretic version\<close>

locale Rosser_Form_Proofs_Minimal_Truth =
Rosser_Form_Proofs
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi
  fls
  prv bprv
  Lq
  dsj
  "proof" prfOf
  enc
  N S
  encPf
  Pf
+
Minimal_Truth_Soundness
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
and Lq
and prv bprv
and enc ("\<langle>_\<rangle>")
and N S P
and "proof" :: "'proof set" and prfOf encPf
and Pf
and isTrue
begin

lemma Fvars_PP'[simp]: "Fvars (PP' \<langle>\<phi>R\<rangle>) = {}" unfolding PP'_def
  by (subst Fvars_subst) auto

lemma Fvars_RR'[simp]: "Fvars (RR (Var yy) \<langle>\<phi>R\<rangle>) = {yy}"
  unfolding RR_def
  by (subst Fvars_psubst) (fastforce intro!: exI[of _ "{yy}"])+

lemma isTrue_PPf_implies_\<phi>R:
assumes "isTrue (all yy (neg (PPf (Var yy) \<langle>\<phi>R\<rangle>)))"
(is "isTrue ?H")
shows "isTrue \<phi>R"
proof-
  define F where "F \<equiv> RR (Var yy) \<langle>\<phi>R\<rangle>"
  have [simp]: "F \<in> fmla" "Fvars F = {yy}"
    unfolding F_def by auto
  have [simp]: "exi yy (PPf (Var yy) \<langle>\<phi>R\<rangle>) \<in> fmla"
    unfolding PPf_def by auto

  have 1: "bprv
     (imp (all yy (neg (PPf (Var yy) \<langle>\<phi>R\<rangle>)))
       (neg (exi yy (PPf (Var yy) \<langle>\<phi>R\<rangle>))))"
  (is "bprv (imp (all yy (neg ?G)) (neg (exi yy ?G)))")
    using B.prv_all_neg_imp_neg_exi[of yy ?G] by auto
  have 2: "bprv (imp (neg (exi yy ?G)) (neg (exi yy (cnj ?G F))))"
    by (auto intro!: B.prv_imp_neg_rev B.prv_exi_cong B.prv_imp_cnjL)
  have "bprv (imp (all yy (neg ?G)) (neg (exi yy (cnj ?G F))))"
    using B.prv_prv_imp_trans[OF _ _ _  1 2] by simp
  hence "bprv (imp ?H (neg (PP' \<langle>\<phi>R\<rangle>)))"
    unfolding PP'_def P'_def
    by (simp add: F_def)
  from B.prv_prv_imp_trans[OF _ _ _  this bprv_imp_\<phi>R]
  have "bprv (imp ?H \<phi>R)" by auto
  from prv_imp_implies_isTrue[OF _ _ _ _ this assms, simplified]
  show ?thesis .
qed

theorem isTrue_\<phi>R:
  assumes "consistent"
  shows "isTrue \<phi>R"
proof-
  have "\<forall> n \<in> num. bprv (neg (PPf n \<langle>\<phi>R\<rangle>))"
    using not_prv_prv_neg_PPf[OF _ _ goedel_rosser_first_theEasyHalf[OF assms]]
    by auto
  hence "\<forall> n \<in> num. isTrue (neg (PPf n \<langle>\<phi>R\<rangle>))" by (auto intro: sound_isTrue)
  hence "isTrue (all yy (neg (PPf (Var yy) \<langle>\<phi>R\<rangle>)))" by (auto intro: isTrue_all)
  thus ?thesis using isTrue_PPf_implies_\<phi>R by auto
qed


theorem goedel_rosser_first_strong: "consistent \<Longrightarrow> \<not> prv \<phi>R \<and> \<not> prv (neg \<phi>R) \<and> isTrue \<phi>R"
  using isTrue_\<phi>R goedel_rosser_first by blast

theorem goedel_rosser_first_strong_ex:
"consistent \<Longrightarrow> \<exists> \<phi>. \<phi> \<in> fmla \<and> \<not> prv \<phi> \<and> \<not> prv (neg \<phi>) \<and> isTrue \<phi>"
  using goedel_rosser_first_strong by (intro exI[of _ \<phi>R]) blast

end \<comment> \<open>context @{locale Rosser_Form_Proofs_Minimal_Truth}\<close>


subsection \<open>Second model-theoretic version\<close>

context Rosser_Form
begin
print_context
end

locale Rosser_Form_Minimal_Truth_Soundness_HBL1iff_Compl_Pf =
Rosser_Form
  var trm fmla Var
  FvarsT substT Fvars subst
  num
  eql cnj imp all exi
  fls
  prv bprv
  Lq
  dsj
  enc
  N
  S
  P
+
Minimal_Truth_Soundness_HBL1iff_Compl_Pf
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
  enc
  prv bprv
  P
  isTrue
  Pf
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and eql cnj imp all exi
and fls
and dsj
and num
and prv bprv
and Lq
and enc ("\<langle>_\<rangle>")
and N S
and isTrue
and P Pf



locale Rosser_Form_Minimal_Truth_Soundness_HBL1iff_Compl_Pf_Compl_NegPf =
Rosser_Form_Minimal_Truth_Soundness_HBL1iff_Compl_Pf
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
  prv bprv
  Lq
  enc
  N S
  isTrue
  P
  Pf
+
M : Minimal_Truth_Soundness_HBL1iff_Compl_Pf_Compl_NegPf
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
  enc
  prv bprv
  N
  isTrue
  Pf
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and eql cnj imp all exi
and fls
and dsj
and num
and prv bprv
and Lq
and enc ("\<langle>_\<rangle>")
and N S P
and isTrue
and Pf

sublocale
  Rosser_Form_Minimal_Truth_Soundness_HBL1iff_Compl_Pf_Compl_NegPf <
  recover_proofs: Rosser_Form_Proofs_Minimal_Truth
  where prfOf = prfOf and "proof" = "proof" and encPf = encPf
  and prv = prv and bprv = bprv
  by standard

context Rosser_Form_Minimal_Truth_Soundness_HBL1iff_Compl_Pf_Compl_NegPf
begin
thm recover_proofs.goedel_rosser_first_strong
end

(*<*)
end
(*>*)

