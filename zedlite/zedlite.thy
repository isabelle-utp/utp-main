section \<open> Pseudo Z-Notation in Isabelle/UTP \<close>

theory zedlite
  imports "UTP.utp_full"
begin

subsection \<open> Schema Calculus \<close>

definition ZSpec :: "('a \<Longrightarrow> 'b) \<Rightarrow> 'b upred \<Rightarrow> 'b upred \<Rightarrow> 'b hrel" where
[upred_defs]: "ZSpec a p q = ($a\<acute> =\<^sub>u $a \<and> \<lceil>p\<rceil>\<^sub>< \<and> \<lceil>q\<rceil>\<^sub>>)"

abbreviation ZDelta :: "'s upred \<Rightarrow> 's hrel" where
"ZDelta P \<equiv> ZSpec 0\<^sub>L P P"

abbreviation ZDelta_ext :: "('a \<Longrightarrow> 'b) \<Rightarrow> 'a upred \<Rightarrow> 'b hrel" where
"ZDelta_ext a P \<equiv> ZDelta (P \<oplus>\<^sub>p a)"

abbreviation ZSpec_ext :: "('a \<Longrightarrow> 'b) \<Rightarrow> 'a upred \<Rightarrow> 'a upred \<Rightarrow> 'b hrel" where
"ZSpec_ext a P Q \<equiv> ZSpec a (P \<oplus>\<^sub>p a) (Q \<oplus>\<^sub>p a)"

abbreviation ZXi_ext :: "('a \<Longrightarrow> 'b) \<Rightarrow> 'a upred \<Rightarrow> 'b hrel"  where
"ZXi_ext a P \<equiv> ZSpec_ext a P utrue" 

translations
  "CONST ZXi_ext a P" <= "CONST ZSpec_ext a P CONST utrue"

syntax
  "_zspec"      :: "salpha \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_:[_,_]\<^sub>Z")
  "_zdelta"     :: "logic \<Rightarrow> logic" ("\<Delta>[_]")
  "_zdelta_ext" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("\<Delta>[_,_]")
  "_zxi_ext"    :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("\<Xi>[_,_]")

translations
  "_zspec a p q" == "CONST ZSpec a p q"
  "_zdelta P" == "CONST ZDelta P"
  "_zdelta_ext a P" == "CONST ZDelta_ext a P"
  "_zxi_ext a P" == "CONST ZXi_ext a P"

lemma ZDelta_true [simp]: "\<Delta>[true] = true"
  by (rel_simp)

lemma ZDelta_unfold: "\<Delta>[P] = (\<lceil>P\<rceil>\<^sub>< \<and> \<lceil>P\<rceil>\<^sub>>)"
  by (rel_auto)

lemma ZXi_ext_unfold: "\<Xi>[a,P] = ($a\<acute> =\<^sub>u $a \<and> \<lceil>P \<oplus>\<^sub>p a\<rceil>\<^sub><)"
  by (rel_auto)

lemma ZSpec_conj: "(ZSpec a p\<^sub>1 p\<^sub>2 \<and> ZSpec b q\<^sub>1 q\<^sub>2) = ZSpec (a+\<^sub>Lb) (p\<^sub>1\<and>q\<^sub>1) (p\<^sub>2\<and>q\<^sub>2)"
  by (rel_auto)

lemma ZSpec_conj_mult: "(ZSpec a p\<^sub>1 p\<^sub>2 \<and> ZSpec b q\<^sub>1 q\<^sub>2 \<and> R) = (ZSpec (a+\<^sub>Lb) (p\<^sub>1\<and>q\<^sub>1) (p\<^sub>2\<and>q\<^sub>2) \<and> R)"
  by (rel_auto)

lemma Dom_ZSpec_empty: "q \<noteq> false \<Longrightarrow> Pre(\<emptyset>:[p,q]\<^sub>Z) = p"
  by (rel_auto)

lemma Dom_ZSpec_conj: 
  "Pre(\<emptyset>:[p\<^sub>1,p\<^sub>2]\<^sub>Z \<and> Q) = (p\<^sub>1 \<and> Pre(Q \<and> \<lceil>p\<^sub>2\<rceil>\<^sub>>))"
  by (rel_auto)

lemma usedby_Delta [unrest]: "vwb_lens a \<Longrightarrow> {$a,$a\<acute>} \<natural> \<Delta>[a,P]"
  by (rel_auto)

subsection \<open> Alphabet Restriction \<close>

text \<open> This operator can be considered as an annotation that relation @{term P} refers only
  to the variables in @{term a}. \<close>

definition Zres_alpha :: "('\<beta> \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" where
[upred_defs]: "Zres_alpha a P = (P \<restriction>\<^sub>v {$a, $a\<acute>})"

syntax
  "_zres_alpha" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" (infixr "\<lhd>\<^sub>\<alpha>" 85)

translations
  "_zres_alpha a P" == "CONST Zres_alpha a P"

lemma res_alpha_all:
  "\<Sigma> \<lhd>\<^sub>\<alpha> P = P"
  by (rel_auto)

text \<open> The following theorems show how the alphabet annotations can be refined for various
  schema operators. \<close>

named_theorems mark_alpha

lemma mark_alpha_Delta_ext [mark_alpha]:
  "vwb_lens a \<Longrightarrow> (\<Sigma> \<lhd>\<^sub>\<alpha> \<Delta>[a,P]) = (a \<lhd>\<^sub>\<alpha> \<Delta>[a,P])"
  by (rel_auto)

lemma mark_alpha_Xi_ext [mark_alpha]:
  "vwb_lens a \<Longrightarrow> (\<Sigma> \<lhd>\<^sub>\<alpha> \<Xi>[a,P]) = (a \<lhd>\<^sub>\<alpha> \<Xi>[a,P])"
  by (rel_auto)

lemma mark_alpha_Xi_ext' [mark_alpha]:
  "vwb_lens a \<Longrightarrow> (\<Sigma> \<lhd>\<^sub>\<alpha> a:[P \<oplus>\<^sub>p a,true]\<^sub>Z) = (a \<lhd>\<^sub>\<alpha> a:[P \<oplus>\<^sub>p a,true]\<^sub>Z)"
  by (rel_auto)

lemma mark_alpha_rel_aext [mark_alpha]:
  "vwb_lens a \<Longrightarrow> (\<Sigma> \<lhd>\<^sub>\<alpha> (P \<oplus>\<^sub>r a)) = (a \<lhd>\<^sub>\<alpha> (P \<oplus>\<^sub>r a))"
  by (rel_auto)

lemma mark_alpha_all_conj [mark_alpha]:
  "\<Sigma> \<lhd>\<^sub>\<alpha> (P \<and> Q) = ((\<Sigma> \<lhd>\<^sub>\<alpha> P) \<and> (\<Sigma> \<lhd>\<^sub>\<alpha> Q))"
  by (rel_auto)

subsection \<open> Calculating Preconditions \<close>

named_theorems pre

declare prepost [pre]

text \<open> Calculation of preconditions for conjoined relations is in general very difficult. However,
  if we have annotations for disjoint alphabets then the following easier law applies. \<close>

lemma pre_conj_disj_alphas [pre]:
  "\<lbrakk> vwb_lens a; vwb_lens b; a \<bowtie> b \<rbrakk> \<Longrightarrow> Pre(a \<lhd>\<^sub>\<alpha> P \<and> b \<lhd>\<^sub>\<alpha> Q) = (Pre(a \<lhd>\<^sub>\<alpha> P) \<and> Pre(b \<lhd>\<^sub>\<alpha> Q))"
  by (rel_auto, metis lens_indep_get mwb_lens_def vwb_lens_mwb weak_lens.put_get)

lemma pre_marked_aext [pre]: "vwb_lens a \<Longrightarrow> Pre(a \<lhd>\<^sub>\<alpha> (P \<oplus>\<^sub>r a)) = Pre (\<Sigma> \<lhd>\<^sub>\<alpha> P) \<oplus>\<^sub>p a"
  by (rel_auto, metis vwb_lens_wb wb_lens_def weak_lens.put_get)

lemma pre_apply_res:
  "Pre P = Pre (\<Sigma> \<lhd>\<^sub>\<alpha> P)"
  by (rel_auto)

text \<open> We can attempt to calculate a precondition by first marking all the alphabets, and
  then using these to try and split conjoined predicates. \<close>

method zcalcpre = (subst pre_apply_res, simp add: mark_alpha pre utp_pred_laws.inf_aci)

end