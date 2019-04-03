section \<open> Pseudo Z-Notation in Isabelle/UTP \<close>

theory zedlite
  imports "UTP.utp_full"
begin

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

abbreviation "pre \<equiv> Dom"

syntax
  "_zspec"      :: "salpha \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_:[_,_]\<^sub>Z")
  "_zdelta"     :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("\<Delta>[_]")
  "_zdelta_ext" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("\<Delta>[_,_]")
  "_zxi_ext"    :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("\<Xi>[_,_]")

translations
  "_zspec a p q" == "CONST ZSpec a p q"
  "_zdelta P" == "CONST ZDelta P"
  "_zdelta_ext a P" == "CONST ZDelta_ext a P"
  "_zxi_ext a P" == "CONST ZXi_ext a P"

lemma ZDelta_unfold: "\<Delta>[P] = (\<lceil>P\<rceil>\<^sub>< \<and> \<lceil>P\<rceil>\<^sub>>)"
  by (rel_auto)

lemma ZXi_ext_unfold: "\<Xi>[a,P] = ($a\<acute> =\<^sub>u $a \<and> \<lceil>P \<oplus>\<^sub>p a\<rceil>\<^sub><)"
  by (rel_auto)

lemma ZSpec_conj: "(ZSpec a p\<^sub>1 p\<^sub>2 \<and> ZSpec b q\<^sub>1 q\<^sub>2) = ZSpec (a+\<^sub>Lb) (p\<^sub>1\<and>q\<^sub>1) (p\<^sub>2\<and>q\<^sub>2)"
  by (rel_auto)

lemma ZSpec_conj_mult: "(ZSpec a p\<^sub>1 p\<^sub>2 \<and> ZSpec b q\<^sub>1 q\<^sub>2 \<and> R) = (ZSpec (a+\<^sub>Lb) (p\<^sub>1\<and>q\<^sub>1) (p\<^sub>2\<and>q\<^sub>2) \<and> R)"
  by (rel_auto)

lemma Dom_ZSpec_empty: "q \<noteq> false \<Longrightarrow> Dom(\<emptyset>:[p,q]\<^sub>Z) = p"
  by (rel_auto)

lemma Dom_ZSpec_conj: 
  "Dom(\<emptyset>:[p\<^sub>1,p\<^sub>2]\<^sub>Z \<and> Q) = (p\<^sub>1 \<and> Dom(Q \<and> \<lceil>p\<^sub>2\<rceil>\<^sub>>))"
  by (rel_auto)

lemma usedby_Delta [unrest]: "vwb_lens a \<Longrightarrow> {$a,$a\<acute>} \<natural> \<Delta>[a,P]"
  by (rel_auto)

end