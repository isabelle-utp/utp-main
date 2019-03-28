section \<open> Pseudo Z-Notation in Isabelle/UTP \<close>

theory zedlite
  imports "UTP.utp_full"
begin

definition ZDelta :: "'s upred \<Rightarrow> 's hrel" ("\<Delta>[_]") where
[upred_defs]: "\<Delta>[P] = (\<lceil>P\<rceil>\<^sub>< \<and> \<lceil>P\<rceil>\<^sub>>)"

abbreviation ZDelta_ext :: "('a \<Longrightarrow> 'b) \<Rightarrow> 'a upred \<Rightarrow> 'b hrel" ("\<Delta>[_,_]") where
"\<Delta>[a,P] \<equiv> \<Delta>[P \<oplus>\<^sub>p a]"

definition ZXi_ext :: "('a \<Longrightarrow> 'b) \<Rightarrow> 'a upred \<Rightarrow> 'b hrel"  where
[upred_defs]: "ZXi_ext a P = (\<Delta>[a,P] \<and> $a\<acute> =\<^sub>u $a)"

syntax
  "_zxi_ext" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("\<Xi>[_,_]")

translations
  "_zxi_ext a P" == "CONST ZXi_ext a P"

end