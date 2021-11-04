theory sse_operation_negative_quantification
  imports sse_operation_negative sse_boolean_algebra_quantification
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3] (*default Nitpick settings*)

subsection \<open>Definitions and interrelations (infinitary case)\<close>

text\<open>\noindent{We define and interrelate infinitary variants for some previously introduced ('negative') conditions
on operations. We show how they relate to quantifiers as previously defined.}\<close>

text\<open>\noindent{iDM: infinitary De Morgan laws.}\<close>
abbreviation riDM1 ("iDM1\<^sup>_ _") where "iDM1\<^sup>S \<eta> \<equiv> \<eta>(\<^bold>\<Or>S) \<^bold>\<preceq> \<^bold>\<And>Ra[\<eta>|S]"
abbreviation riDM2 ("iDM2\<^sup>_ _") where "iDM2\<^sup>S \<eta> \<equiv> \<^bold>\<Or>Ra[\<eta>|S] \<^bold>\<preceq> \<eta>(\<^bold>\<And>S)"
abbreviation riDM3 ("iDM3\<^sup>_ _") where "iDM3\<^sup>S \<eta> \<equiv> \<eta>(\<^bold>\<And>S) \<^bold>\<preceq> \<^bold>\<Or>Ra[\<eta>|S]"
abbreviation riDM4 ("iDM4\<^sup>_ _") where "iDM4\<^sup>S \<eta> \<equiv> \<^bold>\<And>Ra[\<eta>|S] \<^bold>\<preceq> \<eta>(\<^bold>\<Or>S)"
definition "iDM1 \<eta> \<equiv> \<forall>S. iDM1\<^sup>S \<eta>"
definition "iDM2 \<eta> \<equiv> \<forall>S. iDM2\<^sup>S \<eta>"
definition "iDM3 \<eta> \<equiv> \<forall>S. iDM3\<^sup>S \<eta>"
definition "iDM4 \<eta> \<equiv> \<forall>S. iDM4\<^sup>S \<eta>"
declare iDM1_def[Defs] iDM2_def[Defs] iDM3_def[Defs] iDM4_def[Defs]

lemma CoPw_iDM1: "CoPw \<eta> \<Longrightarrow> iDM1 \<eta>" unfolding Defs by (smt Ra_restr_all sup_char) 
lemma CoPw_iDM2: "CoPw \<eta> \<Longrightarrow> iDM2 \<eta>" unfolding Defs by (smt Ra_restr_ex inf_char)
lemma CoP2_iDM3: "CoP2 \<eta> \<Longrightarrow> iDM3 \<eta>" by (smt CoP2_def Ra_restr_ex iDM3_def inf_char)
lemma CoP1_iDM4: "CoP1 \<eta> \<Longrightarrow> iDM4 \<eta>" by (smt CoP1_def Ra_restr_all iDM4_def sup_char)
lemma "XCoP \<eta> \<Longrightarrow> iDM3 \<eta>" nitpick oops
lemma "XCoP \<eta> \<Longrightarrow> iDM4 \<eta>" nitpick oops

text\<open>\noindent{DM1, DM2, iDM1, iDM2 and CoPw are equivalent.}\<close>
lemma iDM1_rel: "iDM1 \<eta> \<Longrightarrow> DM1 \<eta>" proof -
  assume idm1: "iDM1 \<eta>" 
   { fix a::"\<sigma>" and b::"\<sigma>"
     let ?S="\<lambda>Z. Z=a \<or> Z=b"
     have "\<^bold>\<And>Ra[\<eta>|?S] = \<^bold>\<forall>\<^sup>R\<lparr>?S\<rparr> \<eta>" using Ra_restr_all by blast
     moreover have "\<^bold>\<forall>\<^sup>R\<lparr>?S\<rparr> \<eta> = (\<eta> a) \<^bold>\<and> (\<eta> b)" using meet_def by auto
     ultimately have "\<^bold>\<And>Ra[\<eta>|?S] = (\<eta> a) \<^bold>\<and> (\<eta> b)" by simp
     moreover have "\<^bold>\<Or>?S = a \<^bold>\<or> b" using supremum_def join_def by auto
     moreover from idm1 have "\<eta>(\<^bold>\<Or>?S) \<^bold>\<preceq> \<^bold>\<And>Ra[\<eta>|?S]" by (simp add: iDM1_def)
     ultimately have "\<eta>(a \<^bold>\<or> b) \<^bold>\<preceq> (\<eta> a) \<^bold>\<and> (\<eta> b)" by simp
   } thus ?thesis by (simp add: DM1_def)
 qed
lemma iDM2_rel: "iDM2 \<eta> \<Longrightarrow> DM2 \<eta>" proof -
  assume idm2: "iDM2 \<eta>" 
   { fix a::"\<sigma>" and b::"\<sigma>"
     let ?S="\<lambda>Z. Z=a \<or> Z=b"
     have "\<^bold>\<Or>Ra[\<eta>|?S] = \<^bold>\<exists>\<^sup>R\<lparr>?S\<rparr> \<eta>" using Ra_restr_ex by blast
     moreover have "\<^bold>\<exists>\<^sup>R\<lparr>?S\<rparr> \<eta> = (\<eta> a) \<^bold>\<or> (\<eta> b)" using join_def by auto
     ultimately have "\<^bold>\<Or>Ra[\<eta>|?S] = (\<eta> a) \<^bold>\<or> (\<eta> b)" by simp
     moreover have "\<^bold>\<And>?S = a \<^bold>\<and> b" using infimum_def meet_def by auto
     moreover from idm2 have "\<^bold>\<Or>Ra[\<eta>|?S] \<^bold>\<preceq> \<eta>(\<^bold>\<And>?S)" by (simp add: iDM2_def)
     ultimately have "(\<eta> a) \<^bold>\<or> (\<eta> b) \<^bold>\<preceq> \<eta>(a \<^bold>\<and> b)" by auto
   } thus ?thesis by (simp add: DM2_def)
qed
lemma "DM1 \<eta> = iDM1 \<eta>" using CoPw_iDM1 DM1_CoPw iDM1_rel by blast
lemma "DM2 \<eta> = iDM2 \<eta>" using CoPw_iDM2 DM2_CoPw iDM2_rel by blast
lemma "iDM1 \<eta> = iDM2 \<eta>" using CoPw_iDM1 CoPw_iDM2 DM1_CoPw DM2_CoPw iDM1_rel iDM2_rel by blast

text\<open>\noindent{iDM3/4 entail their finitary variants but not the other way round.}\<close>
lemma iDM3_rel: "iDM3 \<eta> \<Longrightarrow> DM3 \<eta>" proof -
  assume idm3: "iDM3 \<eta>" 
   { fix a::"\<sigma>" and b::"\<sigma>"
     let ?S="\<lambda>Z. Z=a \<or> Z=b"
     have "\<^bold>\<Or>Ra[\<eta>|?S] = \<^bold>\<exists>\<^sup>R\<lparr>?S\<rparr> \<eta>" using Ra_restr_ex by blast
     moreover have "\<^bold>\<exists>\<^sup>R\<lparr>?S\<rparr> \<eta> = (\<eta> a) \<^bold>\<or> (\<eta> b)" using join_def by auto
     ultimately have "\<^bold>\<Or>Ra[\<eta>|?S] = (\<eta> a) \<^bold>\<or> (\<eta> b)" by simp
     moreover have "\<^bold>\<And>?S = a \<^bold>\<and> b" using infimum_def meet_def by auto
     moreover from idm3 have "\<eta>(\<^bold>\<And>?S) \<^bold>\<preceq> \<^bold>\<Or>Ra[\<eta>|?S]" by (simp add: iDM3_def)
     ultimately have "\<eta>(a \<^bold>\<and> b) \<^bold>\<preceq> (\<eta> a) \<^bold>\<or> (\<eta> b)" by auto
   } thus ?thesis by (simp add: DM3_def)
qed
lemma iDM4_rel: "iDM4 \<eta> \<Longrightarrow> DM4 \<eta>" proof -
  assume idm4: "iDM4 \<eta>" 
   { fix a::"\<sigma>" and b::"\<sigma>"
     let ?S="\<lambda>Z. Z=a \<or> Z=b"
     have "\<^bold>\<And>Ra[\<eta>|?S] = \<^bold>\<forall>\<^sup>R\<lparr>?S\<rparr> \<eta>" using Ra_restr_all by blast
     moreover have "\<^bold>\<forall>\<^sup>R\<lparr>?S\<rparr> \<eta> = (\<eta> a) \<^bold>\<and> (\<eta> b)" using meet_def by auto
     ultimately have "\<^bold>\<And>Ra[\<eta>|?S] = (\<eta> a) \<^bold>\<and> (\<eta> b)" by simp
     moreover have "\<^bold>\<Or>?S = a \<^bold>\<or> b" using supremum_def join_def by auto
     moreover from idm4 have "\<^bold>\<And>Ra[\<eta>|?S] \<^bold>\<preceq> \<eta>(\<^bold>\<Or>?S)" by (simp add: iDM4_def)
     ultimately have "(\<eta> a) \<^bold>\<and> (\<eta> b) \<^bold>\<preceq> \<eta>(a \<^bold>\<or> b)" by simp
   } thus ?thesis by (simp add: DM4_def)
 qed
lemma "DM3 \<eta> \<Longrightarrow> iDM3 \<eta>" nitpick oops
lemma "DM4 \<eta> \<Longrightarrow> iDM4 \<eta>" nitpick oops

text\<open>\noindent{Indeed the previous characterization of the infinitary De Morgan laws is fairly general and entails
the traditional version employing quantifiers (though not the other way round).}\<close>
text\<open>\noindent{The first two variants DM1/2 follow easily from DM1/2, iDM1/2 or CoPw (all of them equivalent).}\<close>
lemma iDM1_trad: "iDM1 \<eta> \<Longrightarrow> \<forall>\<pi>. \<eta>(\<^bold>\<exists>x. \<pi> x)  \<^bold>\<preceq>  (\<^bold>\<forall>x. \<eta>(\<pi> x))" by (metis (mono_tags, lifting) CoPw_def DM1_CoPw iDM1_rel)
lemma iDM2_trad: "iDM2 \<eta> \<Longrightarrow> \<forall>\<pi>. (\<^bold>\<exists>x. \<eta>(\<pi> x)) \<^bold>\<preceq> \<eta>(\<^bold>\<forall>x. \<pi> x)" by (metis (mono_tags, lifting) CoPw_def DM2_CoPw iDM2_rel)

text\<open>\noindent{An analogous relationship holds for variants DM3/4, though the proof is less trivial.
To see how let us first consider an intermediate version of the De Morgan laws, obtained as a
particular case of the general variant above, with S as the range of a propositional function.}\<close>
abbreviation "piDM1 \<pi> \<eta> \<equiv> \<eta>(\<^bold>\<Or>Ra(\<pi>)) \<^bold>\<preceq> \<^bold>\<And>Ra[\<eta>|Ra(\<pi>)]"
abbreviation "piDM2 \<pi> \<eta> \<equiv> \<^bold>\<Or>Ra[\<eta>|Ra(\<pi>)] \<^bold>\<preceq> \<eta>(\<^bold>\<And>Ra(\<pi>))"
abbreviation "piDM3 \<pi> \<eta> \<equiv> \<eta>(\<^bold>\<And>Ra(\<pi>)) \<^bold>\<preceq> \<^bold>\<Or>Ra[\<eta>|Ra(\<pi>)]"
abbreviation "piDM4 \<pi> \<eta> \<equiv> \<^bold>\<And>Ra[\<eta>|Ra(\<pi>)] \<^bold>\<preceq> \<eta>(\<^bold>\<Or>Ra(\<pi>))"

text\<open>\noindent{They are entailed (unidirectionally) by the general De Morgan laws.}\<close>
lemma "iDM1 \<eta> \<Longrightarrow> \<forall>\<pi>. piDM1 \<pi> \<eta>" by (simp add: iDM1_def)
lemma "iDM2 \<eta> \<Longrightarrow> \<forall>\<pi>. piDM2 \<pi> \<eta>" by (simp add: iDM2_def)
lemma "iDM3 \<eta> \<Longrightarrow> \<forall>\<pi>. piDM3 \<pi> \<eta>" by (simp add: iDM3_def)
lemma "iDM4 \<eta> \<Longrightarrow> \<forall>\<pi>. piDM4 \<pi> \<eta>" by (simp add: iDM4_def)

text\<open>\noindent{Drawing upon the relationships shown previously we can rewrite the latter two as:}\<close>
lemma iDM3_aux: "piDM3 \<pi> \<eta> \<equiv> \<eta>(\<^bold>\<forall>\<pi>) \<^bold>\<preceq> \<^bold>\<exists>[\<eta>|\<lparr>Ra \<pi>\<rparr>]\<^sup>N" unfolding Ra_all Ra_ex_restr by simp
lemma iDM4_aux: "piDM4 \<pi> \<eta> \<equiv> \<^bold>\<forall>[\<eta>|\<lparr>Ra \<pi>\<rparr>]\<^sup>P \<^bold>\<preceq> \<eta>(\<^bold>\<exists>\<pi>)" unfolding Ra_ex Ra_all_restr by simp

text\<open>\noindent{and thus finally obtain the desired formulas.}\<close>
lemma iDM3_trad: "iDM3 \<eta> \<Longrightarrow> \<forall>\<pi>. \<eta>(\<^bold>\<forall>x. \<pi> x)  \<^bold>\<preceq>  (\<^bold>\<exists>x. \<eta>(\<pi> x))" by (metis Ra_ex_comp2 iDM3_def iDM3_aux comp_apply)
lemma iDM4_trad: "iDM4 \<eta> \<Longrightarrow> \<forall>\<pi>. (\<^bold>\<forall>x. \<eta>(\<pi> x)) \<^bold>\<preceq> \<eta>(\<^bold>\<exists>x. \<pi> x)" by (metis Ra_all_comp1 iDM4_def iDM4_aux comp_apply)

end
