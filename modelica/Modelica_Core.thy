section {* Modelica Core *}

theory Modelica_Core
imports "../hybrid/utp_hrd"
begin

abbreviation ModelicaBlock ("[_ | _]\<^sub>M") where
"[P | Q]\<^sub>M \<equiv> \<^bold>R\<^sub>s(P \<turnstile> ($tr <\<^sub>u $tr\<acute> \<and> Q) \<diamondop> false)"

lemma preR_simple_block [rdes]: "pre\<^sub>R([\<lceil>P\<^sub>1\<rceil>\<^sub>h | \<lceil>Q\<^sub>1\<rceil>\<^sub>h]\<^sub>M) = (\<not>(R1(\<not> \<lceil>P\<^sub>1\<rceil>\<^sub>h)))"
  by (rel_auto)

lemma periR_simple_block [rdes]: "peri\<^sub>R([\<lceil>P\<^sub>1\<rceil>\<^sub>h | \<lceil>Q\<^sub>1\<rceil>\<^sub>h]\<^sub>M) = (\<not>(R1(\<not> \<lceil>P\<^sub>1\<rceil>\<^sub>h)) \<Rightarrow> ($tr <\<^sub>u $tr\<acute> \<and> \<lceil>Q\<^sub>1\<rceil>\<^sub>h))"
  by (rel_auto)
  
lemma postR_simple_block [rdes]: "post\<^sub>R([\<lceil>P\<rceil>\<^sub>h | \<lceil>Q\<rceil>\<^sub>h]\<^sub>M) = R1(\<not> \<lceil>P\<rceil>\<^sub>h)"
  by (rel_auto)
    
lemma NSRD_simple_block [closure]: "[\<lceil>P\<^sub>1\<rceil>\<^sub>h | \<lceil>Q\<^sub>1\<rceil>\<^sub>h]\<^sub>M is NSRD"
  apply (rule NSRD_intro)
  apply (rule RHS_tri_design_is_SRD)
  apply (simp_all add: unrest rdes neg_hInt_R1_true)
done
end
