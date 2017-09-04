theory utp_hhoare
  imports utp_hyrel
begin
  
definition 
  HHoare :: "'c::topological_space upred \<Rightarrow> 'c upred \<Rightarrow> ('d,'c) hyrel \<Rightarrow> 'c upred \<Rightarrow> 'c upred \<Rightarrow> bool" ("{_;_}_{_;_}\<^sub>H") where
[upred_defs]: "{a;r}P{b;g}\<^sub>H \<longleftrightarrow> ((\<lceil>a\<rceil>\<^sub>C\<^sub>< \<and> \<lceil>r\<rceil>\<^sub>H) \<Rightarrow> (\<lceil>b\<rceil>\<^sub>C\<^sub>> \<and> \<lceil>g\<rceil>\<^sub>H)) \<sqsubseteq> P"
  

lemma cond_refines: 
  "\<lbrakk> P \<sqsubseteq> (b \<and> Q); P \<sqsubseteq> (\<not>b \<and> R) \<rbrakk> \<Longrightarrow> P \<sqsubseteq> (Q \<triangleleft> b \<triangleright> R)"
  by (rel_auto)

lemma 
  assumes 
    "{c'\<and>b;r}Q{c;g}\<^sub>H"
    "{a;r\<and>(\<not> b)}P{c';g}\<^sub>H"
  shows "{a;r}P[b]\<^sub>HQ{c;g}\<^sub>H"
proof -
  have "{a;r}(Q \<triangleleft> \<lceil>b\<rceil>\<^sub>C\<^sub>< \<triangleright> (P \<and> hInt (\<lambda>\<tau>. \<not> b))){c;g}\<^sub>H"
    apply (simp add: HHoare_def)
    apply (rule cond_refines)
oops

end