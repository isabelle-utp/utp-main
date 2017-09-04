section {* Modelica.Blocks.Math *}

theory Modelica_Blocks_Math
imports Modelica_Core
begin

definition Add :: "real \<Rightarrow> real \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> ('d,'c::t2_space) hyrel" where 
[urel_defs]: "Add k1 k2 u1 u2 y = [ true | \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>k1\<guillemotright> * $u1\<acute> + \<guillemotleft>k2\<guillemotright> * $u2\<acute>\<rceil>\<^sub>h ]\<^sub>M"
  
definition Add3 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> ('d,'c::t2_space) hyrel" where
[urel_defs]: "Add3 k1 k2 k3 u1 u2 u3 y = [ true | \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>k1\<guillemotright> * $u1\<acute> + \<guillemotleft>k2\<guillemotright> * $u2\<acute> + \<guillemotleft>k3\<guillemotright> * $u3\<acute>\<rceil>\<^sub>h ]\<^sub>M"
  
definition Abs :: "(real \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> ('d,'c::t2_space) hyrel" where
[urel_defs]: "Abs u y = [ true | \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>abs\<guillemotright>\<lparr>$u\<acute>\<rparr>\<^sub>u\<rceil>\<^sub>h ]\<^sub>M"
  
definition Gain :: "'a \<Rightarrow> ('a::real_algebra \<Longrightarrow> 'c) \<Rightarrow> ('a \<Longrightarrow> 'c) \<Rightarrow> ('d,'c::t2_space) hyrel" where
[urel_defs]: "Gain k u y = [ true | \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>k\<guillemotright> * $u\<acute>\<rceil>\<^sub>h ]\<^sub>M"

definition Product :: "('a::real_algebra \<Longrightarrow> 'c::t2_space) \<Rightarrow> ('a \<Longrightarrow> 'c) \<Rightarrow> ('a \<Longrightarrow> 'c) \<Rightarrow> ('d,'c) hyrel" where
[urel_defs]: "Product u1 u2 y = [ true | \<lceil>$y\<acute> =\<^sub>u $u1\<acute> * $u2\<acute>\<rceil>\<^sub>h ]\<^sub>M"

definition Division :: "('a::real_algebra \<Longrightarrow> 'c::t2_space) \<Rightarrow> ('a \<Longrightarrow> 'c) \<Rightarrow> ('a \<Longrightarrow> 'c) \<Rightarrow> ('d,'c) hyrel" where
[urel_defs]: "Division u1 u2 y = [ true | \<lceil>$y\<acute> =\<^sub>u $u1\<acute> * $u2\<acute>\<rceil>\<^sub>h ]\<^sub>M"
  
end