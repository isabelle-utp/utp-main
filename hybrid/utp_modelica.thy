section {* Modelica in Hybrid Reactive Designs *}

theory utp_modelica
imports utp_hrd
begin
  
definition Gain :: "('a::real_algebra \<Longrightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> ('a \<Longrightarrow> 'c) \<Rightarrow> ('d,'c::t2_space) hyrel" where
[urel_defs]: "Gain u k y = \<^bold>R\<^sub>s(true \<turnstile> \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>k\<guillemotright> * $u\<acute>\<rceil>\<^sub>h \<diamondop> false)"

definition Product :: "('a::real_algebra \<Longrightarrow> 'c::t2_space) \<Rightarrow> ('a \<Longrightarrow> 'c) \<Rightarrow> ('a \<Longrightarrow> 'c) \<Rightarrow> ('d,'c) hyrel" where
[urel_defs]: "Product u1 u2 y = \<^bold>R\<^sub>s(true \<turnstile> \<lceil>$y\<acute> =\<^sub>u $u1\<acute> * $u2\<acute>\<rceil>\<^sub>h \<diamondop> false)"

definition Division :: "('a::real_algebra \<Longrightarrow> 'c::t2_space) \<Rightarrow> ('a \<Longrightarrow> 'c) \<Rightarrow> ('a \<Longrightarrow> 'c) \<Rightarrow> ('d,'c) hyrel" where
[urel_defs]: "Division u1 u2 y = \<^bold>R\<^sub>s(\<lceil>$u2\<acute> \<noteq>\<^sub>u 0\<rceil>\<^sub>h \<turnstile> \<lceil>$y\<acute> =\<^sub>u $u1\<acute> * $u2\<acute>\<rceil>\<^sub>h \<diamondop> false)" 

end