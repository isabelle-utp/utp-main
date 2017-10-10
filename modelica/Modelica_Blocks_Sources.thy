section {* Modelica.Blocks.Sources *}

theory Modelica_Blocks_Sources
imports Modelica_Core
begin

definition Clock :: "real \<Rightarrow> real \<Rightarrow> (real \<Longrightarrow> 'c::t2_space) \<Rightarrow> ('d,'c) hyrel" where
[urel_defs]: "Clock offset startTime y = [ true | \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>offset + (if ti < startTime then 0 else ti - startTime)\<guillemotright>\<rceil>\<^sub>h ]\<^sub>M"

definition Constant :: "'a::real_algebra \<Rightarrow> ('a \<Longrightarrow> 'c::t2_space) \<Rightarrow> ('d,'c) hyrel" where
[urel_defs]: "Constant k y = [ true | \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>k\<guillemotright>\<rceil>\<^sub>h ]\<^sub>M"

definition Step :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real \<Longrightarrow> 'c::t2_space) \<Rightarrow> ('d,'c) hyrel" where
"Step offset startTime height y =
  [true | \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>offset + (if ti < startTime then 0 else height)\<guillemotright>\<rceil>\<^sub>h ]\<^sub>M"

definition Ramp :: 
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real \<Longrightarrow> 'c::t2_space) \<Rightarrow> ('d,'c) hyrel" where
[urel_defs]: "Ramp height duration offset startTime y
                = [ \<guillemotleft>duration\<guillemotright> \<ge>\<^sub>u 0 
                  | \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>offset + (if ti < startTime then 0 
                                       else if ti < startTime + duration 
                                       then (ti - startTime) * height / duration
                                       else height)\<guillemotright>\<rceil>\<^sub>h ]\<^sub>M"
          
definition Sine :: 
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real \<Longrightarrow> 'c::t2_space) \<Rightarrow> ('d,'c) hyrel" where
"Sine ampltitude freqHz phase offset startTime y =
  [true | \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>offset + (if ti < startTime 
                             then 0 
                             else sin(2 * pi * freqHz * (ti - startTime) + phase))\<guillemotright>\<rceil>\<^sub>h]\<^sub>M"
  

end