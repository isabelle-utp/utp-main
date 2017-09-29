theory Modelica_Blocks_Discrete
  imports Modelica_Core
begin
  
definition Sample :: "real \<Rightarrow> real \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> ('d,'c::t2_space) hyrel" where
"Sample samplePeriod startTime u y = 
  [ true | (\<^bold>\<forall> t\<in>{0..<\<^bold>l}\<^sub>u \<bullet> ((y~(\<guillemotleft>t\<guillemotright>) =\<^sub>u 0) \<triangleleft> \<guillemotleft>t\<guillemotright> <\<^sub>u \<guillemotleft>startTime\<guillemotright> \<triangleright> (y~(\<guillemotleft>t\<guillemotright>) =\<^sub>u u~(\<guillemotleft>of_int(\<lfloor>t/samplePeriod\<rfloor>) * samplePeriod\<guillemotright>))))]\<^sub>M" 
  
end