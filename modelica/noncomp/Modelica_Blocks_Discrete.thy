theory Modelica_Blocks_Discrete
  imports Modelica_Blocks_Core
begin
  
definition sample\<^sub>m :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
[upred_defs, mo_defs]: "sample\<^sub>m s p ti = (\<exists> n::nat. ti = s + of_nat n * p)"
  
definition Sampler :: 
  "real \<Rightarrow> real \<Rightarrow> (real, 'l, 'c) mcon \<Rightarrow> (real, 'l, 'c) mcon \<Rightarrow> ('l, 'c) mblock" where
[upred_defs, mo_defs]: 
  "Sampler samplePeriod startTime u y =
    \<lparr> mieqs = &y =\<^sub>u &u
    , mdeqs = true\<^sub>r
    , maeqs = true
    , mqeqs = (\<guillemotleft>sample\<^sub>m startTime samplePeriod\<guillemotright>(&time)\<^sub>a \<Rightarrow> &y =\<^sub>u &u)
    , mreqs = {}
    , mzcfs = {}
    , mtevs = sample\<^sub>m startTime samplePeriod
    \<rparr>"
  
end
