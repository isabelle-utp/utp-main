theory Modelica_Blocks_Discrete
  imports Modelica_Blocks_Core
begin
  
definition sample\<^sub>m :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
[upred_defs, mo_defs]: "sample\<^sub>m s p ti = (\<exists> n::nat. ti = s + of_nat n * p)"
  
definition Sampler :: 
  "real \<Rightarrow> real \<Rightarrow> (real, 'c) mcon \<Rightarrow> (real, 'c) mcon \<Rightarrow> 'c mblock" where
[upred_defs, mo_defs]:
  "Sampler samplePeriod startTime u y =
    \<lparr> minit = &y =\<^sub>u &u
    , mceqs = y \<leftarrow>\<^sub>h $y
    , mgrds = [(TimeEvent (sample\<^sub>m startTime samplePeriod), \<^bold>c:y :=\<^sub>R &\<^bold>c:u)]
    \<rparr>"
  
end
