theory Modelica_Blocks_Continuous
  imports Modelica_Blocks_Core
begin
  
datatype Init = NoInit | SteadyState | InitialState | InitialOutput
  
definition Integrator :: 
  "Init \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real, 'c) mcon \<Rightarrow> (real, 'c) mcon \<Rightarrow> 'c mblock" where
[upred_defs, mo_defs]: 
  "Integrator initType k y_start y u =
    \<lparr> minit = ((\<guillemotleft>initType \<in> {InitialState,InitialOutput}\<guillemotright> \<Rightarrow> &y =\<^sub>u \<guillemotleft>y_start\<guillemotright>) \<and>
               (\<guillemotleft>initType = SteadyState\<guillemotright> \<Rightarrow> \<guillemotleft>k\<guillemotright>*&u =\<^sub>u 0))
    , mceqs = \<forall>[y has-der (\<guillemotleft>k\<guillemotright>*&u)]\<^sub>H
    , mgrds = []
    \<rparr>"
  
end