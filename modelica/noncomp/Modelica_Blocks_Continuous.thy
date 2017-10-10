theory Modelica_Blocks_Continuous
  imports Modelica_Blocks_Core
begin
  
datatype Init = NoInit | SteadyState | InitialState | InitialOutput
  
definition Integrator :: 
  "Init \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real, 'l, 'c) mcon \<Rightarrow> (real, 'l, 'c) mcon \<Rightarrow> ('l, 'c) mblock" where
[upred_defs, mo_defs]: 
  "Integrator initType k y_start u y =
    \<lparr> minit = ((\<guillemotleft>initType \<in> {InitialState,InitialOutput}\<guillemotright> \<Rightarrow> &y =\<^sub>u \<guillemotleft>y_start\<guillemotright>) \<and>
               (\<guillemotleft>initType = SteadyState\<guillemotright> \<Rightarrow> \<guillemotleft>k\<guillemotright>*&u =\<^sub>u 0))
    , mceqs = y has-der (\<guillemotleft>k\<guillemotright>*&u)
    , mgrds = []
    \<rparr>"
  
definition Der ::
  "(real, 'l, 'c) mcon \<Rightarrow> (real, 'l, 'c) mcon \<Rightarrow> ('l, 'c) mblock" where
[upred_defs, mo_defs]:
  "Der u y = 
    \<lparr> minit = true
    , mceqs = u has-der &y
    , mgrds = []
    \<rparr>"
  
end