theory Modelica_Blocks_Continuous
  imports Modelica_Blocks_Core
begin
  
datatype Init = NoInit | SteadyState | InitialState | InitialOutput
  
definition Integrator :: 
  "Init \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real, 'l, 'c) mcon \<Rightarrow> (real, 'l, 'c) mcon \<Rightarrow> ('l, 'c) mblock" where
[upred_defs, mo_defs]: 
  "Integrator initType k y_start u y =
    \<lparr> mieqs = ((\<guillemotleft>initType \<in> {InitialState,InitialOutput}\<guillemotright> \<Rightarrow> &y =\<^sub>u \<guillemotleft>y_start\<guillemotright>) \<and>
               (\<guillemotleft>initType = SteadyState\<guillemotright> \<Rightarrow> \<guillemotleft>k\<guillemotright>*&u =\<^sub>u 0))
    , mdeqs = y has-der (\<guillemotleft>k\<guillemotright>*&u)
    , maeqs = true
    , mqeqs = true
    , mreqs = {}
    , mzcfs = {}
    , mtevs = (\<lambda> t. False)
    \<rparr>"

definition ResetIntegrator :: 
  "real \<Rightarrow> (real, 'l, 'c) mcon \<Rightarrow> (real, 'l, 'c) mcon \<Rightarrow> 
   (real, 'l, 'c) mcon \<Rightarrow> (bool, 'l, 'c) mcon \<Rightarrow> ('l, 'c) mblock" where
[upred_defs, mo_defs]: 
  "ResetIntegrator k u y y_start r =
    \<lparr> mieqs = (&y =\<^sub>u &y_start)
    , mdeqs = y has-der (\<guillemotleft>k\<guillemotright>*&u)
    , maeqs = true
    , mqeqs = true
    , mreqs = {($y\<acute> =\<^sub>u $y_start) \<triangleleft> &r \<triangleright>\<^sub>r ($y\<acute> =\<^sub>u $y)}
    , mzcfs = {}
    , mtevs = (\<lambda> t. False)
    \<rparr>"

  
definition Der ::
  "(real, 'l, 'c) mcon \<Rightarrow> (real, 'l, 'c) mcon \<Rightarrow> ('l, 'c) mblock" where
[upred_defs, mo_defs]:
  "Der u y = 
    \<lparr> mieqs = true
    , mdeqs = u has-der &y
    , maeqs = true
    , mqeqs = true
    , mreqs = {}
    , mzcfs = {}
    , mtevs = (\<lambda>t. False)
    \<rparr>"
  
end