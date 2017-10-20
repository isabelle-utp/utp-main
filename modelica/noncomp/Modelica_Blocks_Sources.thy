theory Modelica_Blocks_Sources
  imports Modelica_Blocks_Core
begin

definition Clock :: "real \<Rightarrow> real \<Rightarrow> (real, 'l, 'c) mcon \<Rightarrow> ('l, 'c) mblock" where
[upred_defs, mo_defs]:
  "Clock offset startTime y =
    \<lparr> mieqs = true
    , mdeqs = true\<^sub>r
    , maeqs = (&y =\<^sub>u \<guillemotleft>offset\<guillemotright> + (0 \<triangleleft> &time <\<^sub>u \<guillemotleft>startTime\<guillemotright> \<triangleright> &time - \<guillemotleft>startTime\<guillemotright>))
    , mqeqs = true
    , mreqs = {}
    , mzcfs = {}
    , mtevs = (\<lambda>t. False)
    \<rparr>"

definition Constant :: "real \<Rightarrow> (real, 'l, 'c) mcon \<Rightarrow> ('l, 'c) mblock" where
[upred_defs, mo_defs]: 
  "Constant k y =
    \<lparr> mieqs = true
    , mdeqs = true\<^sub>r
    , maeqs = (&y =\<^sub>u \<guillemotleft>k\<guillemotright>)
    , mqeqs = true
    , mreqs = {}
    , mzcfs = {}
    , mtevs = (\<lambda>t. False)
    \<rparr>"
  
definition Step :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real, 'l, 'c) mcon \<Rightarrow> ('l, 'c) mblock" where
[upred_defs, mo_defs]: 
  "Step height offset startTime y =
    \<lparr> mieqs = (&y =\<^sub>u \<guillemotleft>offset\<guillemotright>)
    , mdeqs = true\<^sub>r
    , maeqs = true
    , mqeqs = (&time =\<^sub>u \<guillemotleft>startTime\<guillemotright> \<Rightarrow> &y =\<^sub>u \<guillemotleft>offset + height\<guillemotright>)
    , mreqs = {}
    , mzcfs = {}
    , mtevs = (\<lambda>t. t = startTime)
    \<rparr>"
  
end