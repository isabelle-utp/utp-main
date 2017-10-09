theory Modelica_Blocks_Sources
  imports Modelica_Blocks_Core
begin

definition Clock :: "real \<Rightarrow> real \<Rightarrow> (real, 'c) mcon \<Rightarrow> 'c mblock" where
[upred_defs, mo_defs]:
  "Clock offset startTime y =
    \<lparr> minit = true
    , mceqs = y \<leftarrow>\<^sub>h (\<guillemotleft>offset\<guillemotright> + (0 \<triangleleft> $time\<acute> <\<^sub>u \<guillemotleft>startTime\<guillemotright> \<triangleright> $time\<acute> - \<guillemotleft>startTime\<guillemotright>))
    , mgrds = []
    \<rparr>"
  
definition Constant :: "real \<Rightarrow> (real, 'c) mcon \<Rightarrow> 'c mblock" where
[upred_defs, mo_defs]: 
  "Constant k y =
    \<lparr> minit = true
    , mceqs = y \<leftarrow>\<^sub>h \<guillemotleft>k\<guillemotright>
    , mgrds = []
    \<rparr>"
  
definition Step :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real, 'c) mcon \<Rightarrow> 'c mblock" where
[upred_defs, mo_defs]: 
  "Step height offset startTime y =
    \<lparr> minit = (&y =\<^sub>u \<guillemotleft>offset\<guillemotright>)
    , mceqs = y \<leftarrow>\<^sub>h $y
    , mgrds = [(TimeEvent (\<lambda> ti. ti = startTime), \<^bold>c:y :=\<^sub>R \<guillemotleft>offset + height\<guillemotright>)]
    \<rparr>"

end