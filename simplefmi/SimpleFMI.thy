theory SimpleFMI
  imports "../theories/utp_time_rel"
begin

purge_notation Sublist.parallel (infixl "\<parallel>" 50)
    
type_synonym '\<alpha> fmu = "'\<alpha> trel"
type_synonym '\<alpha> ma = "'\<alpha> trel"
  
definition fmu_single ("FMU[_, _]") where
[upred_defs]: "fmu_single a P = rel_aext P (map_st\<^sub>L a)"

definition fmu_comp :: "'\<alpha> fmu \<Rightarrow> '\<alpha> fmu \<Rightarrow> '\<alpha> fmu" (infixr "\<parallel>" 85) where
[upred_defs]: "fmu_comp P Q = (P \<and> Q)"
  
definition FMI :: "('\<alpha> \<Rightarrow> '\<alpha>) \<Rightarrow> '\<alpha> fmu list \<Rightarrow> '\<alpha> trel \<Rightarrow> ('\<alpha> \<Rightarrow> '\<alpha>) \<Rightarrow> '\<alpha> trel" where
[upred_defs]: "FMI Init FMUs MA Wiring = \<langle>Init\<rangle>\<^sub>r ;; (((foldr fmu_comp FMUs true) \<and> MA) ;; \<langle>Wiring\<rangle>\<^sub>r)\<^sup>\<star>"

definition ArbStep :: "'\<alpha> ma" where
[upred_defs]: "ArbStep = true"

definition FixedStep :: "real pos \<Rightarrow> '\<alpha> ma" where
[upred_defs]: "FixedStep t = (($time\<acute> - $time) =\<^sub>u \<guillemotleft>t\<guillemotright>)"
  
lemma fmu_comp_true [simp]: 
  "P \<parallel> true = P"
  by (rel_auto)

lemma fmu_comp_ArbStep [simp]: 
  "P \<parallel> ArbStep = P"
  by (rel_auto)
    
end