theory VDMRT
  imports SimpleFMI
begin
  
alphabet vrt_st =
  ctdown :: "real pos"

notation vrt_st_child_lens ("\<Sigma>\<^sub>v")

type_synonym '\<alpha> vrel = "('\<alpha> vrt_st_ext) trel"
  
translations
  (type) "'\<alpha> vrel" <= (type) "('\<alpha> vrt_st_ext) trel"

text {* A periodic thread takes a positive real $n$ denoting the period and a relation P acting on 
  the VDM-RT state-space. It checks if the internal variable \emph{ctdown} is 0, and if so executes
  the body of the relation and afterwards sets the countdown to period $n$. If countdown is non-zero
  then it picks an amount of time strictly greater than 0 and less than or equal to the current
  countdown amount and decrements this. It also updates the global clock to reflect this. The
  behaviour is then iterated. *}

(*
definition PeriodicBody :: "real pos \<Rightarrow> '\<alpha> vrt_st_scheme hrel \<Rightarrow> '\<alpha> vrel" where
[upred_defs]:
  "PeriodicBody n P = 
    ([P]\<^sub>S ;; ctdown :=\<^sub>r \<guillemotleft>n\<guillemotright>) 
      \<triangleleft> &ctdown =\<^sub>u 0 \<triangleright>\<^sub>R 
    (\<Sqinter> t | 0 <\<^sub>u \<guillemotleft>t\<guillemotright> \<and> \<guillemotleft>t\<guillemotright> \<le>\<^sub>u $st:ctdown \<bullet> ctdown :=\<^sub>r (&ctdown - \<guillemotleft>t\<guillemotright>) ;; wait\<^sub>r(\<guillemotleft>t\<guillemotright>))"
*)
  
definition PeriodicBody :: "real pos \<Rightarrow> '\<alpha> vrt_st_scheme hrel \<Rightarrow> '\<alpha> vrel" where
[upred_defs]:
  "PeriodicBody n P = 
    (wait\<^sub>r(&ctdown) ;; [P]\<^sub>S ;; ctdown :=\<^sub>r \<guillemotleft>n\<guillemotright>) 
     \<sqinter>
    (\<Sqinter> t | 0 <\<^sub>u \<guillemotleft>t\<guillemotright> \<and> \<guillemotleft>t\<guillemotright> <\<^sub>u $st:ctdown \<bullet> ctdown :=\<^sub>r (&ctdown - \<guillemotleft>t\<guillemotright>) ;; wait\<^sub>r(\<guillemotleft>t\<guillemotright>))"

definition Periodic :: "real pos \<Rightarrow> '\<alpha> vrt_st_scheme hrel \<Rightarrow> '\<alpha> vrel" where
[upred_defs]: 
  "Periodic n P = (PeriodicBody n P)\<^sup>\<star>\<^sup>r"
  
lemma PeriodicBody_RR_closed [closure]:
  "PeriodicBody n P is RR"
  by (rel_auto)
  
lemma Periodic_RR_closed [closure]:
  "Periodic n P is RR"
  by (simp add: Periodic_def closure)
      
definition VDMRT_FMU :: "real pos \<Rightarrow> '\<alpha> vrt_st_scheme hrel \<Rightarrow> '\<alpha> vrt_st_scheme fmu" where
[upred_defs]:
"VDMRT_FMU n P = \<lparr> fmiInstantiate = (ctdown := \<guillemotleft>n\<guillemotright>)
                 , fmiDoStep = PeriodicBody n P \<rparr>"
  
lemma fmiInstantiate_VDMRT_FMU [simp]:
  "fmiInstantiate (VDMRT_FMU n P) = ctdown := \<guillemotleft>n\<guillemotright>"
  by (simp add: VDMRT_FMU_def)

lemma fmiDoStep_VDMRT_FMU [simp]:
  "fmiDoStep (VDMRT_FMU n P) = PeriodicBody n P"
  by (simp add: VDMRT_FMU_def)
   
text {* If a larger time step than the current countdown time is requested, or the time step is 0
  then the behaviour is miraculuous (it isn't possible). Otherwise, if the countdown timer is equal
  to the step then the thread body is executed and then the timer is reset. Otherwise the 
  timer is decremented. *}
    
lemma Step_VDMRT [step_simps]:
      "Step t (VDMRT_FMU n P) = 
       false \<triangleleft> &ctdown <\<^sub>u \<guillemotleft>t\<guillemotright> \<or> \<guillemotleft>t\<guillemotright> =\<^sub>u 0 \<triangleright>\<^sub>R
       (([P]\<^sub>S ;; ctdown :=\<^sub>r \<guillemotleft>n\<guillemotright>) \<triangleleft> &ctdown =\<^sub>u \<guillemotleft>t\<guillemotright> \<triangleright>\<^sub>R (ctdown :=\<^sub>r (&ctdown - \<guillemotleft>t\<guillemotright>)))"
  by (rel_auto, simp_all add: neq_zero_impl_greater)

end