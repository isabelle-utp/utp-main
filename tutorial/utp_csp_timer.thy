section {* FMI Timed (Simplified) *}

theory utp_csp_timer
  imports "../theories/utp_csp"
begin

type_synonym TIME = nat
  
datatype ch_timer = 
  setT TIME |
  updateSS TIME |
  step "TIME \<times> TIME" |
  endc
  
alphabet st_timer =
  currentTime :: TIME
  stepSize    :: TIME
  
type_synonym timer = "(st_timer, ch_timer) action"
  
definition Timer :: "TIME \<Rightarrow> TIME \<Rightarrow> TIME \<Rightarrow> timer" where
"Timer ct hc tN =
  currentTime, stepSize :=\<^sub>C \<guillemotleft>ct\<guillemotright>, \<guillemotleft>hc\<guillemotright> ;;
  (\<mu>\<^sub>C Step \<bullet> (setT?(t:\<guillemotleft>t\<guillemotright> <\<^sub>u \<guillemotleft>tN\<guillemotright>) \<^bold>\<rightarrow> currentTime :=\<^sub>C \<guillemotleft>t\<guillemotright>
           \<box> updateSS?(ss) \<^bold>\<rightarrow> stepSize :=\<^sub>C \<guillemotleft>ss\<guillemotright>
           \<box> step!(&currentTime)!(&stepSize) \<^bold>\<rightarrow>
               currentTime :=\<^sub>C min\<^sub>u(&currentTime + &stepSize, \<guillemotleft>tN\<guillemotright>)
           \<box> (&currentTime =\<^sub>u \<guillemotleft>tN\<guillemotright>) &\<^sub>u endc \<^bold>\<rightarrow> Stop) ;; Step)"

end