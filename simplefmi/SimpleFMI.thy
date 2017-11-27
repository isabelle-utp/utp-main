theory SimpleFMI
  imports 
    "../theories/utp_time_rel"
    "../theories/utp_reactive_hoare"
    "../hybrid/utp_hybrid"    
begin

purge_notation Sublist.parallel (infixl "\<parallel>" 50)
    
record '\<alpha> fmu =
  fmi2Instantiate :: "'\<alpha> trel"
  fmi2DoStep      :: "'\<alpha> trel"

type_synonym '\<alpha> ma = "'\<alpha> trel"
  
definition fmu_single ("FMU[_, _]") where
[upred_defs]: "fmu_single a fmu = 
  \<lparr> fmi2Instantiate = rel_aext (fmi2Instantiate fmu) (map_st\<^sub>L a)
  , fmi2DoStep = rel_aext (fmi2Instantiate fmu) (map_st\<^sub>L a) \<rparr>"

definition fmu_comp :: "'\<alpha> trel \<Rightarrow> '\<alpha> trel \<Rightarrow> '\<alpha> trel" (infixr "\<parallel>" 85) where
[upred_defs]: "fmu_comp P Q = (P \<and> Q)"
  
definition FMI :: "('\<alpha> \<Rightarrow> '\<alpha>) \<Rightarrow> '\<alpha> fmu list \<Rightarrow> '\<alpha> trel \<Rightarrow> ('\<alpha> \<Rightarrow> '\<alpha>) \<Rightarrow> '\<alpha> trel" where
[upred_defs]: "FMI Init FMUs MA Wiring = 
                 (foldr fmu_comp (map fmi2Instantiate FMUs) true) ;;  
                 \<langle>Init\<rangle>\<^sub>r ;; 
                 (((foldr fmu_comp (map fmi2DoStep FMUs) true) \<parallel> MA) ;; \<langle>Wiring\<rangle>\<^sub>r)\<^sup>\<star>"

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
    
(*
lemma fmu_hoare_rp [hoare_safe]:
  "\<lbrakk> x \<natural> p; \<lbrace>p\<restriction>\<^sub>px\<rbrace>Q\<lbrace>p\<restriction>\<^sub>px\<rbrace>\<^sub>r \<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>FMU[x, Q]\<lbrace>p\<rbrace>\<^sub>r"
  apply (rel_simp, auto simp add: des_vars.defs rp_vars.defs)
  apply (rename_tac ok wait tr st ok' wait' tr' st')
  apply (drule_tac x="ok" in spec)
  apply (drule_tac x="wait" in spec)
  apply (drule_tac x="tr" in spec)
  apply (drule_tac x="get\<^bsub>x\<^esub> st" in spec)
  apply (drule_tac x="ok'" in spec)
  apply (drule_tac x="wait'" in spec)
  apply (drule_tac x="tr'" in spec)
  apply (drule_tac x="get\<^bsub>x\<^esub> st'" in spec)
  apply (auto)
done

lemma fmi_hoare_rp:
  assumes "\<lbrace>true\<rbrace>\<langle>Init\<rangle>\<^sub>r ;; \<langle>Wiring\<rangle>\<^sub>r\<lbrace>p\<rbrace>\<^sub>r" "\<And> fmu. fmu \<in> set(FMUs) \<Longrightarrow> \<lbrace>p\<rbrace>\<langle>Wiring\<rangle>\<^sub>r ;; fmu\<lbrace>p\<rbrace>\<^sub>r"
  shows "\<lbrace>true\<rbrace>FMI Init FMUs MA Wiring\<lbrace>p\<rbrace>\<^sub>r"
oops
*)  
    
definition Modelica_FMU :: "(unit, '\<alpha>::t2_space) hyrel \<Rightarrow> '\<alpha> fmu" where
[upred_defs]: "Modelica_FMU P = \<lparr> fmi2Instantiate = II\<^sub>r, fmi2DoStep = H2T(P) \<rparr>"
    
end