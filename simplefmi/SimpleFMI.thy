theory SimpleFMI
  imports 
    "../theories/utp_time_rel"
    "../theories/utp_reactive_hoare"
    "../hybrid/utp_hybrid"    
begin
  
purge_notation Sublist.parallel (infixl "\<parallel>" 50)
    
record '\<alpha> fmu =
  fmiInstantiate :: "'\<alpha> hrel"
  fmiDoStep      :: "'\<alpha> trel"

text {* A Master Algorithm is a set of possible time steps the FMI network can make at a given
  instant. *}
  
type_synonym master_algorithm = "real pos set"
  
definition fmu_single ("FMU[_, _]") where
[upred_defs]: "fmu_single a fmu = 
  \<lparr> fmiInstantiate = (fmiInstantiate fmu) \<oplus>\<^sub>f a
  , fmiDoStep      = a:[rel_aext (fmiDoStep fmu) (map_st\<^sub>L a)]\<^sub>r \<rparr>"

definition fmu_comp :: "'\<alpha> trel \<Rightarrow> '\<alpha> trel \<Rightarrow> '\<alpha> trel" (infixr "\<parallel>" 85) where
[upred_defs]: "fmu_comp P Q = (P \<and> Q)"
  
definition TimeConstraint :: "(real pos) set \<Rightarrow> (real pos, 'a) hrel_rp" where
[upred_defs]: "TimeConstraint T = R1(&tt \<in>\<^sub>u \<guillemotleft>T\<guillemotright>)"

lemma TimeConstraint_RR [closure]: "TimeConstraint(T) is RR"
  by (rel_auto)

abbreviation Instantiate_FMUs :: "'\<alpha> fmu list \<Rightarrow> '\<alpha> trel" 
where "Instantiate_FMUs FMUs \<equiv> [foldr (op ;;) (map fmiInstantiate FMUs) II]\<^sub>S"

lemma st_rel_seq:
  "[P ;; Q]\<^sub>S = [P]\<^sub>S ;; [Q]\<^sub>S"
  by (rel_auto)
  
lemma st_rel_conj:
  "[P \<and> Q]\<^sub>S = ([P]\<^sub>S \<and> [Q]\<^sub>S)"
   by (rel_auto)
  
text {* We make the assumption that the FMUs operate on separate state spaces and thus the order
  of execution is irrelevant. *}
    
definition Step :: "real pos \<Rightarrow> '\<alpha> fmu \<Rightarrow> '\<alpha> trel" where
[upred_defs]: "Step t FMU = ((fmiDoStep FMU)\<lbrakk>\<guillemotleft>t\<guillemotright>/&tt\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr)"
  
lemma Step_RR [closure]: "fmiDoStep FMU is RR \<Longrightarrow> Step t FMU is RR"
  apply (cases FMU)
  
  apply (simp add: Step_def)
  apply (rule RR_intro)
       apply (simp_all add: unrest)
   apply (rule closure) back
   apply (rel_auto)
oops

definition Step_FMUs :: "'\<alpha> fmu list \<Rightarrow> master_algorithm \<Rightarrow> '\<alpha> trel"
  where "Step_FMUs FMUs MA = (\<Sqinter> t\<in>MA \<bullet> foldr (op ;;) (map (Step t) FMUs) II\<^sub>r ;; wait\<^sub>r(\<guillemotleft>t\<guillemotright>))"
    
(*
lemma "\<lbrakk> \<And> f. f\<in>fmiDoStep`set(FMUs) \<Longrightarrow> f is RR \<rbrakk> \<Longrightarrow> Step_FMUs FMUs MA is RR"
  apply (rule RR_intro)
  apply (simp add: Step_FMUs_def)
  apply (rel_auto)
*)  

definition FMI :: "('\<alpha> \<Rightarrow> '\<alpha>) \<Rightarrow> '\<alpha> fmu list \<Rightarrow> master_algorithm \<Rightarrow> ('\<alpha> \<Rightarrow> '\<alpha>) \<Rightarrow> '\<alpha> trel" where
[upred_defs]: "FMI Init FMUs MA Wiring = 
                 Instantiate_FMUs FMUs ;;  
                 \<langle>Init\<rangle>\<^sub>r ;; 
                 (Step_FMUs FMUs MA ;; \<langle>Wiring\<rangle>\<^sub>r)\<^sup>\<star>"

definition ArbStep :: "master_algorithm" where
[upred_defs]: "ArbStep = UNIV"

definition FixedStep :: "real pos \<Rightarrow> master_algorithm" where
[upred_defs]: "FixedStep t = {t}"
  
lemma fmu_comp_true [simp]: 
  "P \<parallel> true = P"
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
[upred_defs]: "Modelica_FMU P = \<lparr> fmiInstantiate = II, fmiDoStep = H2T(P) \<rparr>"
    
end