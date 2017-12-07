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
  \<lparr> fmiInstantiate = a:[fmiInstantiate fmu]\<^sup>+
  , fmiDoStep      = a:[fmiDoStep fmu]\<^sub>r\<^sup>+ \<rparr>"

definition fmu_comp :: "'\<alpha> trel \<Rightarrow> '\<alpha> trel \<Rightarrow> '\<alpha> trel" (infixr "\<parallel>" 85) where
[upred_defs]: "fmu_comp P Q = (P \<and> Q)"
  
definition TimeConstraint :: "(real pos) set \<Rightarrow> (real pos, 'a) hrel_rp" where
[upred_defs]: "TimeConstraint T = R1(&tt \<in>\<^sub>u \<guillemotleft>T\<guillemotright>)"

lemma TimeConstraint_RR [closure]: "TimeConstraint(T) is RR"
  by (rel_auto)

abbreviation Instantiate_FMUs :: "'\<alpha> fmu list \<Rightarrow> '\<alpha> trel" 
where "Instantiate_FMUs FMUs \<equiv> [foldr (op ;;) (map fmiInstantiate FMUs) II]\<^sub>S"
  
text {* We make the assumption that the FMUs operate on separate state spaces and thus the order
  of execution is irrelevant. *}
    
definition Step :: "real pos \<Rightarrow> '\<alpha> fmu \<Rightarrow> '\<alpha> trel" where
[upred_defs]: "Step t FMU = ((fmiDoStep FMU \<and> $time\<acute> >\<^sub>u $time)\<lbrakk>\<guillemotleft>t\<guillemotright>/&tt\<rbrakk> \<and> $time\<acute> =\<^sub>u $time)"

lemma Step_RR_lemma: 
  assumes "P is RR"
  shows "((P \<and> $time\<acute> >\<^sub>u $time)\<lbrakk>\<guillemotleft>t\<guillemotright>/&tt\<rbrakk> \<and> $time\<acute> =\<^sub>u $time) is RR"
proof -
  have "((RR P \<and> $time\<acute> >\<^sub>u $time)\<lbrakk>\<guillemotleft>t\<guillemotright>/&tt\<rbrakk> \<and> $time\<acute> =\<^sub>u $time) is RR"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma Step_RR [closure]: "fmiDoStep FMU is RR \<Longrightarrow> Step t FMU is RR"
  by (simp add: Step_def Step_RR_lemma)

lemma Step_fmu_single [simp]: "Step t (FMU[a, P]) = a:[Step t P]\<^sub>r\<^sup>+"
  by (simp add: Step_def fmu_single_def, rel_auto)
    
definition Step_FMUs :: "'\<alpha> fmu list \<Rightarrow> master_algorithm \<Rightarrow> '\<alpha> trel"
  where "Step_FMUs FMUs MA = (\<Sqinter> t\<in>MA \<bullet> (;; f : FMUs \<bullet> Step t f) ;; wait\<^sub>r(\<guillemotleft>t\<guillemotright>))"

lemma Step_FMUs_RR_closed [closure]:
  assumes "MA \<noteq> {}" "FMUs \<noteq> []" "\<And> f. f\<in>set(map fmiDoStep FMUs) \<Longrightarrow> f is RR"
  shows "Step_FMUs FMUs MA is RR"
  by (simp add: Step_FMUs_def closure assms)
    
definition FMI :: "('\<alpha> \<Rightarrow> '\<alpha>) \<Rightarrow> '\<alpha> fmu list \<Rightarrow> master_algorithm \<Rightarrow> ('\<alpha> \<Rightarrow> '\<alpha>) \<Rightarrow> '\<alpha> trel" where
[upred_defs]: "FMI Init FMUs MA Wiring = 
                 Instantiate_FMUs FMUs ;;  
                 \<langle>Init\<rangle>\<^sub>r ;; 
                 (\<langle>Wiring\<rangle>\<^sub>r ;; Step_FMUs FMUs MA)\<^sup>\<star>\<^sup>r"

lemma FMI_hoare_rp [hoare_safe]:
  assumes 
    "\<lbrace>true\<rbrace> Instantiate_FMUs FMUs ;; \<langle>Init\<rangle>\<^sub>r \<lbrace>I\<rbrace>\<^sub>r"
    "\<lbrace>I\<rbrace> \<langle>Wiring\<rangle>\<^sub>r ;; Step_FMUs FMUs MA \<lbrace>I\<rbrace>\<^sub>r"
  shows "\<lbrace>true\<rbrace>FMI Init FMUs MA Wiring\<lbrace>I\<rbrace>\<^sub>r"
proof -
  have 1:"FMI Init FMUs MA Wiring = 
          (Instantiate_FMUs FMUs ;; \<langle>Init\<rangle>\<^sub>r) ;;
          (\<langle>Wiring\<rangle>\<^sub>r ;; Step_FMUs FMUs MA)\<^sup>\<star>\<^sup>r"
    by (simp add: FMI_def, simp add: seqr_assoc)
  show ?thesis
    by (simp add: 1 hoare_safe assms)
qed

definition ArbStep :: "master_algorithm" where
[upred_defs]: "ArbStep = UNIV"

definition FixedStep :: "real pos \<Rightarrow> master_algorithm" where
[upred_defs]: "FixedStep t = {t}"

named_theorems step_simps
  
method fmi_hoare_split uses defs =
  (rule FMI_hoare_rp, 
   simp_all add:step_simps Step_FMUs_def FixedStep_def HyStep_cond HyStep_hEvolves' closure continuous_intros defs,
   simp_all add: frame alpha usubst unrest rpred closure);
   ((uexpr_simp simps:pos_transfer rpred));
   (simp add: rpred closure unrest usubst cond_st_distr)?
  
method fmi_hoare uses defs =
  fmi_hoare_split defs: defs ; hoare_auto
  
    
lemma fmi_instantiatiate_FMU [simp]:
  "fmiInstantiate(FMU[a, P]) = a:[fmiInstantiate P]\<^sup>+"
  by (simp add: fmu_single_def)
        
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
    
lemma fmiInstantiate_Modelica_FMU [simp]: "fmiInstantiate (Modelica_FMU hr) = II"
  by (simp add: Modelica_FMU_def)
    
lemma fmiDoStep_Modelica_FMU [simp]: "fmiDoStep (Modelica_FMU hr) = H2T(hr)"
  by (simp add: Modelica_FMU_def)

lemma Step_Modelica_lemma:
  "t > 0 \<Longrightarrow> (((\<Sqinter> t \<bullet> wait\<^sub>r \<guillemotleft>t\<guillemotright> ;; [P]\<^sub>S) \<and> $time <\<^sub>u $time\<acute>)\<lbrakk>\<guillemotleft>t\<guillemotright>/&tt\<rbrakk> \<and> $time\<acute> =\<^sub>u $time) = [P]\<^sub>S"
  by (rel_auto)
    
lemma Step_Modelica_FMU [step_simps]: 
  "Step t (Modelica_FMU P) = (false \<triangleleft> \<guillemotleft>t = 0\<guillemotright> \<triangleright>\<^sub>R [HyStep[t](P)]\<^sub>S)"
  apply (cases "t > 0")
  apply (simp add: Step_def hyrel2trel_alt_def)
  apply (rel_auto)
  apply (subgoal_tac "t = 0")
  apply (simp, unliteralise, simp add: Step_def rpred, rel_auto)
  using neq_zero_impl_greater apply blast
done
    
end