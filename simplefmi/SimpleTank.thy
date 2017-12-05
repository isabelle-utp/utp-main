theory SimpleTank
  imports 
    VDMRT
    SimpleFMI
    "../hybrid/utp_hybrid"
    "../theories/utp_reactive_hoare"
begin recall_syntax
  
alphabet tank_st =
  valve   :: bool
  level   :: real
  
setup_lifting type_definition_tank_st_ext
  
text {* Proof that the state-space is a T2 topological space. *}
  
instantiation tank_st_ext :: (t2_space) t2_space
begin
  lift_definition open_tank_st_ext :: "'a tank_st_scheme set \<Rightarrow> bool" is "open" .
  instance by (intro_classes, (transfer, auto simp add: separation_t2)+)
end

lemma continuous_Rep_tank_st_ext [continuous_intros]:
  "continuous_on UNIV Rep_tank_st_ext"
  by (metis continuous_on_open_vimage image_vimage_eq open_Int open_UNIV open_tank_st_ext.rep_eq)
  
alphabet ctr_st = vrt_st +
  valveOn     :: bool
  levelSensor :: real
  
alphabet wt_st =
  tank  :: tank_st
  ctr   :: "ctr_st vrt_st_scheme"
    
definition
  "Init = [ &tank:valve      \<mapsto>\<^sub>s true
          , &tank:level      \<mapsto>\<^sub>s -0.001
          , &ctr:valveOn     \<mapsto>\<^sub>s true
          , &ctr:levelSensor \<mapsto>\<^sub>s 0 ]"
  
definition 
  "Wiring = [ &tank:valve      \<mapsto>\<^sub>s &ctr:valveOn
            , &ctr:levelSensor \<mapsto>\<^sub>s &tank:level ]"

abbreviation (input) tank_ode_1 :: "real \<Rightarrow> real \<Rightarrow> real" where
"tank_ode_1 \<equiv> (\<lambda> t l. 1)"

abbreviation (input) tank_ode_2 :: "real \<Rightarrow> real \<Rightarrow> real" where
"tank_ode_2 \<equiv> (\<lambda> t l. -1)"

abbreviation (input) tank_sol_1 :: "real \<Rightarrow> real \<Rightarrow> real" where
"tank_sol_1 \<equiv> (\<lambda> l\<^sub>0 t. l\<^sub>0 + t)"

abbreviation (input) tank_sol_2 :: "real \<Rightarrow> real \<Rightarrow> real" where
"tank_sol_2 \<equiv> (\<lambda> l\<^sub>0 t. l\<^sub>0 - t)"
  
lemma tank_ode_usol_1:
  "l > 0 \<Longrightarrow> (tank_sol_1 l\<^sub>0 usolves_ode tank_ode_1 from 0) {0..l} UNIV"
  by (linear_ode)

lemma tank_ode_usol_2:
  "l > 0 \<Longrightarrow> (tank_sol_2 l\<^sub>0 usolves_ode tank_ode_2 from 0) {0..l} UNIV"
  by (linear_ode)
    
definition Tank  :: "tank_st fmu" where 
  "Tank = Modelica_FMU (\<langle>&level : \<lambda>lev. -1\<rangle>\<^sub>h \<triangleleft> &valve \<triangleright>\<^sub>h \<langle>&level : \<lambda>lev. 1\<rangle>\<^sub>h)"

definition Ctr :: "real \<Rightarrow> real \<Rightarrow> ctr_st vrt_st_ext fmu" where
"Ctr minLevel maxLevel = 
  VDMRT_FMU 0.001 (valveOn := false \<triangleleft> &levelSensor \<le>\<^sub>u \<guillemotleft>minLevel\<guillemotright> \<triangleright>\<^sub>r 
                   valveOn := true \<triangleleft> &levelSensor \<ge>\<^sub>u \<guillemotleft>maxLevel\<guillemotright> \<triangleright>\<^sub>r II)"

definition 
  "WaterTank minLevel maxLevel = 
     FMI Init [FMU[ctr, Ctr minLevel maxLevel], FMU[tank, Tank]] ArbStep Wiring"
   
term "[x:y \<mapsto>\<^sub>s v]"
    

(*
term "\<sigma>(y ;\<^sub>L x \<mapsto>\<^sub>s v)"
*)  

translations 
  "\<sigma>(x:y \<mapsto>\<^sub>s v)" <= "CONST subst_upd \<sigma> (y ;\<^sub>L x) v"

term "assigns_r (subst_upd id (y ;\<^sub>L x) v)"
  
term "x:y := v" 
                    
declare [[show_types=false]]
    
text {* Use of a 1 second fixed step master algorithm when the VDM-RT model only permits 1ms or less
  yields no possible evolutions, and thus only the initial state can be observed. *}
    
lemma st_subst_rel [usubst]:
  "\<sigma> \<dagger>\<^sub>S [P]\<^sub>S = [\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> P]\<^sub>S"
  by (rel_auto)
      
declare cond_st_distr [rpred del]
    

  
  
term "x := v"
  
term "(subst_upd id (y ;\<^sub>L x) v)"
    
term ctdown
  
lemma "ctr:ctdown :=\<^sub>r 0 ;; ctr:valveOn :=\<^sub>r false = undefined"
  apply (simp add: rpred closure usubst)
  oops
    
lemma ArbStep_not_empty [simp]: "\<not> ArbStep = {}"
  by (simp add: ArbStep_def)

lemma st_subst_comp [usubst]: 
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<circ> \<lceil>\<rho>\<rceil>\<^sub>S\<^sub>\<sigma> = \<lceil>\<sigma> \<circ> \<rho>\<rceil>\<^sub>S\<^sub>\<sigma>"
  by (rel_auto)
    
lemma "FMI Init [FMU[ctr, Ctr 1 10], FMU[tank, Tank]] (FixedStep 1) Wiring = false"
  apply (simp add: FMI_def alpha frame rpred usubst Ctr_def Tank_def FixedStep_def Init_def Step_FMUs_def seqr_assoc)
  apply (subst rea_assigns_comp)
    apply (simp_all add: closure)
  apply (simp add: rpred closure usubst)
  apply (subst rea_uplus_unfold)
      apply (simp add: rpred closure usubst)
   apply (simp add: rea_assigns_comp closure usubst frame unrest Step_VDMRT)
  apply (literalise, simp, unliteralise)
  apply (simp add: frame rpred alpha usubst unrest)
  apply (uexpr_simp simps: pos_transfer, simp add: rpred)
done
  
  
lemma tank_ode_1_evolve:
  "\<langle>{&level} : tank_ode_1(ti)\<rangle>\<^sub>h = {[&level \<mapsto>\<^sub>s \<guillemotleft>op +\<guillemotright>(&level)\<^sub>a(\<guillemotleft>ti\<guillemotright>)\<^sub>a]}\<^sub>h"
  by (ode_fsolve tank_sol_1)

lemma tank_ode_2_evolve:
  "\<langle>{&level} : tank_ode_2(ti)\<rangle>\<^sub>h = {[&level \<mapsto>\<^sub>s \<guillemotleft>op -\<guillemotright>(&level)\<^sub>a(\<guillemotleft>ti\<guillemotright>)\<^sub>a]}\<^sub>h"
  by (ode_fsolve tank_sol_2) 
    
lemma continuous_lens_pr_var [closure]: "continuous_lens x \<Longrightarrow> continuous_lens (pr_var x)"
  by (simp add: pr_var_def)
    
lemma continuous_lens_level [closure]: "continuous_lens level"
  apply (unfold_locales, simp_all add: lens_defs prod.case_eq_if)
  apply (simp add: tank_st.select_defs iso_tuple_fst_def tuple_iso_tuple_def 
      tank_st_ext_Tuple_Iso_def Topological_Spaces.continuous_on_fst continuous_Rep_tank_st_ext)
  sorry
        
lemma Tank_Step:
  "H2T(\<langle>&level : \<lambda>lev. 1\<rangle>\<^sub>h \<triangleleft> &valve \<triangleright>\<^sub>h \<langle>&level : \<lambda>lev. - 1\<rangle>\<^sub>h) = 
       (\<Sqinter> t | 0 <\<^sub>u \<guillemotleft>t\<guillemotright> \<bullet> wait\<^sub>r \<guillemotleft>t\<guillemotright> ;; (level :=\<^sub>r (&level + \<guillemotleft>real_of_pos t\<guillemotright>) \<triangleleft> &valve \<triangleright>\<^sub>R level :=\<^sub>r (&level - \<guillemotleft>real_of_pos t\<guillemotright>)))"
  by (simp add: hyrel2trl_cond hyrel2trel_hEvolves tank_ode_1_evolve tank_ode_2_evolve closure continuous_intros, rel_auto)
    
declare rel_frext_skip [frame]
declare rel_frext_assigns [frame]
  
declare arestr_lit [simp]
declare arestr_false [simp] 
declare arestr_zero [simp] 
declare aext_lit [simp]
  
lemma st_rel_cond [rpred]:
  "[P \<triangleleft> b \<triangleright>\<^sub>r Q]\<^sub>S = [P]\<^sub>S \<triangleleft> b \<triangleright>\<^sub>R [Q]\<^sub>S"
  by (rel_auto)
 
lemma st_subst_assigns_rea [usubst]:
  "\<sigma> \<dagger>\<^sub>S \<langle>\<rho>\<rangle>\<^sub>r = \<langle>\<rho> \<circ> \<sigma>\<rangle>\<^sub>r"
  by (rel_auto)
  
lemma st_rel_false [rpred]: "[false]\<^sub>S = false"
  by (rel_auto)
    
lemma st_rel_skip [rpred]: 
  "[II]\<^sub>S = (II\<^sub>r :: ('s, 't::trace) rdes)"
  by (rel_auto)
  
lemma st_subst_rea_skip [usubst]:
  "\<sigma> \<dagger>\<^sub>S II\<^sub>r = \<langle>\<sigma>\<rangle>\<^sub>r"
  by (rel_auto)

lemma st_subst_rea_wait [usubst]:
  "\<sigma> \<dagger>\<^sub>S wait\<^sub>r n = wait\<^sub>r (\<sigma> \<dagger> n) ;; \<langle>\<sigma>\<rangle>\<^sub>r"
  by (rel_auto)
    
lemma lit_plus_appl [lit_simps]: 
  "\<guillemotleft>op +\<guillemotright>(x)\<^sub>a(y)\<^sub>a = x + y"
  by (pred_auto)

lemma lit_minus_appl [lit_simps]: 
  "\<guillemotleft>op -\<guillemotright>(x)\<^sub>a(y)\<^sub>a = x - y"
  by (pred_auto)
    
lemma [usubst]: "ctr \<prec>\<^sub>v tank" 
  by (simp add: var_name_ord_def)
        
lemma [usubst]: "x \<prec>\<^sub>v y \<Longrightarrow> x:a \<prec>\<^sub>v y:b"
  by (simp add: var_name_ord_def)
    
lemma var_name_ord_comp_inner [usubst]: 
  "a \<prec>\<^sub>v b \<Longrightarrow> x:a \<prec>\<^sub>v x:b"
  by (simp add: var_name_ord_def)

lemma var_name_ord_pr_var_1 
  [usubst]: "x \<prec>\<^sub>v y \<Longrightarrow> &x \<prec>\<^sub>v y"
  by (simp add: var_name_ord_def)

lemma [usubst]: "x \<prec>\<^sub>v y \<Longrightarrow> x \<prec>\<^sub>v &y"
  by (simp add: var_name_ord_def)
    
lemma [usubst]: "level \<prec>\<^sub>v valve"
  by (simp add: var_name_ord_def)

lemma [usubst]: "ctdown \<prec>\<^sub>v levelSensor"
  by (simp add: var_name_ord_def)  

lemma [usubst]: "ctdown \<prec>\<^sub>v valveOn"
  by (simp add: var_name_ord_def)  

lemma [usubst]: "levelSensor \<prec>\<^sub>v valveOn"
  by (simp add: var_name_ord_def)  

(* The difference between the sensed value of the water level and the actual level is less than 0.1 *)
    
lemma wt_prop1:
  "\<lbrace>true\<rbrace>FMI Init [FMU[ctr, Ctr 0 10], FMU[tank, Tank]] (FixedStep 0.001) Wiring \<lbrace>&tank:level - &ctr:levelSensor <\<^sub>u 0.1\<rbrace>\<^sub>r"
proof (rule FMI_hoare_rp, simp_all)
  show "\<lbrace>true\<rbrace> [ctr:[fmiInstantiate (Ctr 0 10)]\<^sup>+ ;; tank:[fmiInstantiate Tank]\<^sup>+]\<^sub>S ;; \<langle>Init\<rangle>\<^sub>r \<lbrace>&tank:level - &ctr:levelSensor <\<^sub>u 0.1\<rbrace>\<^sub>r"
    by (simp add: Ctr_def Step_VDMRT Tank_def Init_def rpred frame alpha usubst closure, rel_auto)
  show "\<lbrace>&tank:level - &ctr:levelSensor <\<^sub>u 0.1\<rbrace> 
          \<langle>Wiring\<rangle>\<^sub>r ;; Step_FMUs [FMU[ctr, Ctr 0 10], FMU[tank, Tank]] (FixedStep (1 / 1000))
        \<lbrace>&tank:level - &ctr:levelSensor <\<^sub>u 0.1\<rbrace>\<^sub>r"
    apply (simp add: Wiring_def rpred frame closure usubst Ctr_def Tank_def Step_FMUs_def Step_VDMRT Step_Modelica_FMU HyStep_cond tank_ode_1_evolve tank_ode_2_evolve)
    apply (simp add: HyStep_hEvolves' closure continuous_intros usubst alpha)
    apply (uexpr_simp simps:pos_transfer)
    apply (rel_auto)
    apply (simp_all add: pos_transfer)
  done
qed

method fmi_hoare uses defs =
  (rule FMI_hoare_rp, 
   simp_all add:Step_VDMRT Step_Modelica_FMU Step_FMUs_def FixedStep_def HyStep_cond HyStep_hEvolves' closure continuous_intros defs,
   (simp_all add: frame alpha usubst unrest rpred closure),
   ((uexpr_simp simps:pos_transfer)[1])?,
   ((uexpr_simp simps:pos_transfer)[2])?)
 
term cond
 
definition subst_cond :: "'\<alpha> usubst \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> usubst \<Rightarrow> '\<alpha> usubst" ("(3_ \<triangleleft> _ \<triangleright>\<^sub>s/ _)" [52,0,53] 52) where
[upred_defs]: "subst_cond \<sigma> b \<rho> = (\<lambda> s. if \<lbrakk>b\<rbrakk>\<^sub>e s then \<sigma>(s) else \<rho>(s))"
 
lemma st_cond_assigns [rpred]:
  "\<langle>\<sigma>\<rangle>\<^sub>r \<triangleleft> b \<triangleright>\<^sub>R \<langle>\<rho>\<rangle>\<^sub>r = \<langle>\<sigma> \<triangleleft> b \<triangleright>\<^sub>s \<rho>\<rangle>\<^sub>r"
  by (rel_auto)
  
lemma usubst_cond_upd_1 [usubst]:
  "\<sigma>(x \<mapsto>\<^sub>s u) \<triangleleft> b \<triangleright>\<^sub>s \<rho>(x \<mapsto>\<^sub>s v) = (\<sigma> \<triangleleft> b \<triangleright>\<^sub>s \<rho>)(x \<mapsto>\<^sub>s u \<triangleleft> b \<triangleright> v)"
  by (rel_auto)

lemma usubst_cond_upd_2 [usubst]:
  "\<lbrakk> vwb_lens x; x \<sharp> \<rho> \<rbrakk> \<Longrightarrow> \<sigma>(x \<mapsto>\<^sub>s u) \<triangleleft> b \<triangleright>\<^sub>s \<rho> = (\<sigma> \<triangleleft> b \<triangleright>\<^sub>s \<rho>)(x \<mapsto>\<^sub>s u \<triangleleft> b \<triangleright> &x)"
  by (rel_simp, metis lens_override_def lens_override_idem var_ueval)

lemma usubst_cond_upd_3 [usubst]:
  "\<lbrakk> vwb_lens x; x \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> \<sigma> \<triangleleft> b \<triangleright>\<^sub>s \<rho>(x \<mapsto>\<^sub>s v) = (\<sigma> \<triangleleft> b \<triangleright>\<^sub>s \<rho>)(x \<mapsto>\<^sub>s &x \<triangleleft> b \<triangleright> v)"
  by (rel_simp, metis lens_override_def lens_override_idem var_ueval)
    
lemma usubst_cond_id [usubst]:
  "id \<triangleleft> b \<triangleright>\<^sub>s id = id"
  by (rel_auto)
    
lemma cond_true_false [simp]: 
  "true \<triangleleft> b \<triangleright> false = b"
  by (rel_auto)
  
declare cond_idem [simp]
  
term abs

lemma hoare_rp_prune_1 [hoare_safe]:
  "\<lbrace>p\<rbrace>Q\<lbrace>r\<rbrace>\<^sub>r \<Longrightarrow> \<lbrace>p\<rbrace>false \<triangleleft> b \<triangleright>\<^sub>R Q\<lbrace>r\<rbrace>\<^sub>r"
  by (rel_auto)
    
lemma hoare_rp_wait [hoare_safe]:
  "\<lbrace>p\<rbrace>wait\<^sub>r n\<lbrace>p\<rbrace>\<^sub>r"
  by (rel_auto)
  
lemma wt_prop2:
  "\<lbrace>true\<rbrace>
     FMI Init [FMU[ctr, Ctr 0 10], FMU[tank, Tank]] (FixedStep 0.001) Wiring 
   \<lbrace>(&tank:level - &ctr:levelSensor =\<^sub>u -0.001) \<triangleleft> &tank:valve \<triangleright> (&tank:level - &ctr:levelSensor =\<^sub>u 0.001)\<rbrace>\<^sub>r"  
  apply (fmi_hoare defs: Tank_def Ctr_def Init_def Wiring_def tank_ode_1_evolve tank_ode_2_evolve)
   apply (hoare_auto)
  apply (uexpr_simp simps:pos_transfer)
  apply (simp add: rpred closure usubst unrest cond_st_distr)
  apply (hoare_auto)
done    
 
lemma wt_prop3:
  "\<lbrace>true\<rbrace>
     FMI Init [FMU[ctr, Ctr 0 10], FMU[tank, Tank]] (FixedStep 0.001) Wiring 
   \<lbrace>(\<not> &tank:valve \<and> &ctr:valveOn) =\<^sub>u (&ctr:levelSensor <\<^sub>u 10 \<and> &tank:level \<ge>\<^sub>u 10) \<and> 
    (&tank:level - &ctr:levelSensor =\<^sub>u -0.001) \<triangleleft> &tank:valve \<triangleright> (&tank:level - &ctr:levelSensor =\<^sub>u 0.001)\<rbrace>\<^sub>r"  
  apply (fmi_hoare defs: Tank_def Ctr_def Init_def Wiring_def tank_ode_1_evolve tank_ode_2_evolve)
   apply (hoare_auto)
  apply (uexpr_simp simps:pos_transfer)
  apply (simp add: rpred closure usubst unrest cond_st_distr)
  apply (hoare_auto)
  apply (pred_simp)
 
  

    
proof (rule FMI_hoare_rp, simp_all)
  show "\<lbrace>true\<rbrace> [ctr:[fmiInstantiate (Ctr 0 10)]\<^sup>+ ;; tank:[fmiInstantiate Tank]\<^sup>+]\<^sub>S ;; \<langle>Init\<rangle>\<^sub>r \<lbrace>&tank:level - &ctr:levelSensor <\<^sub>u 0.1\<rbrace>\<^sub>r"
    by (simp add: Ctr_def Step_VDMRT Tank_def Init_def rpred frame alpha usubst closure, rel_auto)
  show "\<lbrace>&tank:level - &ctr:levelSensor <\<^sub>u 0.1\<rbrace> 
          \<langle>Wiring\<rangle>\<^sub>r ;; Step_FMUs [FMU[ctr, Ctr 0 10], FMU[tank, Tank]] (FixedStep (1 / 1000))
        \<lbrace>&tank:level - &ctr:levelSensor <\<^sub>u 0.1\<rbrace>\<^sub>r"
    apply (simp add: Wiring_def rpred frame closure usubst Ctr_def Tank_def Step_FMUs_def Step_VDMRT Step_Modelica_FMU HyStep_cond tank_ode_1_evolve tank_ode_2_evolve)
    apply (simp add: HyStep_hEvolves' closure continuous_intros usubst alpha)
    apply (uexpr_simp simps:pos_transfer)
    apply (rel_auto)
    apply (simp_all add: pos_transfer)
  done
qed

  
lemma wt_prop2:
  "\<lbrace>true\<rbrace>FMI Init [FMU[ctr, Ctr 0 10], FMU[tank, Tank]] (FixedStep 0.001) Wiring \<lbrace>&tank:level - &ctr:levelSensor <\<^sub>u 0.1\<rbrace>\<^sub>r"
  
  show "\<lbrace>true\<rbrace> 
           [ctr:[fmiInstantiate (Ctr 0 10)]\<^sup>+ ;; tank:[fmiInstantiate Tank]\<^sup>+]\<^sub>S ;;
           \<langle>Init\<rangle>\<^sub>r ;; Step_FMUs [FMU[ctr, Ctr 0 10], FMU[tank, Tank]] {1 / 1000} ;; \<langle>Wiring\<rangle>\<^sub>r
        \<lbrace>\<not> &ctr:valveOn \<Rightarrow> &tank:level \<le>\<^sub>u 11\<rbrace>\<^sub>r"
     apply (simp add: Ctr_def Step_VDMRT Tank_def Tank_Step Step_FMUs_def)
     apply (simp add: Step_Modelica_FMU Step_VDMRT HyStep_cond tank_ode_1_evolve tank_ode_2_evolve)
     apply (simp_all add: HyStep_hEvolves' closure continuous_intros)
     apply (simp add: frame alpha usubst)
     apply (simp add: Init_def)
     apply (simp add: rpred frame Init_def Wiring_def usubst unrest closure alpha)
     apply (uexpr_simp simps:pos_transfer)
     apply (simp add: alpha usubst frame rpred closure unrest seqr_assoc)
     apply (rel_auto)
  done

    
lemma "\<lbrace>true\<rbrace>FMI Init [FMU[ctr, Ctr 0 10], FMU[tank, Tank]] (FixedStep 0.001) Wiring \<lbrace>&tank:level \<le>\<^sub>u \<guillemotleft>12\<guillemotright>\<rbrace>\<^sub>r"
proof (rule FMI_hoare_rp, simp_all add: FixedStep_def, safe, simp_all)
  show "fmiDoStep FMU[ctr, Ctr 0 10] is RR"
    by (simp add: Ctr_def fmu_single_def closure)
  show "fmiDoStep FMU[tank, Tank] is RR"
    by (simp add: Tank_def fmu_single_def closure)
  show "\<lbrace>true\<rbrace> 
           [ctr:[fmiInstantiate (Ctr 0 10)]\<^sup>+ ;; tank:[fmiInstantiate Tank]\<^sup>+]\<^sub>S ;;
           \<langle>Init\<rangle>\<^sub>r ;; Step_FMUs [FMU[ctr, Ctr 0 10], FMU[tank, Tank]] {1 / 1000} ;; \<langle>Wiring\<rangle>\<^sub>r
        \<lbrace>&tank:level \<le>\<^sub>u \<guillemotleft>12\<guillemotright>\<rbrace>\<^sub>r"
     apply (simp add: Ctr_def Step_VDMRT Tank_def Tank_Step Step_FMUs_def)
     apply (simp add: Step_Modelica_FMU Step_VDMRT HyStep_cond tank_ode_1_evolve tank_ode_2_evolve)
     apply (simp_all add: HyStep_hEvolves' closure continuous_intros)
     apply (unliteralise)
     apply (simp add: frame alpha usubst)
     apply (simp add: Init_def)
     apply (simp add: rpred frame Init_def Wiring_def usubst unrest closure alpha)
     apply (uexpr_simp simps:pos_transfer)
     apply (simp add: alpha usubst frame rpred closure unrest seqr_assoc)
    apply (rel_auto)
  done
  show "\<lbrace>&tank:level \<le>\<^sub>u \<guillemotleft>12\<guillemotright>\<rbrace> 
           Step_FMUs [FMU[ctr, Ctr 0 10], FMU[tank, Tank]] {1 / 1000} ;; 
           \<langle>Wiring\<rangle>\<^sub>r 
        \<lbrace>&tank:level \<le>\<^sub>u \<guillemotleft>12\<guillemotright>\<rbrace>\<^sub>r"
   apply (simp add: Tank_def Tank_Step Step_FMUs_def)
   apply (simp add: Step_Modelica_FMU Step_VDMRT HyStep_cond tank_ode_1_evolve tank_ode_2_evolve)
   apply (simp_all add: HyStep_hEvolves' closure continuous_intros)
   apply (uexpr_simp simps:pos_transfer)
   apply (simp add: rpred frame Init_def Ctr_def Step_FMUs_def Wiring_def Step_VDMRT HyStep_cond usubst unrest closure alpha)
   apply (uexpr_simp simps:pos_transfer)
    apply (rel_auto)
    
  apply (simp add: Ctr_def fmu_single_def closure)
    apply (simp add: Tank_def fmu_single_def closure)
   apply (simp add: Tank_def Tank_Step Step_FMUs_def)
   apply (simp add: Step_Modelica_FMU Step_VDMRT HyStep_cond tank_ode_1_evolve tank_ode_2_evolve)
   apply (simp_all add: HyStep_hEvolves' closure continuous_intros)

  apply (simp add: real_of_pos_1 real_of_pos_less_transfer real_of_pos_numeral real_op_pos_div)
  apply (simp add: Modelica_FMU_def Step_def Tank_Step)
    
    apply (subst usubst)
   apply (subst rpred)
    apply (simp_all add: closure)
    apply (rule closure)
    apply (simp_all add: closure)
    apply (rule closure)
      apply (simp_all add: closure)
        apply (rule closure)
     apply (simp_all add: closure)
    apply (rule closure)
     apply (simp_all add: closure)
    apply (rule closure) back
    apply (rule closure) back
         apply (simp_all add: closure)
    apply (rule closure) back
    apply (simp_all)

    
lemma "\<lbrace>true\<rbrace>WaterTank 0 10 10\<lbrace>&tank:level <\<^sub>u 10 \<and> &ctr:levelSensor <\<^sub>u 10\<rbrace>\<^sub>r"
  apply (simp add: conj_comm conj_assoc)
  apply (simp add: WaterTank_def Ctr_def Tank_def FMI_def)
  apply (rule hoare_safe)
   apply (rule hoare_safe)
   apply (simp add: Init_def)
   apply (rel_auto)
  apply (rule hoare_safe)
  apply (rule hoare_safe)
  apply (rule hoare_safe)
    apply (rule hoare_safe)
     apply (simp add: unrest)
    apply (simp add: Periodic_def PeriodicBody_def)
    apply (rule hoare_safe)
     apply (rule hoare_safe)
     apply (rel_auto)
        apply (rel_auto)
    apply (
     apply (rule unrest)
  apply (simp add: unrest)
(*
  apply (rule hoare)
   apply (rule hoare_safe)
   apply (simp add: Init_def)
   apply (rel_auto)
oops
*)

end