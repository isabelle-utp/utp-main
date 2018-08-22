theory SimpleTank
  imports 
    VDMRT
    SimpleFMI
    "UTP-Hybrid.utp_hybrid"
    "UTP-Reactive.utp_rea_hoare"
begin recall_syntax
  
alphabet tank_st =
  valve   :: bool
  level   :: real

alphabet ctr_st = vrt_st +
  valveOn     :: bool
  levelSensor :: real
    
alphabet wt_st =
  tank  :: tank_st
  ctr   :: "ctr_st vrt_st_scheme"
    
definition
  "Init = [ &tank:valve      \<mapsto>\<^sub>s true
          , &tank:level      \<mapsto>\<^sub>s 0
          , &ctr:valveOn     \<mapsto>\<^sub>s true
          , &ctr:levelSensor \<mapsto>\<^sub>s 0 ]"
  
definition 
  "Wiring = [ &tank:valve      \<mapsto>\<^sub>s &ctr:valveOn
            , &ctr:levelSensor \<mapsto>\<^sub>s &tank:level ]"
  
lemma tank_st_ords [usubst]: "level \<prec>\<^sub>v valve"
  by (simp add: var_name_ord_def)
  
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
  
lemma ctr_st_ords [usubst]: 
  "ctdown \<prec>\<^sub>v levelSensor"
  "ctdown \<prec>\<^sub>v valveOn"
  "levelSensor \<prec>\<^sub>v valveOn"
  by (simp_all add: var_name_ord_def)  

lemma wt_st_ords [usubst]: "ctr \<prec>\<^sub>v tank" 
  by (simp add: var_name_ord_def)

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
  VDMRT_FMU 0.001 (valveOn := false \<triangleleft> &levelSensor \<le>\<^sub>u \<guillemotleft>minLevel + 0.1\<guillemotright> \<triangleright>\<^sub>r 
                   valveOn := true \<triangleleft> &levelSensor \<ge>\<^sub>u \<guillemotleft>maxLevel - 0.1\<guillemotright> \<triangleright>\<^sub>r II)"

definition WaterTank :: "real \<Rightarrow> real \<Rightarrow> wt_st trel" where
  "WaterTank minLevel maxLevel = 
     FMI Init [FMU[ctr, Ctr minLevel maxLevel], FMU[tank, Tank]] (FixedStep 0.001) Wiring"

lemma ArbStep_not_empty [simp]: "\<not> ArbStep = {}"
  by (simp add: ArbStep_def)
    
(*
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
*)
  
lemma tank_ode_1_evolve:
  "\<langle>{&level} : tank_ode_1(ti)\<rangle>\<^sub>h = {[&level \<mapsto>\<^sub>s \<guillemotleft>(+)\<guillemotright>(&level)\<^sub>a(\<guillemotleft>ti\<guillemotright>)\<^sub>a]}\<^sub>h"
  by (ode_fsolve tank_sol_1)

lemma tank_ode_2_evolve:
  "\<langle>{&level} : tank_ode_2(ti)\<rangle>\<^sub>h = {[&level \<mapsto>\<^sub>s \<guillemotleft>(-)\<guillemotright>(&level)\<^sub>a(\<guillemotleft>ti\<guillemotright>)\<^sub>a]}\<^sub>h"
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

(* The difference between the sensed value of the water level and the actual level is less than 0.1 *)
    
    
(*
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
*)
   
abbreviation WTI :: "wt_st upred" where
  "WTI \<equiv> &ctr:ctdown =\<^sub>u 0.001 \<and>
         ((&tank:level <\<^sub>u 9.9) \<or> 
          (&tank:level \<ge>\<^sub>u 9.9 \<and> &tank:level <\<^sub>u 9.95 \<and> \<not> &ctr:valveOn) \<or>
          (&tank:level \<ge>\<^sub>u 9.9 \<and> &tank:level <\<^sub>u 10 \<and> &ctr:valveOn))"
               
lemma wt_lemma_1:
  "\<lbrace>true\<rbrace> WaterTank 0 10 \<lbrace>WTI\<rbrace>\<^sub>r"  
  unfolding WaterTank_def
  by (fmi_hoare defs: Tank_def Ctr_def Init_def Wiring_def tank_ode_1_evolve tank_ode_2_evolve)

lemma wt_safe:
  "\<lbrace>true\<rbrace> WaterTank 0 10 \<lbrace>&tank:level <\<^sub>u 10\<rbrace>\<^sub>r"  
  by (rule hoare_rp_strengthen[where q'="WTI"])
     (rel_auto, rule wt_lemma_1)  
  
end