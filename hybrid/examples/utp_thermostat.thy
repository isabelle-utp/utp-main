section {* Thermostat *}

theory utp_thermostat
  imports "../utp_hybrid"
begin

subsection {* State-space *}
  
alphabet thermo_c =
  temp :: real

alphabet thermo_d =
  isOn :: bool

setup_lifting type_definition_thermo_c_ext

instantiation thermo_c_ext :: (t2_space) t2_space
begin
  lift_definition open_thermo_c_ext :: "'a thermo_c_scheme set \<Rightarrow> bool" is "open" .
  instance by (intro_classes, (transfer, auto simp add: separation_t2)+)
end
  
subsection {* Constants *}
  
abbreviation init_temp :: real where
"init_temp \<equiv> 20"
  
abbreviation max_temp :: real where
"max_temp \<equiv> 21"

abbreviation min_temp :: real where
"min_temp \<equiv> 19"

subsection {* Differential Equations and Solutions *}

abbreviation heating_ode :: "real ODE" where
"heating_ode \<equiv> (\<lambda> t temp. 5 - 0.1 * temp)"

abbreviation cooling_ode :: "real ODE" where
"cooling_ode \<equiv> (\<lambda> t temp. - 0.1 * temp)"

subsection {* System Definition *}
  
definition thermostat :: "(thermo_d, thermo_c) hyrel" where
  "thermostat =
    (\<^bold>c:temp :=\<^sub>r \<guillemotleft>init_temp\<guillemotright> ;; 
     \<^bold>d:isOn :=\<^sub>r false ;;
     (\<nu> X \<bullet> (\<langle>temp \<bullet> heating_ode(ti)\<rangle>\<^sub>h \<triangleleft> &\<^bold>d:isOn \<triangleright>\<^sub>R \<langle>temp \<bullet> cooling_ode(ti)\<rangle>\<^sub>h)
              [$temp\<acute> <\<^sub>u \<guillemotleft>min_temp\<guillemotright> \<or> $temp\<acute> >\<^sub>u \<guillemotleft>max_temp\<guillemotright>]\<^sub>h
            (\<^bold>d:isOn :=\<^sub>r true \<triangleleft> &\<^bold>c:temp <\<^sub>u \<guillemotleft>min_temp\<guillemotright> \<triangleright>\<^sub>R \<^bold>d:isOn :=\<^sub>r false) ;; X))"

end