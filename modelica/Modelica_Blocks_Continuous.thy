section \<open> Modelica.Blocks.Continuous \<close>

theory Modelica_Blocks_Continuous
imports Modelica_Blocks_Math
begin
  
type_synonym Init = nat
  
abbreviation "NoInit        :: Init \<equiv> 1"
abbreviation "SteadyState   :: Init \<equiv> 2"  
abbreviation "InitialState  :: Init \<equiv> 3"  
abbreviation "InitialOutput :: Init \<equiv> 4"
  
definition Integrator where
[urel_defs]: "Integrator k y_start initType u y =
                [ true
                | ((y~ has-deriv 0 at 0 < \<^bold>l) \<triangleleft> \<guillemotleft>initType = SteadyState\<guillemotright> \<triangleright> (y~(0) =\<^sub>u \<guillemotleft>y_start\<guillemotright>))
                  \<and> y~ has-vderiv (\<lambda>\<^sub>u t \<bullet> \<guillemotleft>k\<guillemotright> * u~(\<guillemotleft>t\<guillemotright>)) ]\<^sub>M"

definition Derivative where
[urel_defs]: "Derivative k T x_start y_start initType u x y =
                [ \<guillemotleft>T\<guillemotright> >\<^sub>u 0 
                | ((x~ has-deriv 0 at 0 < \<^bold>l) 
                     \<triangleleft> \<guillemotleft>initType = SteadyState\<guillemotright> \<triangleright> 
                   (x~(0) =\<^sub>u \<guillemotleft>x_start\<guillemotright>)
                     \<triangleleft> \<guillemotleft>initType = InitialState\<guillemotright> \<triangleright>
                   (y~(0) =\<^sub>u \<guillemotleft>y_start\<guillemotright>)) 
                   \<and> x~ has-vderiv (\<lambda>\<^sub>u t \<bullet> (u~(\<guillemotleft>t\<guillemotright>) - x~(\<guillemotleft>t\<guillemotright>)) / \<guillemotleft>T\<guillemotright>)
                   \<and> y~ has-vderiv (\<lambda>\<^sub>u t \<bullet> (\<guillemotleft>k\<guillemotright> / \<guillemotleft>T\<guillemotright> * (u~(\<guillemotleft>t\<guillemotright>) - x~(\<guillemotleft>t\<guillemotright>)))) ]\<^sub>M"

text \<open> The PID controller needs some internal wires which we here define. \<close>

alphabet PID_st =
  pid_P :: real
  pid_I :: real
  pid_D :: real
  pid_y :: real
  pid_x :: real
  
setup_lifting type_definition_PID_st_ext

instantiation PID_st_ext :: (t2_space) t2_space
begin
  lift_definition open_PID_st_ext :: "'a PID_st_scheme set \<Rightarrow> bool" is "open" .

  instance
    apply (intro_classes)
    apply (transfer, simp)
    apply (transfer, auto)
    apply (transfer, auto)
    apply (transfer, meson hausdorff)
  done
end
  
definition PID where
 "PID k Ti Td Nd initType xi_start xd_start y_start u y
    = Gain 1 u pid_P \<parallel>\<^sub>B 
      Integrator (1 / Ti) xi_start initType u pid_I \<parallel>\<^sub>B
      Derivative Td (Td / Nd) xd_start 0 initType u pid_x pid_D \<parallel>\<^sub>B 
      Add3 1 1 1 pid_P pid_I pid_D pid_y \<parallel>\<^sub>B
      Gain k pid_y y"

end