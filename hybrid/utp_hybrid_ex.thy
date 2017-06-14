section {* Hybrid systems examples *}

theory utp_hybrid_ex
  imports utp_hybrid
begin

subsection {* Bouncing Ball *}
  
text {* We first setup the state-space and prove this is a topological (T2) space *}
  
alphabet bball =
  height :: real
  velocity :: real

setup_lifting type_definition_bball_ext

instantiation bball_ext :: (t2_space) t2_space
begin
  lift_definition open_bball_ext :: "'a bball_scheme set \<Rightarrow> bool" is "open" .

  instance
    apply (intro_classes)
    apply (transfer, simp)
    apply (transfer, auto)
    apply (transfer, auto)
    apply (transfer, meson hausdorff)
  done
end

text {* Next we define some constants; the ODE (ordinary differential equation) and its solution *}
  
abbreviation grav :: real where
"grav \<equiv> -9.81"

text {* The ODE specifies two continuous variables, for velocity and height respectively. It
  does not depend on time which makes it an autonomous ODE. *}

abbreviation grav_ode :: "(real \<times> real) ODE" where
"grav_ode \<equiv> (\<lambda> t (v, h). (- grav, v))"

text {* We also present the following solution to the ODE, which is a function from initial values
  of the continuous variables to a continuous function that shows how the variables change with time. *}

abbreviation grav_sol :: "real \<times> real \<Rightarrow> real \<Rightarrow> real \<times> real" where
"grav_sol \<equiv> \<lambda> (v\<^sub>0, h\<^sub>0) \<tau>. (v\<^sub>0 - grav * \<tau>, v\<^sub>0 * \<tau> - grav * (\<tau> * \<tau>) / 2 + h\<^sub>0)"
  
lemma grav_ode_sol:
  "(\<langle>{&velocity,&height} \<bullet> \<guillemotleft>grav_ode\<guillemotright>\<rangle>\<^sub>h) = {&velocity,&height} \<leftarrow>\<^sub>h \<guillemotleft>grav_sol\<guillemotright>\<lparr>&velocity,&height\<rparr>\<^sub>u\<lparr>\<guillemotleft>time\<guillemotright>\<rparr>\<^sub>u"
proof -
  have 1:"\<forall>l>0. unique_on_strip 0 {0..l} grav_ode 1"
    by (auto, unfold_locales, auto intro!: continuous_on_Pair continuous_on_const Topological_Spaces.continuous_on_fst continuous_on_snd simp add: lipschitz_def dist_Pair_Pair prod.case_eq_if)
  have 2:"\<forall> v\<^sub>0 h\<^sub>0. \<forall>l>0. ((grav_sol (v\<^sub>0, h\<^sub>0)) solves_ode grav_ode) {0..l} UNIV"
    by (clarify, ode_cert)
  from 1 2 have sol:"\<forall> v\<^sub>0 h\<^sub>0. \<forall>l>0. ((grav_sol (v\<^sub>0, h\<^sub>0)) usolves_ode grav_ode from 0) {0..l} UNIV"
    by (auto, rule_tac uos_impl_uniq_sol[where L=1], simp_all)
  show ?thesis
    apply (subst ode_solution[where \<F>="grav_sol"])
    apply (simp_all add: lens_indep_sym plus_vwb_lens)
    using sol apply (simp)
    apply (rel_auto)
  done
qed
  
definition
  "bouncing_ball =
     (\<mu> X \<bullet> \<^bold>c:velocity, \<^bold>c:height := 0, 2.0 ;;
            (\<langle>{&velocity,&height} \<bullet> \<guillemotleft>grav_ode\<guillemotright>\<rangle>\<^sub>h
              [$height\<acute> \<le>\<^sub>u 0]\<^sub>h
             (\<^bold>c:velocity := (- 0.8 * &\<^bold>c:velocity) ;; X)))"

subsection {* Thermostat *}

alphabet thermostat_c =
  temp :: real

alphabet thermostat_d =
  isOn :: bool

setup_lifting type_definition_thermostat_c_ext

instantiation thermostat_c_ext :: (t2_space) t2_space
begin
  lift_definition open_thermostat_c_ext :: "'a thermostat_c_scheme set \<Rightarrow> bool" is "open" .

  instance
    apply (intro_classes)
    apply (transfer, simp)
    apply (transfer, auto)
    apply (transfer, auto)
    apply (transfer, meson hausdorff)
  done
end
  
definition
  "thermostat =
    (\<mu> X \<bullet> \<^bold>c:temp, \<^bold>d:isOn := 20, false ;;
           (\<langle>temp \<bullet> \<guillemotleft>(\<lambda> _ t. 5 - 0.1 * t)\<guillemotright>\<rangle>\<^sub>h \<triangleleft> &\<^bold>d:isOn \<triangleright>\<^sub>r \<langle>temp \<bullet> \<guillemotleft>(\<lambda> _ t. - 0.1 * t)\<guillemotright>\<rangle>\<^sub>h)
            [$temp\<acute> <\<^sub>u 19 \<or> $temp\<acute> >\<^sub>u 21]\<^sub>h
           (\<^bold>d:isOn := true \<triangleleft> &\<^bold>c:temp <\<^sub>u 19 \<triangleright>\<^sub>r \<^bold>d:isOn := false))"
end