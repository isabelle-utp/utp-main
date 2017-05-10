section {* Hybrid systems examples *}

theory utp_hybrid_ex
  imports utp_differential
begin

alphabet bball =
  pos :: real
  vel :: real

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

abbreviation "grav \<equiv> -9.81"

definition
  "bouncing_ball =
     (\<mu> X \<bullet> \<^bold>c:vel, \<^bold>c:pos := 0, 2.0 ;;
            (\<langle>pos;vel \<bullet> \<guillemotleft>(\<lambda> t (v, p). (grav, v))\<guillemotright>\<rangle>\<^sub>H
              [&pos \<le>\<^sub>u 0]\<^sub>H
             (\<^bold>c:vel := (- 0.8 * &\<^bold>c:vel) ;; X)))"

definition
  "thermostat =
    (\<mu> X \<bullet> \<^bold>c:temp, \<^bold>d:isOn := 20, false ;;
           (\<langle>temp \<bullet> \<guillemotleft>(\<lambda> _ t. 5 - 0.1 * t)\<guillemotright>\<rangle>\<^sub>H \<triangleleft> &\<^bold>d:isOn \<triangleright>\<^sub>r \<langle>temp \<bullet> \<guillemotleft>(\<lambda> _ t. - 0.1 * t)\<guillemotright>\<rangle>\<^sub>H)
            [&temp <\<^sub>u 19 \<or> &temp >\<^sub>u 21]\<^sub>H
           (\<^bold>d:isOn := true \<triangleleft> &\<^bold>c:temp <\<^sub>u 19 \<triangleright>\<^sub>r \<^bold>d:isOn := false))"
end