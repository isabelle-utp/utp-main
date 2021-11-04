section \<open> Centimetre-Gram-Second System \<close>

theory CGS
  imports SI_Units
begin

subsection \<open> Preliminaries \<close>

typedef CGS = "UNIV :: unit set" ..
instance CGS :: unit_system
  by (rule unit_system_intro[of "Abs_CGS ()"], metis (full_types) 
           Abs_CGS_cases UNIV_eq_I insert_iff old.unit.exhaust)
instance CGS :: time_second ..
abbreviation "CGS \<equiv> unit :: CGS"

subsection \<open> Base Units \<close>

abbreviation "centimetre  \<equiv> BUNIT(L, CGS)"
abbreviation "gram        \<equiv> BUNIT(M, CGS)"

subsection \<open> Conversion to SI \<close>

instantiation CGS :: metrifiable
begin

lift_definition convschema_CGS :: "CGS itself \<Rightarrow> (CGS, SI) Conversion" is
"\<lambda> x. \<lparr> cLengthF = 0.01, cMassF = 0.001, cTimeF = 1
      , cCurrentF = 1, cTemperatureF = 1, cAmountF = 1, cIntensityF = 1 \<rparr>" by simp

instance ..
end

lemma CGS_SI_simps [simp]: "LengthF (convschema (a::CGS itself)) = 0.01" "MassF (convschema a) = 0.001"
  "TimeF (convschema a) = 1" "CurrentF (convschema a) = 1" "TemperatureF (convschema a) = 1"
  by (transfer, simp)+

subsection \<open> Conversion Examples \<close>

lemma "metrify ((100::rat) *\<^sub>Q centimetre) = 1 *\<^sub>Q metre"
  by (si_simp)

end