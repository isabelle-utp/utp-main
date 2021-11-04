section \<open> British Imperial System (1824/1897) \<close>

theory BIS
  imports ISQ SI_Units CGS
begin

text \<open> The values in the British Imperial System (BIS) are derived from the UK Weights and Measures 
  Act 1824. \<close>

subsection \<open> Preliminaries \<close>

typedef BIS = "UNIV :: unit set" ..
instance BIS :: unit_system
  by (rule unit_system_intro[of "Abs_BIS ()"], 
      metis (full_types) Abs_BIS_cases UNIV_eq_I insert_iff old.unit.exhaust)
instance BIS :: time_second ..
abbreviation "BIS \<equiv> unit :: BIS"

subsection \<open> Base Units \<close>

abbreviation "yard     \<equiv> BUNIT(L, BIS)"
abbreviation "pound    \<equiv> BUNIT(M, BIS)"
abbreviation "rankine  \<equiv> BUNIT(\<Theta>, BIS)"

text \<open> We chose Rankine rather than Farenheit as this is more compatible with the SI system and 
  avoids the need for having an offset in conversion functions. \<close>

subsection \<open> Derived Units \<close>

definition [si_eq]: "foot = 1/3 *\<^sub>Q yard"

definition [si_eq]: "inch = 1/12 *\<^sub>Q foot"

definition [si_eq]: "furlong = 220 *\<^sub>Q yard"

definition [si_eq]: "mile = 1760 *\<^sub>Q yard"

definition [si_eq]: "acre = 4840 *\<^sub>Q yard\<^sup>\<three>"

definition [si_eq]: "ounce = 1/12 *\<^sub>Q pound"

definition [si_eq]: "gallon = 277.421 *\<^sub>Q inch\<^sup>\<three>"

definition [si_eq]: "quart = 1/4 *\<^sub>Q gallon"

definition [si_eq]: "pint = 1/8 *\<^sub>Q gallon"

definition [si_eq]: "peck = 2 *\<^sub>Q gallon"

definition [si_eq]: "bushel = 8 *\<^sub>Q gallon"

definition [si_eq]: "minute = 60 *\<^sub>Q second"

definition [si_eq]: "hour = 60 *\<^sub>Q minute"

subsection \<open> Conversion to SI \<close>

instantiation BIS :: metrifiable
begin

lift_definition convschema_BIS :: "BIS itself \<Rightarrow> (BIS, SI) Conversion" is
"\<lambda> x. \<lparr> cLengthF = 0.9143993, cMassF = 0.453592338, cTimeF = 1
      , cCurrentF = 1, cTemperatureF = 5/9, cAmountF = 1, cIntensityF = 1 \<rparr>" by simp

instance ..
end

lemma BIS_SI_simps [simp]: "LengthF (convschema (a::BIS itself)) = 0.9143993" 
                           "MassF (convschema a) = 0.453592338"
                           "TimeF (convschema a) = 1" 
                           "CurrentF (convschema a) = 1" 
                           "TemperatureF (convschema a) = 5/9"
  by (transfer, simp)+

subsection \<open> Conversion Examples \<close>

lemma "metrify (foot :: rat[L, BIS]) = 0.9143993 / 3 *\<^sub>Q metre"
  by (simp add: foot_def)

lemma "metrify ((70::rat) *\<^sub>Q mile \<^bold>/ hour) = (704087461 / 22500000) *\<^sub>Q (metre \<^bold>/ second)"
  by (si_simp)

lemma "QMC(CGS \<rightarrow> BIS) ((1::rat) *\<^sub>Q centimetre) = 100000 / 9143993 *\<^sub>Q yard"
  by simp



end