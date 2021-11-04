section \<open> Non-SI Units Accepted for SI use \<close>

theory SI_Accepted
  imports SI_Derived
begin

definition [si_def, si_eq]: "minute = 60 *\<^sub>Q second"

definition [si_def, si_eq]: "hour = 60 *\<^sub>Q minute"

definition [si_def, si_eq]: "day = 24 *\<^sub>Q hour"

definition [si_def, si_eq]: "astronomical_unit = 149597870700 *\<^sub>Q metre"

definition degree :: "'a::real_field[L/L]" where
[si_def, si_eq]: "degree = (2\<cdot>(of_real pi) / 180) *\<^sub>Q radian"

abbreviation degrees ("_\<degree>" [999] 999) where "n\<degree> \<equiv> n *\<^sub>Q degree"

definition [si_def, si_eq]: "litre = 1/1000 *\<^sub>Q metre\<^sup>\<three>"

definition [si_def, si_eq]: "tonne = 10^3 *\<^sub>Q kilogram"

definition [si_def, si_eq]: "dalton = 1.66053906660 * (1 / 10^27) *\<^sub>Q kilogram"

subsection \<open> Example Unit Equations \<close>

lemma "1 *\<^sub>Q hour = 3600 *\<^sub>Q second"
  by (si_simp)

lemma "watt \<^bold>\<cdot> hour \<cong>\<^sub>Q 3600 *\<^sub>Q joule"   by (si_calc)

lemma "25 *\<^sub>Q metre \<^bold>/ second = 90 *\<^sub>Q (kilo *\<^sub>Q metre) \<^bold>/ hour"
  by (si_calc)

end