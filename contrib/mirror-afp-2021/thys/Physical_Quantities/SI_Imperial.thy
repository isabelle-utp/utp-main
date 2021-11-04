section \<open> Imperial Units via SI Units \<close>

theory SI_Imperial
  imports SI_Accepted
begin

subsection \<open> Units of Length \<close>

default_sort field_char_0

text \<open> The units of length are defined in terms of the international yard, as standardised in 1959. \<close>

definition yard :: "'a[L]" where
[si_eq]: "yard = 0.9144 *\<^sub>Q metre"

definition foot :: "'a[L]" where
[si_eq]: "foot = 1/3 *\<^sub>Q yard"

lemma foot_alt_def: "foot = 0.3048 *\<^sub>Q metre"
  by (si_simp)

definition inch :: "'a[L]" where
[si_eq]: "inch = (1 / 36) *\<^sub>Q yard"

lemma inch_alt_def: "inch = 25.4 *\<^sub>Q milli *\<^sub>Q metre"
  by (si_simp)

definition mile :: "'a[L]" where
[si_eq]: "mile = 1760 *\<^sub>Q yard"

lemma mile_alt_def: "mile = 1609.344 *\<^sub>Q metre"
  by (si_simp)

definition nautical_mile :: "'a[L]" where
[si_eq]: "nautical_mile = 1852 *\<^sub>Q metre"

subsection \<open> Units of Mass \<close>

text \<open> The units of mass are defined in terms of the international yard, as standardised in 1959. \<close>

definition pound :: "'a[M]" where
[si_eq]: "pound = 0.45359237 *\<^sub>Q kilogram"

definition ounce :: "'a[M]" where
[si_eq]: "ounce = 1/16 *\<^sub>Q pound"

definition stone :: "'a[M]" where
[si_eq]: "stone = 14 *\<^sub>Q pound"

subsection \<open> Other Units \<close>

definition knot :: "'a[L \<cdot> T\<^sup>-\<^sup>1]" where
[si_eq]: "knot = 1 *\<^sub>Q (nautical_mile \<^bold>/ hour)"

definition pint :: "'a[Volume]" where
[si_eq]: "pint = 0.56826125 *\<^sub>Q litre"

definition gallon :: "'a[Volume]" where
[si_eq]: "gallon = 8 *\<^sub>Q pint"

definition degrees_farenheit :: "'a \<Rightarrow> 'a[\<Theta>]" ("_\<degree>F" [999] 999)
  where [si_eq]: "degrees_farenheit x = (x + 459.67)\<cdot>5/9 *\<^sub>Q kelvin"

default_sort type

subsection \<open> Unit Equations \<close>
  
lemma miles_to_feet: "mile = 5280 *\<^sub>Q foot"
  by si_simp

lemma mph_to_kmh: "1 *\<^sub>Q (mile \<^bold>/ hour) = 1.609344 *\<^sub>Q ((kilo *\<^sub>Q metre) \<^bold>/ hour)"
  by si_simp

lemma farenheit_to_celcius: "T\<degree>F = ((T - 32) \<cdot> 5/9)\<degree>C"
  by si_simp

end