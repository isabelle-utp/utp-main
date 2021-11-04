section \<open> Derived SI-Units\<close>

theory SI_Derived
  imports SI_Prefix
begin                                  

subsection \<open> Definitions \<close>

abbreviation "newton \<equiv> kilogram \<^bold>\<cdot> metre \<^bold>\<cdot> second\<^sup>-\<^sup>\<two>"

type_synonym 'a newton = "'a[M \<cdot> L \<cdot> T\<^sup>-\<^sup>2, SI]"

abbreviation "pascal \<equiv> kilogram \<^bold>\<cdot> metre\<^sup>-\<^sup>\<one> \<^bold>\<cdot> second\<^sup>-\<^sup>\<two>"

type_synonym 'a pascal = "'a[M \<cdot> L\<^sup>-\<^sup>1 \<cdot> T\<^sup>-\<^sup>2, SI]"

abbreviation "volt \<equiv> kilogram \<^bold>\<cdot> metre\<^sup>\<two> \<^bold>\<cdot> second\<^sup>-\<^sup>\<three> \<^bold>\<cdot> ampere\<^sup>-\<^sup>\<one>"

type_synonym 'a volt = "'a[M \<cdot> L\<^sup>2 \<cdot> T\<^sup>-\<^sup>3 \<cdot> I\<^sup>-\<^sup>1, SI]"

abbreviation "farad \<equiv> kilogram\<^sup>-\<^sup>\<one> \<^bold>\<cdot> metre\<^sup>-\<^sup>\<two> \<^bold>\<cdot> second\<^sup>\<four> \<^bold>\<cdot> ampere\<^sup>\<two>"

type_synonym 'a farad = "'a[M\<^sup>-\<^sup>1 \<cdot> L\<^sup>-\<^sup>2 \<cdot> T\<^sup>4 \<cdot> I\<^sup>2, SI]"

abbreviation "ohm \<equiv> kilogram \<^bold>\<cdot> metre\<^sup>\<two> \<^bold>\<cdot> second\<^sup>-\<^sup>\<three> \<^bold>\<cdot> ampere\<^sup>-\<^sup>\<two>"

type_synonym 'a ohm = "'a[M \<cdot> L\<^sup>2 \<cdot> T\<^sup>-\<^sup>3 \<cdot> I\<^sup>-\<^sup>2, SI]"

abbreviation "siemens \<equiv> kilogram\<^sup>-\<^sup>\<one> \<^bold>\<cdot> metre\<^sup>-\<^sup>\<two> \<^bold>\<cdot> second\<^sup>\<three> \<^bold>\<cdot> ampere\<^sup>\<two>"

abbreviation "weber \<equiv> kilogram \<^bold>\<cdot> metre\<^sup>\<two> \<^bold>\<cdot> second\<^sup>-\<^sup>\<two> \<^bold>\<cdot> ampere\<^sup>-\<^sup>\<one>"

abbreviation "tesla \<equiv> kilogram \<^bold>\<cdot> second\<^sup>-\<^sup>\<two> \<^bold>\<cdot> ampere\<^sup>-\<^sup>\<one>"

abbreviation "henry \<equiv> kilogram \<^bold>\<cdot> metre\<^sup>\<two> \<^bold>\<cdot> second\<^sup>-\<^sup>\<two> \<^bold>\<cdot> ampere\<^sup>-\<^sup>\<two>"

abbreviation "lux \<equiv> candela \<^bold>\<cdot> steradian \<^bold>\<cdot> metre\<^sup>-\<^sup>\<two>"

abbreviation (input) "becquerel \<equiv> second\<^sup>-\<^sup>\<one>"

abbreviation "gray \<equiv> metre\<^sup>\<two> \<^bold>\<cdot> second\<^sup>-\<^sup>\<two>"

abbreviation "sievert \<equiv> metre\<^sup>\<two> \<^bold>\<cdot> second\<^sup>-\<^sup>\<two>"

abbreviation "katal \<equiv> mole \<^bold>\<cdot> second\<^sup>-\<^sup>\<one>"

definition degrees_celcius :: "'a::field_char_0 \<Rightarrow> 'a[\<Theta>]" ("_\<degree>C" [999] 999) 
  where [si_eq]: "degrees_celcius x = (x *\<^sub>Q kelvin) + approx_ice_point"

definition [si_eq]: "gram = milli *\<^sub>Q kilogram"

subsection \<open> Equivalences \<close>

lemma joule_alt_def: "joule \<cong>\<^sub>Q newton \<^bold>\<cdot> metre" 
  by si_calc

lemma watt_alt_def: "watt \<cong>\<^sub>Q joule \<^bold>/ second"
  by si_calc

lemma volt_alt_def: "volt = watt \<^bold>/ ampere"
  by simp
  
lemma farad_alt_def: "farad \<cong>\<^sub>Q coulomb \<^bold>/ volt"
  by si_calc

lemma ohm_alt_def: "ohm \<cong>\<^sub>Q volt \<^bold>/ ampere"
  by si_calc

lemma siemens_alt_def: "siemens \<cong>\<^sub>Q ampere \<^bold>/ volt"
  by si_calc

lemma weber_alt_def: "weber \<cong>\<^sub>Q volt \<^bold>\<cdot> second"
  by si_calc

lemma tesla_alt_def: "tesla \<cong>\<^sub>Q weber \<^bold>/ metre\<^sup>\<two>"
  by si_calc

lemma henry_alt_def: "henry \<cong>\<^sub>Q weber \<^bold>/ ampere"
  by si_calc

lemma lux_alt_def: "lux = lumen \<^bold>/ metre\<^sup>\<two>"
  by simp

lemma gray_alt_def: "gray \<cong>\<^sub>Q joule \<^bold>/ kilogram"
  by si_calc

lemma sievert_alt_def: "sievert \<cong>\<^sub>Q joule \<^bold>/ kilogram"
  by si_calc

subsection \<open> Properties \<close>

lemma kilogram: "kilo *\<^sub>Q gram = kilogram"
  by (si_simp)

lemma celcius_to_kelvin: "T\<degree>C = (T *\<^sub>Q kelvin) + (273.15 *\<^sub>Q kelvin)"
  by (si_simp)

end