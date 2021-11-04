section \<open> Physical Constants \<close>

theory SI_Constants
  imports SI_Units
begin

subsection \<open> Core Derived Units \<close>

abbreviation (input) "hertz \<equiv> second\<^sup>-\<^sup>\<one>"

abbreviation "radian \<equiv> metre \<^bold>\<cdot> metre\<^sup>-\<^sup>\<one>"

abbreviation "steradian \<equiv> metre\<^sup>\<two> \<^bold>\<cdot> metre\<^sup>-\<^sup>\<two>"

abbreviation "joule \<equiv> kilogram \<^bold>\<cdot> metre\<^sup>\<two> \<^bold>\<cdot>  second\<^sup>-\<^sup>\<two>"

type_synonym 'a joule = "'a[M \<cdot> L\<^sup>2 \<cdot> T\<^sup>-\<^sup>2, SI]"

abbreviation "watt \<equiv> kilogram \<^bold>\<cdot> metre\<^sup>\<two> \<^bold>\<cdot> second\<^sup>-\<^sup>\<three>"

type_synonym 'a watt = "'a[M \<cdot> L\<^sup>2 \<cdot> T\<^sup>-\<^sup>3, SI]"

abbreviation "coulomb \<equiv> ampere \<^bold>\<cdot> second"

type_synonym 'a coulomb = "'a[I \<cdot> T, SI]"

abbreviation "lumen \<equiv> candela \<^bold>\<cdot> steradian"

type_synonym 'a lumen = "'a[J \<cdot> (L\<^sup>2 \<cdot> L\<^sup>-\<^sup>2), SI]"

subsection \<open> Constants \<close>

text \<open> The most general types we support must form a field into which the natural numbers can 
  be injected. \<close>

default_sort field_char_0

text \<open> Hyperfine transition frequency of frequency of Cs \<close>

abbreviation caesium_frequency:: "'a[T\<^sup>-\<^sup>1,SI]" ("\<Delta>v\<^sub>C\<^sub>s") where
  "caesium_frequency \<equiv> 9192631770 *\<^sub>Q hertz"

text \<open> Speed of light in vacuum \<close>

abbreviation speed_of_light :: "'a[L \<cdot> T\<^sup>-\<^sup>1,SI]" ("\<^bold>c") where
  "speed_of_light \<equiv> 299792458 *\<^sub>Q (metre\<^bold>\<cdot>second\<^sup>-\<^sup>\<one>)"

text \<open> Planck constant \<close>

abbreviation Planck :: "'a[M \<cdot> L\<^sup>2 \<cdot> T\<^sup>-\<^sup>2 \<cdot> T,SI]" ("\<^bold>h") where
  "Planck \<equiv> (6.62607015 \<cdot> 1/(10^34)) *\<^sub>Q (joule\<^bold>\<cdot>second)"

text \<open> Elementary charge \<close>

abbreviation elementary_charge :: "'a[I \<cdot> T,SI]" ("\<^bold>e") where
  "elementary_charge \<equiv> (1.602176634 \<cdot> 1/(10^19)) *\<^sub>Q coulomb"

text \<open> The Boltzmann constant \<close>

abbreviation Boltzmann :: "'a[M \<cdot> L\<^sup>2 \<cdot> T\<^sup>-\<^sup>2 \<cdot> \<Theta>\<^sup>-\<^sup>1,SI]" ("\<^bold>k") where
  "Boltzmann \<equiv> (1.380649\<cdot>1/(10^23)) *\<^sub>Q (joule \<^bold>/ kelvin)"

text \<open> The Avogadro number \<close>

abbreviation Avogadro :: "'a[N\<^sup>-\<^sup>1,SI]" ("N\<^sub>A") where
"Avogadro \<equiv> 6.02214076\<cdot>(10^23) *\<^sub>Q (mole\<^sup>-\<^sup>\<one>)"

abbreviation max_luminous_frequency :: "'a[T\<^sup>-\<^sup>1,SI]" where
"max_luminous_frequency \<equiv> (540\<cdot>10^12) *\<^sub>Q hertz"

text \<open> The luminous efficacy of monochromatic radiation of frequency \<^const>\<open>max_luminous_frequency\<close>. \<close>

abbreviation luminous_efficacy :: "'a[J \<cdot> (L\<^sup>2 \<cdot> L\<^sup>-\<^sup>2) \<cdot> (M \<cdot> L\<^sup>2 \<cdot> T\<^sup>-\<^sup>3)\<^sup>-\<^sup>1,SI]" ("K\<^sub>c\<^sub>d") where
"luminous_efficacy \<equiv> 683 *\<^sub>Q (lumen\<^bold>/watt)"

subsection \<open> Checking Foundational Equations of the SI System \<close>

theorem second_definition: 
  "1 *\<^sub>Q second \<cong>\<^sub>Q (9192631770 *\<^sub>Q \<one>) \<^bold>/ \<Delta>v\<^sub>C\<^sub>s"
  by si_calc

theorem metre_definition: 
  "1 *\<^sub>Q metre \<cong>\<^sub>Q (\<^bold>c \<^bold>/ (299792458 *\<^sub>Q \<one>))\<^bold>\<cdot>second"
  "1 *\<^sub>Q metre \<cong>\<^sub>Q (9192631770 / 299792458) *\<^sub>Q (\<^bold>c \<^bold>/ \<Delta>v\<^sub>C\<^sub>s)"
  by si_calc+

theorem kilogram_definition:
  "((1 *\<^sub>Q kilogram)::'a kilogram) \<cong>\<^sub>Q (\<^bold>h \<^bold>/ (6.62607015 \<cdot> 1/(10^34) *\<^sub>Q \<one>))\<^bold>\<cdot>metre\<^sup>-\<^sup>\<two>\<^bold>\<cdot>second" 
  by si_calc


abbreviation "approx_ice_point \<equiv> 273.15 *\<^sub>Q kelvin"

default_sort type

end