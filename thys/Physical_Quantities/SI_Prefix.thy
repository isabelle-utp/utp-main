section \<open> SI Prefixes \<close>

theory SI_Prefix
  imports SI_Constants
begin

subsection \<open> Definitions \<close>

text \<open> Prefixes are simply numbers that can be composed with units using the scalar 
  multiplication operator \<^const>\<open>scaleQ\<close>. \<close>

default_sort ring_char_0

definition deca :: "'a" where [si_eq]: "deca = 10^1"

definition hecto :: "'a" where [si_eq]: "hecto = 10^2"

definition kilo :: "'a" where [si_eq]: "kilo = 10^3"

definition mega :: "'a" where [si_eq]: "mega = 10^6"

definition giga :: "'a" where [si_eq]: "giga = 10^9"

definition tera :: "'a" where [si_eq]: "tera = 10^12"

definition peta :: "'a" where [si_eq]: "peta = 10^15"

definition exa :: "'a" where [si_eq]: "exa = 10^18"

definition zetta :: "'a" where [si_eq]: "zetta = 10^21"

definition yotta :: "'a" where [si_eq]: "yotta = 10^24"

default_sort field_char_0

definition deci :: "'a" where [si_eq]: "deci = 1/10^1"

definition centi :: "'a" where [si_eq]: "centi = 1/10^2"

definition milli :: "'a" where [si_eq]: "milli = 1/10^3"

definition micro :: "'a" where [si_eq]: "micro = 1/10^6"

definition nano :: "'a" where [si_eq]: "nano = 1/10^9"

definition pico :: "'a" where [si_eq]: "pico = 1/10^12"

definition femto :: "'a" where [si_eq]: "femto = 1/10^15"

definition atto :: "'a" where [si_eq]: "atto = 1/10^18"

definition zepto :: "'a" where [si_eq]: "zepto = 1/10^21"

definition yocto :: "'a" where [si_eq]: "yocto = 1/10^24"

subsection \<open> Examples \<close>

lemma "2.3 *\<^sub>Q (centi *\<^sub>Q metre)\<^sup>\<three> = 2.3 \<cdot> 1/10^6 *\<^sub>Q metre\<^sup>\<three>"
  by (si_simp)

lemma "1 *\<^sub>Q (centi *\<^sub>Q metre)\<^sup>-\<^sup>\<one> = 100 *\<^sub>Q metre\<^sup>-\<^sup>\<one>"
  by (si_simp)

subsection \<open> Binary Prefixes \<close>

text \<open> Although not in general applicable to physical quantities, we include these prefixes
  for completeness. \<close>

default_sort ring_char_0

definition kibi :: "'a" where [si_eq]: "kibi = 2^10"

definition mebi :: "'a" where [si_eq]: "mebi = 2^20"

definition gibi :: "'a" where [si_eq]: "gibi = 2^30"

definition tebi :: "'a" where [si_eq]: "tebi = 2^40"

definition pebi :: "'a" where [si_eq]: "pebi = 2^50"

definition exbi :: "'a" where [si_eq]: "exbi = 2^60"

definition zebi :: "'a" where [si_eq]: "zebi = 2^70"

definition yobi :: "'a" where [si_eq]: "yobi = 2^80"

default_sort type

end