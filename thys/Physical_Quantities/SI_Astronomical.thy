section \<open> Astronomical Constants \<close>

theory SI_Astronomical
  imports SI "HOL-Decision_Procs.Approximation"
begin

text \<open> We create a number of astronomical constants and prove relationships between some of them.
  For this, we use the approximation method that can compute bounds on transcendental functions. \<close>

definition julian_year :: "'a::field[T]" where
[si_eq]: "julian_year = 365.25 *\<^sub>Q day"

definition light_year :: "'a::field_char_0[L]" where
"light_year = QCOERCE[L] (\<^bold>c \<^bold>\<cdot> julian_year)"

text \<open> We need to apply a coercion in the definition of light year to convert the dimension type
  from \<^typ>\<open>L \<cdot> T\<^sup>-\<^sup>1 \<cdot> T\<close> to \<^typ>\<open>L\<close>. The correctness of this coercion is confirmed by the following
  equivalence theorem. \<close>

lemma light_year: "light_year \<cong>\<^sub>Q \<^bold>c \<^bold>\<cdot> julian_year"
  unfolding light_year_def by (si_calc)

lemma light_year_eq [si_eq]: "\<lbrakk>light_year\<rbrakk>\<^sub>Q = \<lbrakk>\<^bold>c \<^bold>\<cdot> julian_year\<rbrakk>\<^sub>Q"
  using light_year quant_equiv_iff by blast

text \<open> HOL can characterise \<^const>\<open>pi\<close> exactly and so we also give an exact value for the parsec. \<close>

definition parsec :: "real[L]" where
[si_eq]: "parsec = 648000 / pi *\<^sub>Q astronomical_unit"

text \<open> We calculate some conservative bounds on the parsec: it is somewhere between 3.26 and 3.27
  light-years. \<close>

lemma parsec_lb: "3.26 *\<^sub>Q light_year < parsec"
  by (si_simp, approximation 12)

lemma parsec_ub: "parsec < 3.27 *\<^sub>Q light_year"
  by (si_simp, approximation 12)

text\<open> The full beauty of the approach is perhaps revealed here, with the 
      type of a classical three-dimensional gravitation field:\<close>

type_synonym gravitation_field = "real\<^sup>3[L] \<Rightarrow> (real\<^sup>3[L \<cdot> T\<^sup>-\<^sup>2])"

end