chapter \<open> International System of Units \<close>

section \<open> SI Units Semantics \<close>

theory SI_Units
  imports ISQ
begin

text \<open> An SI unit is simply a particular kind of quantity with an SI tag. \<close>

typedef SI = "UNIV :: unit set" by simp

instance SI :: unit_system
  by (rule unit_system_intro[of "Abs_SI ()"], metis (full_types) Abs_SI_cases UNIV_eq_I insert_iff old.unit.exhaust)

abbreviation "SI \<equiv> unit :: SI"

type_synonym ('n, 'd) SIUnitT = "('n, 'd, SI) QuantT" ("_[_]" [999,0] 999)

text \<open> We now define the seven base units. Effectively, these definitions axiomatise given names
  for the \<^term>\<open>1\<close> elements of the base quantities. \<close>

abbreviation "metre    \<equiv> BUNIT(L, SI)"
abbreviation "kilogram \<equiv> BUNIT(M, SI)"
abbreviation "ampere   \<equiv> BUNIT(I, SI)"
abbreviation "kelvin   \<equiv> BUNIT(\<Theta>, SI)"
abbreviation "mole     \<equiv> BUNIT(N, SI)"
abbreviation "candela  \<equiv> BUNIT(J, SI)"

text \<open> The second is commonly used in unit systems other than SI. Consequently, we define it 
  polymorphically, and require that the system type instantiate a type class to use it. \<close>

class time_second = unit_system

instance SI :: time_second ..
              
abbreviation "second  \<equiv> BUNIT(T, 'a::time_second)"

text \<open>Note that as a consequence of our construction, the term \<^term>\<open>metre\<close> is a SI Unit constant of 
SI-type \<^typ>\<open>'a[L, SI]\<close>, so a unit of dimension \<^typ>\<open>Length\<close> with the magnitude of type \<^typ>\<open>'a\<close>.
A magnitude instantiation can be, e.g., an integer, a rational number, a real number, or a vector of 
type \<^typ>\<open>real\<^sup>3\<close>. Note than when considering vectors, dimensions refer to the \<^emph>\<open>norm\<close> of the vector,
not to its components. \<close>

lemma BaseUnits: 
  "is_base_unit metre" "is_base_unit second" "is_base_unit kilogram" "is_base_unit ampere"
  "is_base_unit kelvin" "is_base_unit mole" "is_base_unit candela"
  by (simp_all add: mk_base_unit)

text \<open> The effect of the above encoding is that we can use the SI base units as synonyms for their
  corresponding dimensions at the type level. \<close>

type_synonym 'a metre    = "'a[Length, SI]"
type_synonym 'a second   = "'a[Time, SI]"
type_synonym 'a kilogram = "'a[Mass, SI]"
type_synonym 'a ampere   = "'a[Current, SI]"
type_synonym 'a kelvin   = "'a[Temperature, SI]"
type_synonym 'a mole     = "'a[Amount, SI]"
type_synonym 'a candela  = "'a[Intensity, SI]"

text \<open> We can therefore construct a quantity such as \<^term>\<open>5 :: rat metre\<close>, which unambiguously 
  identifies that the unit of $5$ is metres using the type system. This works because each base
  unit it the one element. \<close>

subsection \<open> Example Unit Equations \<close>

lemma "(metre \<^bold>\<cdot> second\<^sup>-\<^sup>\<one>) \<^bold>\<cdot> second \<cong>\<^sub>Q metre"
  by (si_calc)

subsection \<open> Metrification \<close>

class metrifiable = unit_system +
  fixes convschema :: "'a itself \<Rightarrow> ('a, SI) Conversion" ("schema\<^sub>C")

instantiation SI :: metrifiable
begin
lift_definition convschema_SI :: "SI itself \<Rightarrow> (SI, SI) Conversion"
is "\<lambda> s. 
  \<lparr> cLengthF = 1
  , cMassF = 1
  , cTimeF = 1
  , cCurrentF = 1
  , cTemperatureF = 1
  , cAmountF = 1
  , cIntensityF = 1 \<rparr>" by simp
instance ..
end

abbreviation metrify :: "('a::field_char_0)['d::dim_type, 's::metrifiable] \<Rightarrow> 'a['d::dim_type, SI]" where
"metrify \<equiv> qconv (convschema (TYPE('s)))"

text \<open> Conversion via SI units \<close>

abbreviation qmconv :: 
  "'s\<^sub>1 itself \<Rightarrow> 's\<^sub>2 itself
   \<Rightarrow> ('a::field_char_0)['d::dim_type, 's\<^sub>1::metrifiable] 
   \<Rightarrow> 'a['d::dim_type, 's\<^sub>2::metrifiable]" where
"qmconv s\<^sub>1 s\<^sub>2 x \<equiv> qconv (inv\<^sub>C (schema\<^sub>C s\<^sub>2) \<circ>\<^sub>C schema\<^sub>C s\<^sub>1) x"

syntax
  "_qmconv" :: "type \<Rightarrow> type \<Rightarrow> logic" ("QMC'(_ \<rightarrow> _')")

translations
  "QMC('s\<^sub>1 \<rightarrow> 's\<^sub>2)" == "CONST qmconv TYPE('s\<^sub>1) TYPE('s\<^sub>2)"

lemma qmconv_self: "QMC('s::metrifiable \<rightarrow> 's) = id"
  by (simp add: fun_eq_iff)

end