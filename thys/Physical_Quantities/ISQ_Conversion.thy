section \<open> Conversion Between Unit Systems \<close>

theory ISQ_Conversion
  imports ISQ_Units
begin
                                          
subsection \<open> Conversion Schemas \<close>

text \<open>  A conversion schema provides factors for each of the base units for converting between
  two systems of units. We currently only support conversion between systems that can meaningfully
  characterise a subset of the seven SI dimensions. \<close>

record ConvSchema =
  cLengthF      :: rat
  cMassF        :: rat
  cTimeF        :: rat
  cCurrentF     :: rat 
  cTemperatureF :: rat
  cAmountF      :: rat
  cIntensityF   :: rat

text \<open> We require that all the factors of greater than zero. \<close>

typedef ('s\<^sub>1::unit_system, 's\<^sub>2::unit_system) Conversion ("(_/ \<Rightarrow>\<^sub>U _)" [1, 0] 0) =
  "{c :: ConvSchema. cLengthF c > 0 \<and> cMassF c > 0 \<and> cTimeF c > 0 \<and> cCurrentF c > 0
         \<and> cTemperatureF c > 0 \<and> cAmountF c > 0 \<and> cIntensityF c > 0}"
  by (rule_tac x="\<lparr> cLengthF = 1, cMassF = 1, cTimeF = 1, cCurrentF = 1
                  , cTemperatureF = 1, cAmountF = 1, cIntensityF = 1 \<rparr>" in exI, simp)

setup_lifting type_definition_Conversion

lift_definition LengthF      :: "('s\<^sub>1::unit_system \<Rightarrow>\<^sub>U 's\<^sub>2::unit_system) \<Rightarrow> rat" is cLengthF .
lift_definition MassF        :: "('s\<^sub>1::unit_system \<Rightarrow>\<^sub>U 's\<^sub>2::unit_system) \<Rightarrow> rat" is cMassF .
lift_definition TimeF        :: "('s\<^sub>1::unit_system \<Rightarrow>\<^sub>U 's\<^sub>2::unit_system) \<Rightarrow> rat" is cTimeF .
lift_definition CurrentF     :: "('s\<^sub>1::unit_system \<Rightarrow>\<^sub>U 's\<^sub>2::unit_system) \<Rightarrow> rat" is cCurrentF .
lift_definition TemperatureF :: "('s\<^sub>1::unit_system \<Rightarrow>\<^sub>U 's\<^sub>2::unit_system) \<Rightarrow> rat" is cTemperatureF .
lift_definition AmountF      :: "('s\<^sub>1::unit_system \<Rightarrow>\<^sub>U 's\<^sub>2::unit_system) \<Rightarrow> rat" is cAmountF .
lift_definition IntensityF   :: "('s\<^sub>1::unit_system \<Rightarrow>\<^sub>U 's\<^sub>2::unit_system) \<Rightarrow> rat" is cIntensityF .

lemma Conversion_props [simp]: "LengthF c > 0" "MassF c > 0" "TimeF c > 0" "CurrentF c > 0"
  "TemperatureF c > 0" "AmountF c > 0" "IntensityF c > 0"
  by (transfer, simp)+

subsection \<open> Conversion Algebra \<close>

lift_definition convid :: "'s::unit_system \<Rightarrow>\<^sub>U 's" ("id\<^sub>C")
is "
  \<lparr> cLengthF = 1
  , cMassF = 1
  , cTimeF = 1
  , cCurrentF = 1
  , cTemperatureF = 1
  , cAmountF = 1
  , cIntensityF = 1 \<rparr>" by simp

lift_definition convcomp :: 
  "('s\<^sub>2 \<Rightarrow>\<^sub>U 's\<^sub>3::unit_system) \<Rightarrow> ('s\<^sub>1::unit_system \<Rightarrow>\<^sub>U 's\<^sub>2::unit_system) \<Rightarrow> ('s\<^sub>1 \<Rightarrow>\<^sub>U 's\<^sub>3)" (infixl "\<circ>\<^sub>C" 55) is
"\<lambda> c\<^sub>1 c\<^sub>2. \<lparr> cLengthF = cLengthF c\<^sub>1 * cLengthF c\<^sub>2, cMassF = cMassF c\<^sub>1 * cMassF c\<^sub>2
         , cTimeF = cTimeF c\<^sub>1 * cTimeF c\<^sub>2, cCurrentF = cCurrentF c\<^sub>1 * cCurrentF c\<^sub>2
         , cTemperatureF = cTemperatureF c\<^sub>1 * cTemperatureF c\<^sub>2
         , cAmountF = cAmountF c\<^sub>1 * cAmountF c\<^sub>2, cIntensityF = cIntensityF c\<^sub>1 * cIntensityF c\<^sub>2 \<rparr>"
  by simp

lift_definition convinv :: "('s\<^sub>1::unit_system \<Rightarrow>\<^sub>U 's\<^sub>2::unit_system) \<Rightarrow> ('s\<^sub>2 \<Rightarrow>\<^sub>U 's\<^sub>1)" ("inv\<^sub>C") is
"\<lambda> c. \<lparr> cLengthF = inverse (cLengthF c), cMassF = inverse (cMassF c), cTimeF = inverse (cTimeF c)
      , cCurrentF = inverse (cCurrentF c), cTemperatureF = inverse (cTemperatureF c)
      , cAmountF = inverse (cAmountF c), cIntensityF = inverse (cIntensityF c) \<rparr>" by simp

lemma convinv_inverse [simp]: "convinv (convinv c) = c"
  by (transfer, simp)

lemma convcomp_inv [simp]: "c \<circ>\<^sub>C inv\<^sub>C c = id\<^sub>C"
  by (transfer, simp)

lemma inv_convcomp [simp]: "inv\<^sub>C c \<circ>\<^sub>C c = id\<^sub>C"
  by (transfer, simp)

lemma Conversion_invs [simp]: "LengthF (inv\<^sub>C x) = inverse (LengthF x)" "MassF (inv\<^sub>C x) = inverse (MassF x)"
  "TimeF (inv\<^sub>C x) = inverse (TimeF x)" "CurrentF (inv\<^sub>C x) = inverse (CurrentF x)"
  "TemperatureF (inv\<^sub>C x) = inverse (TemperatureF x)" "AmountF (inv\<^sub>C x) = inverse (AmountF x)"
  "IntensityF (inv\<^sub>C x) = inverse (IntensityF x)"
  by (transfer, simp)+

lemma Conversion_comps [simp]: "LengthF (c\<^sub>1 \<circ>\<^sub>C c\<^sub>2) = LengthF c\<^sub>1 * LengthF c\<^sub>2"
  "MassF (c\<^sub>1 \<circ>\<^sub>C c\<^sub>2) = MassF c\<^sub>1 * MassF c\<^sub>2"
  "TimeF (c\<^sub>1 \<circ>\<^sub>C c\<^sub>2) = TimeF c\<^sub>1 * TimeF c\<^sub>2"
  "CurrentF (c\<^sub>1 \<circ>\<^sub>C c\<^sub>2) = CurrentF c\<^sub>1 * CurrentF c\<^sub>2"
  "TemperatureF (c\<^sub>1 \<circ>\<^sub>C c\<^sub>2) = TemperatureF c\<^sub>1 * TemperatureF c\<^sub>2"
  "AmountF (c\<^sub>1 \<circ>\<^sub>C c\<^sub>2) = AmountF c\<^sub>1 * AmountF c\<^sub>2"
  "IntensityF (c\<^sub>1 \<circ>\<^sub>C c\<^sub>2) = IntensityF c\<^sub>1 * IntensityF c\<^sub>2"
  by (transfer, simp)+

subsection \<open> Conversion Functions \<close>

definition dconvfactor :: "('s\<^sub>1::unit_system \<Rightarrow>\<^sub>U 's\<^sub>2::unit_system) \<Rightarrow> Dimension \<Rightarrow> rat" where
"dconvfactor c d = 
  LengthF c ^\<^sub>Z dim_nth d Length
  * MassF c ^\<^sub>Z dim_nth d Mass 
  * TimeF c ^\<^sub>Z dim_nth d Time 
  * CurrentF c ^\<^sub>Z dim_nth d Current 
  * TemperatureF c ^\<^sub>Z dim_nth d Temperature
  * AmountF c ^\<^sub>Z dim_nth d Amount
  * IntensityF c ^\<^sub>Z dim_nth d Intensity"

lemma dconvfactor_pos [simp]: "dconvfactor c d > 0"
  by (simp add: dconvfactor_def)

lemma dconvfactor_nz [simp]: "dconvfactor c d \<noteq> 0"
  by (metis dconvfactor_pos less_numeral_extra(3))
  
lemma dconvfactor_convinv: "dconvfactor (convinv c) d = inverse (dconvfactor c d)"
  by (simp add: dconvfactor_def intpow_inverse[THEN sym])

lemma dconvfactor_id [simp]: "dconvfactor id\<^sub>C d = 1"
  by (simp add: dconvfactor_def, transfer, simp)

lemma dconvfactor_compose:
  "dconvfactor (c\<^sub>1 \<circ>\<^sub>C c\<^sub>2) d = dconvfactor c\<^sub>1 d * dconvfactor c\<^sub>2 d"
  by (simp add: dconvfactor_def, transfer, simp add: mult_ac intpow_mult_distrib)

lemma dconvfactor_inverse:
  "dconvfactor c (inverse d) = inverse (dconvfactor c d)"
  by (simp add: dconvfactor_def inverse_dimvec_def intpow_uminus)

lemma dconvfactor_times:
  "dconvfactor c (x \<cdot> y) = dconvfactor c x \<cdot> dconvfactor c y"
  by (auto simp add: dconvfactor_def  mult_ac intpow_mult_combine times_dimvec_def)
                                                                                                                                           
lift_definition qconv :: "('s\<^sub>1, 's\<^sub>2) Conversion \<Rightarrow> ('a::field_char_0)['d::dim_type, 's\<^sub>1::unit_system] \<Rightarrow> 'a['d, 's\<^sub>2::unit_system]"
is "\<lambda> c q. \<lparr> mag = of_rat (dconvfactor c (dim q)) * mag q, dim = dim q, unit_sys = unit \<rparr>" by simp

lemma magQ_qconv: "\<lbrakk>qconv c q\<rbrakk>\<^sub>Q = of_rat (dconvfactor c (dimQ q)) * \<lbrakk>q\<rbrakk>\<^sub>Q"
  by (simp add: si_def, transfer, simp)

lemma qconv_id [simp]: "qconv id\<^sub>C x = x"
  by (transfer', simp add: Measurement_System_eq_intro)

lemma qconv_comp: "qconv (c\<^sub>1 \<circ>\<^sub>C c\<^sub>2) x = qconv c\<^sub>1 (qconv c\<^sub>2 x)"
  by (transfer, simp add: dconvfactor_compose of_rat_mult)

lemma qconv_convinv [simp]: "qconv (convinv c) (qconv c x) = x"
  by (transfer, simp add: dconvfactor_convinv mult.assoc[THEN sym] of_rat_mult[THEN sym] Measurement_System_eq_intro)

lemma qconv_scaleQ [simp]: "qconv c (d *\<^sub>Q x) = d *\<^sub>Q qconv c x"
  by (transfer, simp)

lemma qconv_plus [simp]: "qconv c (x + y) = qconv c x + qconv c y"
  by (transfer, auto simp add: plus_Quantity_ext_def mult.commute ring_class.ring_distribs)

lemma qconv_minus [simp]: "qconv c (x - y) = qconv c x - qconv c y"
  by (transfer, auto simp add: plus_Quantity_ext_def mult.commute ring_class.ring_distribs)

lemma qconv_qmult [simp]: "qconv c (x \<^bold>\<cdot> y) = qconv c x \<^bold>\<cdot> qconv c y"
  by (transfer, simp add: times_Quantity_ext_def times_Measurement_System_ext_def dconvfactor_times of_rat_mult)

lemma qconv_qinverse [simp]: "qconv c (x\<^sup>-\<^sup>\<one>) = (qconv c x)\<^sup>-\<^sup>\<one>"
  by (transfer, simp add: inverse_Quantity_ext_def inverse_Measurement_System_ext_def dconvfactor_inverse of_rat_inverse)

lemma qconv_Length [simp]: "qconv c BUNIT(L, _) = LengthF c *\<^sub>Q BUNIT(L, _)" 
  by (simp add: dconvfactor_def magQ_qconv si_eq mk_BaseDim_def one_dimvec_def)

lemma qconv_Mass [simp]: "qconv c BUNIT(M, _) = MassF c *\<^sub>Q BUNIT(M, _)" 
  by (simp add: dconvfactor_def magQ_qconv si_eq mk_BaseDim_def one_dimvec_def)

lemma qconv_Time [simp]: "qconv c BUNIT(T, _) = TimeF c *\<^sub>Q BUNIT(T, _)" 
  by (simp add: dconvfactor_def magQ_qconv si_eq mk_BaseDim_def one_dimvec_def)

lemma qconv_Current [simp]: "qconv c BUNIT(I, _) = CurrentF c *\<^sub>Q BUNIT(I, _)" 
  by (simp add: dconvfactor_def magQ_qconv si_eq mk_BaseDim_def one_dimvec_def)

lemma qconv_Temperature [simp]: "qconv c BUNIT(\<Theta>, _) = TemperatureF c *\<^sub>Q BUNIT(\<Theta>, _)" 
  by (simp add: dconvfactor_def magQ_qconv si_eq mk_BaseDim_def one_dimvec_def)

lemma qconv_Amount [simp]: "qconv c BUNIT(N, _) = AmountF c *\<^sub>Q BUNIT(N, _)" 
  by (simp add: dconvfactor_def magQ_qconv si_eq mk_BaseDim_def one_dimvec_def)

lemma qconv_Intensity [simp]: "qconv c BUNIT(J, _) = IntensityF c *\<^sub>Q BUNIT(J, _)" 
  by (simp add: dconvfactor_def magQ_qconv si_eq mk_BaseDim_def one_dimvec_def)

end