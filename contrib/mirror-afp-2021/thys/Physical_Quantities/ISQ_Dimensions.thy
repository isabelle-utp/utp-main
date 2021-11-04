chapter \<open> International System of Quantities \<close>

section \<open> Quantity Dimensions \<close>

theory ISQ_Dimensions
  imports Groups_mult Power_int Enum_extra
          HOL.Transcendental
          "HOL-Eisbach.Eisbach"
begin

subsection \<open> Preliminaries \<close>

class unitary = finite +
  assumes unitary_unit_pres: "card (UNIV::'a set) = 1"
begin

definition "unit = (undefined::'a)"

lemma UNIV_unitary: "UNIV = {a::'a}"
proof -
  have "card(UNIV :: 'a set) = 1"
    by (simp add: local.unitary_unit_pres)
  thus ?thesis
    by (metis (full_types) UNIV_I card_1_singletonE empty_iff insert_iff)
qed

lemma eq_unit: "(a::'a) = b"
  by (metis (full_types) UNIV_unitary iso_tuple_UNIV_I singletonD)

end

lemma unitary_intro: "(UNIV::'s set) = {a} \<Longrightarrow> OFCLASS('s, unitary_class)"
  apply (intro_classes, auto)
  using finite.simps apply blast
  using card_1_singleton_iff apply blast
  done

named_theorems si_def and si_eq

instantiation unit :: comm_monoid_add
begin
  definition "zero_unit = ()"
  definition "plus_unit (x::unit) (y::unit) = ()"
  instance proof qed (simp_all)
end

instantiation unit :: comm_monoid_mult
begin
  definition "one_unit = ()"
  definition "times_unit (x::unit) (y::unit) = ()"
  instance proof qed (simp_all)
end

instantiation unit :: inverse
begin
  definition "inverse_unit (x::unit) = ()"
  definition "divide_unit (x::unit) (y::unit) = ()"
  instance ..
end

instance unit :: ab_group_mult
  by (intro_classes, simp_all)

subsection \<open> Dimension Vectors \<close>

text \<open> Quantity dimensions are used to distinguish quantities of different kinds. Only quantities
  of the same kind can be compared and combined: it is a mistake to add a length to a mass, for
  example. Dimensions are often expressed in terms of seven base quantities, which can be combined 
  to form derived quantities. Consequently, a dimension associates with each of the base quantities 
  an integer that denotes the power to which it is raised. We use a special vector type to represent
  dimensions, and then specialise this to the seven major dimensions. \<close>

typedef ('n, 'd) dimvec = "UNIV :: ('d::enum \<Rightarrow> 'n) set"
  morphisms dim_nth dim_lambda ..

declare dim_lambda_inject [simplified, simp]
declare dim_nth_inverse [simp]
declare dim_lambda_inverse [simplified, simp]

instantiation dimvec :: (zero, enum) "one"
begin
definition one_dimvec :: "('a, 'b) dimvec" where "one_dimvec = dim_lambda (\<lambda> i. 0)"
instance ..
end

instantiation dimvec :: (plus, enum) times
begin
definition times_dimvec :: "('a, 'b) dimvec \<Rightarrow> ('a, 'b) dimvec \<Rightarrow> ('a, 'b) dimvec" where
"times_dimvec x y = dim_lambda (\<lambda> i. dim_nth x i + dim_nth y i)"
instance ..
end

instance dimvec :: (comm_monoid_add, enum) comm_monoid_mult
  by ((intro_classes; simp add: times_dimvec_def one_dimvec_def fun_eq_iff add.assoc), simp add: add.commute)
  
text \<open> We also define the inverse and division operations, and an abelian group, which will allow
  us to perform dimensional analysis. \<close>

instantiation dimvec :: ("{plus,uminus}", enum) inverse
begin
definition inverse_dimvec :: "('a, 'b) dimvec \<Rightarrow> ('a, 'b) dimvec" where
"inverse_dimvec x = dim_lambda (\<lambda> i. - dim_nth x i)"

definition divide_dimvec :: "('a, 'b) dimvec \<Rightarrow> ('a, 'b) dimvec \<Rightarrow> ('a, 'b) dimvec" where
[code_unfold]: "divide_dimvec x y = x * (inverse y)"

  instance ..
end

instance dimvec :: (ab_group_add, enum) ab_group_mult
  by (intro_classes, simp_all add: inverse_dimvec_def one_dimvec_def times_dimvec_def divide_dimvec_def)

subsection \<open> Code Generation \<close>

text \<open> Dimension vectors can be represented using lists, which enables code generation and thus
  efficient proof. \<close>

definition mk_dimvec :: "'n list \<Rightarrow> ('n::ring_1, 'd::enum) dimvec" 
  where "mk_dimvec ds = (if (length ds = CARD('d)) then dim_lambda (\<lambda> d. ds ! enum_ind d) else 1)"

code_datatype mk_dimvec

lemma mk_dimvec_inj: "inj_on (mk_dimvec :: 'n list \<Rightarrow> ('n::ring_1, 'd::enum) dimvec) {xs. length xs = CARD('d)}"
proof (rule inj_onI, safe)
  fix x y :: "'n list"
  assume a: "(mk_dimvec x :: ('n, 'd) dimvec) = mk_dimvec y" "length x = CARD('d)" "length y = CARD('d)"
  have "\<And>i. i < length x \<Longrightarrow> x ! i = y ! i"
  proof -
    fix i
    assume "i < length x"
    with a have "enum_ind (ENUM('d) ! i) = i"
      by (simp)
    with a show "x ! i = y ! i"
      by (auto simp add: mk_dimvec_def fun_eq_iff, metis)
  qed

  then show "x = y"
    by (metis a(2) a(3) nth_equalityI)
qed

lemma mk_dimvec_eq_iff [simp]: 
  assumes "length x = CARD('d)" "length y = CARD('d)"
  shows "((mk_dimvec x :: ('n::ring_1, 'd::enum) dimvec) = mk_dimvec y) \<longleftrightarrow> (x = y)"
  by (rule inj_on_eq_iff[OF mk_dimvec_inj], simp_all add: assms)

lemma one_mk_dimvec [code, si_def]: "(1::('n::ring_1, 'a::enum) dimvec) = mk_dimvec (replicate CARD('a) 0)"
  by (auto simp add: mk_dimvec_def one_dimvec_def)

lemma times_mk_dimvec [code, si_def]:
  "(mk_dimvec xs * mk_dimvec ys :: ('n::ring_1, 'a::enum) dimvec) = 
  (if (length xs = CARD('a) \<and> length ys = CARD('a))
    then mk_dimvec (map (\<lambda> (x, y). x + y) (zip xs ys))
    else if length xs = CARD('a) then mk_dimvec xs else mk_dimvec ys)"
  by (auto simp add: times_dimvec_def mk_dimvec_def fun_eq_iff one_dimvec_def)

lemma power_mk_dimvec [si_def]:
  "(power (mk_dimvec xs) n :: ('n::ring_1, 'a::enum) dimvec) = 
    (if (length xs = CARD('a)) then mk_dimvec (map ((*) (of_nat n)) xs) else mk_dimvec xs)"
  by (induct n, simp add: one_dimvec_def mk_dimvec_def)
     (auto simp add: times_mk_dimvec zip_map_map[where f="id", simplified] comp_def split_beta' zip_same_conv_map distrib_right mult.commute)

lemma inverse_mk_dimvec [code, si_def]:
  "(inverse (mk_dimvec xs) :: ('n::ring_1, 'a::enum) dimvec) = 
   (if (length xs = CARD('a)) then mk_dimvec (map uminus xs) else 1)"
  by (auto simp add: inverse_dimvec_def one_dimvec_def mk_dimvec_def fun_eq_iff)  

lemma divide_mk_dimvec [code, si_def]:
  "(mk_dimvec xs / mk_dimvec ys :: ('n::ring_1, 'a::enum) dimvec) = 
  (if (length xs = CARD('a) \<and> length ys = CARD('a))
    then mk_dimvec (map (\<lambda> (x, y). x - y) (zip xs ys))
    else if length ys = CARD('a) then mk_dimvec (map uminus ys) else mk_dimvec xs)"
  by (auto simp add: divide_dimvec_def inverse_mk_dimvec times_mk_dimvec zip_map_map[where f="id", simplified] comp_def split_beta')

text \<open> A base dimension is a dimension where precisely one component has power 1: it is the 
  dimension of a base quantity. Here we define the seven base dimensions. \<close>

definition mk_BaseDim :: "'d::enum \<Rightarrow> (int, 'd) dimvec" where
"mk_BaseDim d = dim_lambda (\<lambda> i. if (i = d) then 1 else 0)"

lemma mk_BaseDim_neq [simp]: "x \<noteq> y \<Longrightarrow> mk_BaseDim x \<noteq> mk_BaseDim y"
  by (auto simp add: mk_BaseDim_def fun_eq_iff)

lemma mk_BaseDim_code [code]: "mk_BaseDim (d::'d::enum) = mk_dimvec (list_update (replicate CARD('d) 0) (enum_ind d) 1)"
  by (auto simp add: mk_BaseDim_def mk_dimvec_def fun_eq_iff)

definition is_BaseDim :: "(int, 'd::enum) dimvec \<Rightarrow> bool" 
  where "is_BaseDim x \<equiv> (\<exists> i. x = dim_lambda ((\<lambda> x. 0)(i := 1)))"

lemma is_BaseDim_mk [simp]: "is_BaseDim (mk_BaseDim x)"
  by (auto simp add: mk_BaseDim_def is_BaseDim_def fun_eq_iff)

subsection \<open> Dimension Semantic Domain \<close>

text \<open> We next specialise dimension vectors to the usual seven place vector. \<close>

datatype sdim = Length | Mass | Time | Current | Temperature | Amount | Intensity

lemma sdim_UNIV: "(UNIV :: sdim set) = {Length, Mass, Time, Current, Temperature, Amount, Intensity}"
  using sdim.exhaust by blast

lemma CARD_sdim [simp]: "CARD(sdim) = 7"
  by (simp add: sdim_UNIV)

instantiation sdim :: enum
begin
  definition "enum_sdim = [Length, Mass, Time, Current, Temperature, Amount, Intensity]"
  definition "enum_all_sdim P \<longleftrightarrow> P Length \<and> P Mass \<and> P Time \<and> P Current \<and> P Temperature \<and> P Amount \<and> P Intensity"
  definition "enum_ex_sdim P \<longleftrightarrow> P Length \<or> P Mass \<or> P Time \<or> P Current \<or> P Temperature \<or> P Amount \<or> P Intensity"
  instance
    by (intro_classes, simp_all add: sdim_UNIV enum_sdim_def enum_all_sdim_def enum_ex_sdim_def)
end

instantiation sdim :: card_UNIV 
begin
  definition "finite_UNIV = Phantom(sdim) True"
  definition "card_UNIV = Phantom(sdim) 7"
  instance by (intro_classes, simp_all add: finite_UNIV_sdim_def card_UNIV_sdim_def)
end

lemma sdim_enum [simp]:
  "enum_ind Length = 0" "enum_ind Mass = 1" "enum_ind Time = 2" "enum_ind Current = 3"
  "enum_ind Temperature = 4" "enum_ind Amount = 5" "enum_ind Intensity = 6"
  by (simp_all add: enum_ind_def enum_sdim_def)

type_synonym Dimension = "(int, sdim) dimvec"

abbreviation LengthBD      ("\<^bold>L") where "\<^bold>L \<equiv> mk_BaseDim Length"
abbreviation MassBD        ("\<^bold>M") where "\<^bold>M \<equiv> mk_BaseDim Mass"
abbreviation TimeBD        ("\<^bold>T") where "\<^bold>T \<equiv> mk_BaseDim Time"
abbreviation CurrentBD     ("\<^bold>I") where "\<^bold>I \<equiv> mk_BaseDim Current"
abbreviation TemperatureBD ("\<^bold>\<Theta>") where "\<^bold>\<Theta> \<equiv> mk_BaseDim Temperature"
abbreviation AmountBD      ("\<^bold>N") where "\<^bold>N \<equiv> mk_BaseDim Amount"
abbreviation IntensityBD   ("\<^bold>J") where "\<^bold>J \<equiv> mk_BaseDim Intensity"

abbreviation "BaseDimensions \<equiv> {\<^bold>L, \<^bold>M, \<^bold>T, \<^bold>I, \<^bold>\<Theta>, \<^bold>N, \<^bold>J}"

lemma BD_mk_dimvec [si_def]: 
  "\<^bold>L = mk_dimvec [1, 0, 0, 0, 0, 0, 0]"
  "\<^bold>M = mk_dimvec [0, 1, 0, 0, 0, 0, 0]"
  "\<^bold>T = mk_dimvec [0, 0, 1, 0, 0, 0, 0]"
  "\<^bold>I = mk_dimvec [0, 0, 0, 1, 0, 0, 0]"
  "\<^bold>\<Theta> = mk_dimvec [0, 0, 0, 0, 1, 0, 0]"
  "\<^bold>N = mk_dimvec [0, 0, 0, 0, 0, 1, 0]"
  "\<^bold>J = mk_dimvec [0, 0, 0, 0, 0, 0, 1]"
  by (simp_all add: mk_BaseDim_code eval_nat_numeral)

text \<open> The following lemma confirms that there are indeed seven unique base dimensions. \<close>

lemma seven_BaseDimensions: "card BaseDimensions = 7"
  by simp

text \<open> We can use the base dimensions and algebra to form dimension expressions. Some examples
  are shown below. \<close>

term "\<^bold>L\<cdot>\<^bold>M\<cdot>\<^bold>T\<^sup>-\<^sup>2"
term "\<^bold>M\<cdot>\<^bold>L\<^sup>-\<^sup>3"

value "\<^bold>L\<cdot>\<^bold>M\<cdot>\<^bold>T\<^sup>-\<^sup>2"

lemma "\<^bold>L\<cdot>\<^bold>M\<cdot>\<^bold>T\<^sup>-\<^sup>2 = mk_dimvec [1, 1, - 2, 0, 0, 0, 0]"
  by (simp add: si_def)

subsection \<open> Dimension Type Expressions \<close>

subsubsection \<open> Classification \<close>

text \<open> We provide a syntax for dimension type expressions, which allows representation of 
  dimensions as types in Isabelle. This will allow us to represent quantities that are parametrised 
  by a particular dimension type. We first must characterise the subclass of types that represent a 
  dimension.

  The mechanism in Isabelle to characterize a certain subclass of Isabelle type expressions
  are \<^emph>\<open>type classes\<close>. The following type class is used to link particular Isabelle types
  to an instance of the type \<^typ>\<open>Dimension\<close>. It requires that any such type has the cardinality
  \<^term>\<open>1\<close>, since a dimension type is used only to mark a quantity.
  \<close>

class dim_type = unitary +
  fixes   dim_ty_sem :: "'a itself \<Rightarrow> Dimension"

syntax
  "_QD" :: "type \<Rightarrow> logic" ("QD'(_')")

translations
  "QD('a)" == "CONST dim_ty_sem TYPE('a)"

text \<open> The notation \<^term>\<open>QD('a::dim_type)\<close> allows to obtain the dimension of a dimension type
  \<^typ>\<open>'a\<close>. 

  The subset of basic dimension types can be characterized by the following type class: \<close>

class basedim_type = dim_type +
  assumes is_BaseDim: "is_BaseDim QD('a)"

subsubsection \<open> Base Dimension Type Expressions \<close>

text \<open> The definition of the basic dimension type constructors is straightforward via a
  one-elementary set, \<^typ>\<open>unit set\<close>. The latter is adequate since we need just an abstract syntax 
  for type expressions, so just one value for the \<^verbatim>\<open>dimension\<close>-type symbols. We define types for
  each of the seven base dimensions, and also for dimensionless quantities. \<close>

typedef Length      = "UNIV :: unit set" .. setup_lifting type_definition_Length
typedef Mass        = "UNIV :: unit set" .. setup_lifting type_definition_Mass
typedef Time        = "UNIV :: unit set" .. setup_lifting type_definition_Time
typedef Current     = "UNIV :: unit set" .. setup_lifting type_definition_Current
typedef Temperature = "UNIV :: unit set" .. setup_lifting type_definition_Temperature
typedef Amount      = "UNIV :: unit set" .. setup_lifting type_definition_Amount
typedef Intensity   = "UNIV :: unit set" .. setup_lifting type_definition_Intensity
typedef NoDimension = "UNIV :: unit set" .. setup_lifting type_definition_NoDimension

type_synonym M = Mass
type_synonym L = Length
type_synonym T = Time
type_synonym I = Current
type_synonym \<Theta> = Temperature
type_synonym N = Amount
type_synonym J = Intensity
type_notation NoDimension ("\<one>")

translations
  (type) "M" <= (type) "Mass"
  (type) "L" <= (type) "Length"
  (type) "T" <= (type) "Time"
  (type) "I" <= (type) "Current"
  (type) "\<Theta>" <= (type) "Temperature"
  (type) "N" <= (type) "Amount"
  (type) "J" <= (type) "Intensity"

text\<open> Next, we embed the base dimensions into the dimension type expressions by instantiating the 
  class \<^class>\<open>basedim_type\<close> with each of the base dimension types. \<close>

instantiation Length :: basedim_type
begin
definition [si_eq]: "dim_ty_sem_Length (_::Length itself) = \<^bold>L"
instance by (intro_classes, auto simp add: dim_ty_sem_Length_def, (transfer, simp)+)
end

instantiation Mass :: basedim_type
begin
definition [si_eq]: "dim_ty_sem_Mass (_::Mass itself) = \<^bold>M"
instance by (intro_classes, auto simp add: dim_ty_sem_Mass_def, (transfer, simp)+)
end

instantiation Time :: basedim_type
begin
definition [si_eq]: "dim_ty_sem_Time (_::Time itself) = \<^bold>T"
instance by (intro_classes, auto simp add: dim_ty_sem_Time_def, (transfer, simp)+)
end

instantiation Current :: basedim_type
begin
definition [si_eq]: "dim_ty_sem_Current (_::Current itself) = \<^bold>I"
instance by (intro_classes, auto simp add: dim_ty_sem_Current_def, (transfer, simp)+)
end

instantiation Temperature :: basedim_type
begin
definition [si_eq]: "dim_ty_sem_Temperature (_::Temperature itself) = \<^bold>\<Theta>"
instance by (intro_classes, auto simp add: dim_ty_sem_Temperature_def, (transfer, simp)+)
end

instantiation Amount :: basedim_type
begin
definition [si_eq]: "dim_ty_sem_Amount (_::Amount itself) = \<^bold>N"
instance by (intro_classes, auto simp add: dim_ty_sem_Amount_def, (transfer, simp)+)
end   

instantiation Intensity :: basedim_type
begin
definition [si_eq]: "dim_ty_sem_Intensity (_::Intensity itself) = \<^bold>J"
instance by (intro_classes, auto simp add: dim_ty_sem_Intensity_def, (transfer, simp)+)
end

instantiation NoDimension :: dim_type
begin
definition [si_eq]: "dim_ty_sem_NoDimension (_::NoDimension itself) = (1::Dimension)"
instance by (intro_classes, auto simp add: dim_ty_sem_NoDimension_def, (transfer, simp)+)
end

lemma base_dimension_types [simp]: 
  "is_BaseDim QD(Length)" "is_BaseDim QD(Mass)" "is_BaseDim QD(Time)" "is_BaseDim QD(Current)" 
  "is_BaseDim QD(Temperature)" "is_BaseDim QD(Amount)" "is_BaseDim QD(Intensity)" 
  by (simp_all add: is_BaseDim)

subsubsection \<open> Dimension Type Constructors: Inner Product and Inverse \<close>

text\<open> Dimension type expressions can be constructed by multiplication and division of the base
  dimension types above. Consequently, we need to define multiplication and inverse operators
  at the type level as well. On the class of dimension types (in which we have already inserted 
  the base dimension types), the definitions of the type constructors for inner product and inverse is 
  straightforward. \<close>

typedef ('a::dim_type, 'b::dim_type) DimTimes (infixl "\<cdot>" 69) = "UNIV :: unit set" ..
setup_lifting type_definition_DimTimes

text \<open> The type \<^typ>\<open>('a,'b) DimTimes\<close> is parameterised by two types, \<^typ>\<open>'a\<close> and \<^typ>\<open>'b\<close> that must
  both be elements of the \<^class>\<open>dim_type\<close> class. As with the base dimensions, it is a unitary type
  as its purpose is to represent dimension type expressions. We instantiate \<^class>\<open>dim_type\<close> with
  this type, where the semantics of a product dimension expression is the product of the underlying
  dimensions. This means that multiplication of two dimension types yields a dimension type. \<close>

instantiation DimTimes :: (dim_type, dim_type) dim_type
begin
  definition dim_ty_sem_DimTimes :: "('a \<cdot> 'b) itself \<Rightarrow> Dimension" where
  [si_eq]: "dim_ty_sem_DimTimes x = QD('a) * QD('b)"
  instance by (intro_classes, simp_all add: dim_ty_sem_DimTimes_def, (transfer, simp)+)
end

text \<open> Similarly, we define inversion of dimension types and prove that dimension types are 
  closed under this. \<close>

typedef 'a DimInv ("(_\<^sup>-\<^sup>1)" [999] 999) = "UNIV :: unit set" ..
setup_lifting type_definition_DimInv
instantiation DimInv :: (dim_type) dim_type
begin
  definition dim_ty_sem_DimInv :: "('a\<^sup>-\<^sup>1) itself \<Rightarrow> Dimension" where
  [si_eq]: "dim_ty_sem_DimInv x = inverse QD('a)"
  instance by (intro_classes, simp_all add: dim_ty_sem_DimInv_def, (transfer, simp)+)
end

subsubsection \<open> Dimension Type Syntax \<close>

text \<open> A division is expressed, as usual, by multiplication with an inverted dimension. \<close>

type_synonym ('a, 'b) DimDiv = "'a \<cdot> ('b\<^sup>-\<^sup>1)" (infixl "'/" 69)

text \<open> A number of further type synonyms allow for more compact notation: \<close>

type_synonym 'a DimSquare = "'a \<cdot> 'a" ("(_)\<^sup>2" [999] 999)
type_synonym 'a DimCube = "'a \<cdot> 'a \<cdot> 'a" ("(_)\<^sup>3" [999] 999)
type_synonym 'a DimQuart = "'a \<cdot> 'a \<cdot> 'a \<cdot> 'a" ("(_)\<^sup>4" [999] 999)
type_synonym 'a DimInvSquare = "('a\<^sup>2)\<^sup>-\<^sup>1" ("(_)\<^sup>-\<^sup>2" [999] 999)
type_synonym 'a DimInvCube = "('a\<^sup>3)\<^sup>-\<^sup>1" ("(_)\<^sup>-\<^sup>3" [999] 999)
type_synonym 'a DimInvQuart = "('a\<^sup>4)\<^sup>-\<^sup>1" ("(_)\<^sup>-\<^sup>4" [999] 999)

translations (type) "'a\<^sup>-\<^sup>2" <= (type) "('a\<^sup>2)\<^sup>-\<^sup>1"
translations (type) "'a\<^sup>-\<^sup>3" <= (type) "('a\<^sup>3)\<^sup>-\<^sup>1"
translations (type) "'a\<^sup>-\<^sup>4" <= (type) "('a\<^sup>4)\<^sup>-\<^sup>1"

print_translation \<open>
  [(@{type_syntax DimTimes}, 
    fn ctx => fn [a, b] => 
      if (a = b) 
          then Const (@{type_syntax DimSquare}, dummyT) $ a
          else case a of
            Const (@{type_syntax DimTimes}, _) $ a1 $ a2 =>
              if (a1 = a2 andalso a2 = b) 
                then Const (@{type_syntax DimCube}, dummyT) $ a1 
                else case a1 of
                  Const (@{type_syntax DimTimes}, _) $ a11 $ a12 =>
                    if (a11 = a12 andalso a12 = a2 andalso a2 = b)
                      then Const (@{type_syntax DimQuart}, dummyT) $ a11
                      else raise Match |
            _ => raise Match)]
\<close>

subsubsection \<open> Derived Dimension Types \<close>

type_synonym Area = "L\<^sup>2"
type_synonym Volume = "L\<^sup>3"
type_synonym Acceleration = "L\<cdot>T\<^sup>-\<^sup>1"
type_synonym Frequency = "T\<^sup>-\<^sup>1"
type_synonym Energy = "L\<^sup>2\<cdot>M\<cdot>T\<^sup>-\<^sup>2"
type_synonym Power = "L\<^sup>2\<cdot>M\<cdot>T\<^sup>-\<^sup>3"
type_synonym Force = "L\<cdot>M\<cdot>T\<^sup>-\<^sup>2"
type_synonym Pressure = "L\<^sup>-\<^sup>1\<cdot>M\<cdot>T\<^sup>-\<^sup>2"
type_synonym Charge = "I\<cdot>T"
type_synonym PotentialDifference = "L\<^sup>2\<cdot>M\<cdot>T\<^sup>-\<^sup>3\<cdot>I\<^sup>-\<^sup>1"
type_synonym Capacitance = "L\<^sup>-\<^sup>2\<cdot>M\<^sup>-\<^sup>1\<cdot>T\<^sup>4\<cdot>I\<^sup>2"

subsection \<open> ML Functions \<close>

text \<open> We define ML functions for converting a dimension to an integer vector, and vice-versa.
  These are useful for normalising dimension types. \<close>

ML \<open> 
signature DIMENSION_TYPE = 
sig
  val dim_to_typ: int list -> typ
  val typ_to_dim: typ -> int list
  val normalise: typ -> typ
end

structure Dimension_Type : DIMENSION_TYPE =
struct
  
  val dims = [@{typ L}, @{typ M}, @{typ T}, @{typ I}, @{typ \<Theta>}, @{typ N}, @{typ J}];

  fun typ_to_dim (Type (@{type_name Length}, [])) = [1, 0, 0, 0, 0, 0, 0] |
      typ_to_dim (Type (@{type_name Mass}, []))   = [0, 1, 0, 0, 0, 0, 0] |
      typ_to_dim (Type (@{type_name Time}, []))   = [0, 0, 1, 0, 0, 0, 0] |
      typ_to_dim (Type (@{type_name Current}, []))   = [0, 0, 0, 1, 0, 0, 0] |
      typ_to_dim (Type (@{type_name Temperature}, []))   = [0, 0, 0, 0, 1, 0, 0] |
      typ_to_dim (Type (@{type_name Amount}, []))   = [0, 0, 0, 0, 0, 1, 0] |
      typ_to_dim (Type (@{type_name Intensity}, []))   = [0, 0, 0, 0, 0, 0, 1] |
      typ_to_dim (Type (@{type_name NoDimension}, []))   = [0, 0, 0, 0, 0, 0, 0] |
      typ_to_dim (Type (@{type_name DimInv}, [x])) = map (fn x => 0 - x) (typ_to_dim x) |
      typ_to_dim (Type (@{type_name DimTimes}, [x, y])) 
         = map (fn (x, y) => x + y) (ListPair.zip (typ_to_dim x, typ_to_dim y)) |
      typ_to_dim _ = raise Match;

  fun DimPow 0 _ = Type (@{type_name NoDimension}, []) |
      DimPow 1 t = t |
      DimPow n t = (if (n > 0) then Type (@{type_name DimTimes}, [DimPow (n - 1) t, t]) 
                               else Type (@{type_name DimInv}, [DimPow (0 - n) t]));

  fun dim_to_typ ds = 
    let val dts = map (fn (n, d) => DimPow n d) (filter (fn (n, _) => n <> 0) (ListPair.zip (ds, dims)))
    in if (dts = []) then @{typ NoDimension} else
          foldl1 (fn (x, y) => Type (@{type_name DimTimes}, [x, y])) dts 
    end;

  val normalise = dim_to_typ o typ_to_dim;

end;

Dimension_Type.typ_to_dim @{typ "L\<^sup>-\<^sup>2\<cdot>M\<^sup>-\<^sup>1\<cdot>T\<^sup>4\<cdot>I\<^sup>2\<cdot>M"};
Dimension_Type.normalise @{typ "L\<^sup>-\<^sup>2\<cdot>M\<^sup>-\<^sup>1\<cdot>T\<^sup>4\<cdot>I\<^sup>2\<cdot>M"};
\<close>

end