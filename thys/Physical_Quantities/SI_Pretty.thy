section \<open> Parsing and Pretty Printing of SI Units \<close>

theory SI_Pretty
  imports SI
begin

subsection \<open> Syntactic SI Units \<close>

text \<open> The following syntactic representation can apply at both the type and value level. \<close>

nonterminal si

syntax
  "_si_metre"    :: "si" ("m")
  "_si_kilogram" :: "si" ("kg")
  "_si_second"   :: "si" ("s")
  "_si_ampere"   :: "si" ("A")
  "_si_kelvin"   :: "si" ("K")
  "_si_mole"     :: "si" ("mol")
  "_si_candela"  :: "si" ("cd")

  "_si_square"      :: "si \<Rightarrow> si" ("(_)\<^sup>2" [999] 999)
  "_si_cube"        :: "si \<Rightarrow> si" ("(_)\<^sup>3" [999] 999)
  "_si_quart"       :: "si \<Rightarrow> si" ("(_)\<^sup>4" [999] 999)

  "_si_inverse"     :: "si \<Rightarrow> si" ("(_\<^sup>-\<^sup>1)" [999] 999)
  "_si_invsquare"   :: "si \<Rightarrow> si" ("(_)\<^sup>-\<^sup>2" [999] 999)
  "_si_invcube"     :: "si \<Rightarrow> si" ("(_)\<^sup>-\<^sup>3" [999] 999)
  "_si_invquart"    :: "si \<Rightarrow> si" ("(_)\<^sup>-\<^sup>4" [999] 999)

  "_si_times"    :: "si \<Rightarrow> si \<Rightarrow> si" (infixl "\<cdot>" 70)

subsection \<open> Type Notation \<close>

text \<open> Pretty notation for SI units at the type level. \<close>

no_type_notation SIUnitT ("_[_]" [999,0] 999)

syntax
  "_si_unit"        :: "type \<Rightarrow> si \<Rightarrow> type" ("_[_]" [999,0] 999)
  "_si_print"       :: "type \<Rightarrow> si" ("SIPRINT'(_')")

translations
  (type) "'a[SIPRINT('d)]" == (type) "'a['d, SI]"
  (si) "SIPRINT('d)\<^sup>2" == (si) "SIPRINT('d\<^sup>2)"
  (si) "SIPRINT('d)\<^sup>3" == (si) "SIPRINT('d\<^sup>3)"
  (si) "SIPRINT('d)\<^sup>4" == (si) "SIPRINT('d\<^sup>4)"
  (si) "SIPRINT('d)\<^sup>-\<^sup>1" == (si) "SIPRINT('d\<^sup>-\<^sup>1)"
  (si) "SIPRINT('d)\<^sup>-\<^sup>2" == (si) "SIPRINT('d\<^sup>-\<^sup>2)"
  (si) "SIPRINT('d)\<^sup>-\<^sup>3" == (si) "SIPRINT('d\<^sup>-\<^sup>3)"
  (si) "SIPRINT('d)\<^sup>-\<^sup>4" == (si) "SIPRINT('d\<^sup>-\<^sup>4)"
  (si) "SIPRINT('d\<^sub>1) \<cdot> SIPRINT('d\<^sub>2)" == (si) "SIPRINT('d\<^sub>1 \<cdot> 'd\<^sub>2)"
  (si) "m"   == (si) "SIPRINT(L)"
  (si) "kg"  == (si) "SIPRINT(M)"
  (si) "s"   == (si) "SIPRINT(T)"
  (si) "A"   == (si) "SIPRINT(I)"
  (si) "K"   == (si) "SIPRINT(\<Theta>)"
  (si) "mol" == (si) "SIPRINT(N)"
  (si) "cd"  == (si) "SIPRINT(J)"

  "_si_invsquare x" <= "_si_inverse (_si_square x)"
  "_si_invcube x" <= "_si_inverse (_si_cube x)"
  "_si_invquart x" <= "_si_inverse (_si_quart x)"

  "_si_invsquare x" <= "_si_square (_si_inverse x)"
  "_si_invcube x" <= "_si_cube (_si_inverse  x)"
  "_si_invquart x" <= "_si_quart (_si_inverse x)"

typ "real[m\<cdot>s\<^sup>-\<^sup>2]"
typ "real[m\<cdot>s\<^sup>-\<^sup>2\<cdot>A\<^sup>2]"
term "5 *\<^sub>Q joule"

subsection \<open> Value Notations \<close>

text \<open> Pretty notation for SI units at the type level. Currently, it is not possible to support
  prefixes, as this would require a more sophisticated cartouche parser. \<close>

definition "SIQ n u = n *\<^sub>Q u"

syntax
  "_si_term"        :: "si \<Rightarrow> logic" ("SI'(_')")
  "_siq_term"       :: "logic \<Rightarrow> si \<Rightarrow> logic" ("SI[_, _]")
  "_siq_print"      :: "logic \<Rightarrow> si"

translations
  "_siq_term n u" => "CONST SIQ n (_si_term u)"
  "_siq_term n (_siq_print u)" <= "CONST SIQ n u"
  "_si_term (_si_times x y)" == "(_si_term x) \<^bold>\<cdot> (_si_term y)"
  "_si_term (_si_inverse x)" == "(_si_term x)\<^sup>-\<^sup>\<one>"
  "_si_term (_si_square x)" == "(_si_term x)\<^sup>\<two>"
  "_si_term (_si_cube x)" == "(_si_term x)\<^sup>\<two>"
  "SI(m)"   => "CONST metre"
  "SI(kg)"  => "CONST kilogram"
  "SI(s)"   => "CONST second"
  "SI(A)"   => "CONST ampere"
  "SI(K)"   => "CONST kelvin"
  "SI(mol)" => "CONST mole"
  "SI(cd)"  => "CONST candela"

  "_si_inverse (_siq_print x)" <= "_siq_print (x\<^sup>-\<^sup>\<one>)"
  "_si_invsquare (_siq_print x)" <= "_siq_print (x\<^sup>-\<^sup>\<two>)"
  "_si_invcube (_siq_print x)" <= "_siq_print (x\<^sup>-\<^sup>\<three>)"
  "_si_invquart (_siq_print x)" <= "_siq_print (x\<^sup>-\<^sup>\<four>)"

  "_si_square (_siq_print x)" <= "_siq_print (x\<^sup>\<two>)"
  "_si_cube (_siq_print x)" <= "_siq_print (x\<^sup>\<three>)"
  "_si_quart (_siq_print x)" <= "_siq_print (x\<^sup>\<four>)"
  "_si_times (_siq_print x) (_siq_print y)" <= "_siq_print (x \<^bold>\<cdot> y)"

  "_si_metre" <= "_siq_print (CONST metre)"
  "_si_kilogram" <= "_siq_print (CONST kilogram)"
  "_si_second" <= "_siq_print (CONST second)"
  "_si_ampere" <= "_siq_print (CONST ampere)"
  "_si_kelvin" <= "_siq_print (CONST kelvin)"
  "_si_mole" <= "_siq_print (CONST mole)"
  "_si_candela" <= "_siq_print (CONST candela)"

term "SI[5, m\<^sup>2]"
term "SI[22, m\<cdot>s\<^sup>-\<^sup>1]"

end