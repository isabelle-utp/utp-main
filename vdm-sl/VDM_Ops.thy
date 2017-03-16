theory VDM_Ops
imports PFOL
begin
  
text {* The following function checks if an input x satisfies a predicate (belongs to a set). If
  it does then it returns the value backed, wrapped up in the option type, otherwise it returns None. *}
  
definition sat :: "('a set) \<Rightarrow> 'a \<Rightarrow> 'a option" where
"sat P x = (if (x \<in> P) then Some x else None)"
  
text {* upfun takes a set which is a predicate on the input values, a total HOL function and turns
  it into a function on option types. The resulting value is defined if (1) each input is defined
  and (2) the input satisfies the predicate. *}

definition upfun :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b::type) \<Rightarrow> ('a option \<Rightarrow> 'b option)" where
[upred_defs]: "upfun A f = (\<lambda> x. (x \<bind> sat A) \<bind> Some \<circ> f)"

abbreviation "upfun' \<equiv> upfun UNIV"
  
lemma upfun_app_1: "upfun A f (Some x) = (if (x \<in> A) then Some (f x) else None)"
  by (simp add: upfun_def sat_def)
    
lemma upfun_app_2: "upfun A f None = None"
  by (simp add: upfun_def sat_def)
  
text {* bpfun is upfun for two argument functions *}
    
definition bpfun :: "('a::type * 'b::type) set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c::type) \<Rightarrow> ('a option \<Rightarrow> 'b option \<Rightarrow> 'c option)" where
[upred_defs]: "bpfun AB f = (\<lambda> v1 v2. do { x \<leftarrow> v1; y \<leftarrow> v2; sat AB (x, y) } \<bind> Some \<circ> uncurry f)"

abbreviation "bpfun' \<equiv> bpfun UNIV"
  
lemma bpfun_app_1 [simp]: "bpfun A f (Some x) (Some y) = (if ((x, y) \<in> A) then Some (f x y) else None)"
  by (simp add: bpfun_def sat_def)
    
lemma bpfun_app_2 [simp]: "bpfun A f None y = None"
  by (simp add: bpfun_def sat_def)

lemma bpfun_app_3 [simp]: "bpfun A f x None = None"
  by (simp add: bpfun_def sat_def)

text {* tpfun is upfun for three argument functions *}
    
definition tpfun :: "('a::type * 'b::type * 'c::type) set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd::type) \<Rightarrow> ('a option \<Rightarrow> 'b option \<Rightarrow> 'c option \<Rightarrow> 'd option)" where
[upred_defs]: "tpfun ABC f = (\<lambda> v1 v2 v3. do { x \<leftarrow> v1; y \<leftarrow> v2; z \<leftarrow> v3; sat ABC (x, y, z) } \<bind> Some \<circ> (\<lambda> (x,y,z). f x y z))"

abbreviation "tpfun' \<equiv> tpfun UNIV"

text {* Next we instantiate some of the numerical and arithmetic type classes for option types
  by lifting the corresponding HOL definitions. *}
  
instantiation option :: (zero) zero
begin
  definition zero_option :: "'a option" where
  [upred_defs]: "zero_option = Some 0"
  instance ..
end
  
instantiation option :: (one) one
begin
  definition one_option :: "'a option" where
  [upred_defs]: "one_option = Some 1"
  instance ..
end

instantiation option :: (plus) plus
begin
  definition plus_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  [upred_defs]: "plus_option = bpfun' (op +)"
  instance ..
end
  
instantiation option :: (minus) minus
begin
  definition minus_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  [upred_defs]: "minus_option = bpfun' (op -)"
  instance ..
end
 
instantiation option :: (times) times
begin
 definition times_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  [upred_defs]: "times_option = bpfun' (op *)"
  instance ..
end

instantiation option :: (uminus) uminus
begin
definition uminus_option :: "'a option \<Rightarrow> 'a option" where
  [upred_defs]: "uminus_option = upfun' uminus"
  instance ..
end

instantiation option :: (modulo) modulo
begin
definition modulo_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  [upred_defs]: "modulo_option = bpfun' (op mod)"
  instance ..
end 

instantiation option :: (abs) abs
begin
definition abs_option :: "'a option \<Rightarrow> 'a option" where
  [upred_defs]: "abs_option = upfun' abs"
  instance ..
end 
  
text {* Inverse is the reciprocal 1/x, and division is obvious. These two functions are lifted differently
  than plus because we need to check if the denominator is 0 or not. *}
  
instantiation option :: ("{zero, inverse}") inverse
begin
  definition inverse_option :: "'a option \<Rightarrow> 'a option" where
  [upred_defs]: "inverse_option = upfun {x. x \<noteq> 0} inverse"

  definition divide_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  [upred_defs]: "divide_option = bpfun {(x, y). y \<noteq> 0} divide"

  instance ..
end
  
text {* We prove that our lifted plus type is a semigroup; i.e. it is associative *}
  
instance option :: (semigroup_add) semigroup_add
  apply (intro_classes)
  apply (simp add: plus_option_def)
  apply (rename_tac x y z)
  apply (case_tac x, case_tac[!] y, case_tac[!] z)
  apply (simp_all add: add.assoc)
done 
  
text {* We also prove its a numeral, meaning we can write down number 5 :: 'a option for example. *}
  
instance option :: (numeral) numeral ..
  
text {* Some example definedness proofs *}

lemma plus: "1 + None = None"
  by (simp add: plus_option_def)  
  
lemma div_ex_1: "1 / None = None"
  by (simp add: divide_option_def)

lemma div_ex_2: "1 / 0 = None"
  by (simp add: divide_option_def zero_option_def one_option_def)
    
end