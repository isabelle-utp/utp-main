theory Function_Ring
  imports "HOL-Algebra.Ring" "HOL-Library.FuncSet" "HOL-Algebra.Module"
begin

text\<open>
  This theory formalizes basic facts about the ring of extensional functions from a fixed set to
  a fixed ring. This will be useful for providing a generic framework for various constructions
  related to the $p$-adics such as polynomial evaluation and sequences. The rings of semialgebraic
  functions will be defined as subrings of these function rings, which will be necessary for the
  proof of $p$-adic quantifier elimination.
\<close>

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>The Ring of Extensional Functions from a Fixed Base Set to a Fixed Base Ring\<close>
(**************************************************************************************************)
(**************************************************************************************************)

  (**************************************************************************************************)
  (**************************************************************************************************)
  subsection\<open>Basic Operations on Extensional Functions\<close>
  (**************************************************************************************************)
  (**************************************************************************************************)

definition function_mult:: "'c set \<Rightarrow> ('a, 'b) ring_scheme \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'a)" where
"function_mult S R f g = (\<lambda>x \<in> S. (f x) \<otimes>\<^bsub>R\<^esub> (g x))"

abbreviation(input) ring_function_mult:: "('a, 'b) ring_scheme \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" where
"ring_function_mult R f g \<equiv> function_mult (carrier R) R f g"

definition function_add:: "'c set \<Rightarrow> ('a, 'b) ring_scheme \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'a)" where
"function_add S R f g = (\<lambda>x \<in> S. (f x) \<oplus>\<^bsub>R\<^esub> (g x))"

abbreviation(input) ring_function_add:: "('a, 'b) ring_scheme \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" where
"ring_function_add R f g \<equiv> function_add (carrier R) R f g"

definition function_one:: "'c set \<Rightarrow> ('a, 'b) ring_scheme \<Rightarrow> ('c \<Rightarrow> 'a)" where
"function_one S R = (\<lambda>x \<in> S. \<one>\<^bsub>R\<^esub>)"

abbreviation(input) ring_function_one :: "('a, 'b) ring_scheme \<Rightarrow> ('a \<Rightarrow> 'a)" where
"ring_function_one R \<equiv> function_one (carrier R) R"

definition function_zero:: "'c set \<Rightarrow> ('a, 'b) ring_scheme \<Rightarrow> ('c \<Rightarrow> 'a)" where
"function_zero S R = (\<lambda>x \<in> S. \<zero>\<^bsub>R\<^esub>)"

abbreviation(input) ring_function_zero :: "('a, 'b) ring_scheme \<Rightarrow> ('a \<Rightarrow> 'a)" where
"ring_function_zero R \<equiv> function_zero (carrier R) R"

definition function_uminus:: "'c set \<Rightarrow> ('a, 'b) ring_scheme \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'a)" where
"function_uminus S R a = (\<lambda> x \<in> S. \<ominus>\<^bsub>R\<^esub> (a x))"

definition ring_function_uminus:: " ('a, 'b) ring_scheme \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" where
"ring_function_uminus R a = function_uminus (carrier R) R a"

definition function_scalar_mult:: "'c set \<Rightarrow> ('a, 'b) ring_scheme \<Rightarrow> 'a \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'a)" where
"function_scalar_mult S R a f = (\<lambda> x \<in> S. a \<otimes>\<^bsub>R\<^esub> (f x))"

  (**************************************************************************************************)
  (**************************************************************************************************)
  subsection\<open>Defining the Ring of Extensional Functions\<close>
  (**************************************************************************************************)
  (**************************************************************************************************)

definition function_ring:: "'c set \<Rightarrow> ('a, 'b) ring_scheme \<Rightarrow> ( 'a, 'c \<Rightarrow> 'a) module" where
"function_ring S R = \<lparr>
   carrier = extensional_funcset S (carrier R),
   Group.monoid.mult = (function_mult S R),
   one = (function_one S R),
   zero = (function_zero S R),
   add = (function_add S R),
   smult = function_scalar_mult S R \<rparr> "

text\<open>The following locale consists of a struct R, and a distinguished set S which is meant to serve as the domain for a ring of functions $S \to carrier R$. \<close>
locale struct_functions = 
  fixes R ::"('a, 'b) partial_object_scheme"  (structure) 
    and S :: "'c set" 

text\<open>The following are locales which fix a ring R (which may be commutative, a domain, or a field) and a function ring F of extensional functions from a fixed set S to $carrier R$\<close>
locale ring_functions  = struct_functions + R?: ring R +
  fixes F (structure)
  defines F_def: "F \<equiv> function_ring S R"

locale cring_functions = ring_functions + R?: cring R

locale domain_functions = ring_functions + R?: domain R

locale field_functions = ring_functions + R?: field R

sublocale cring_functions < ring_functions 
  apply (simp add: ring_functions_axioms)
  by (simp add: F_def)
  
sublocale domain_functions < ring_functions 
  apply (simp add: ring_functions_axioms)
  by (simp add: F_def)
  
sublocale domain_functions < cring_functions 
  apply (simp add: cring_functions_def is_cring ring_functions_axioms)
  by (simp add: F_def)

sublocale field_functions < domain_functions 
  apply (simp add: domain_axioms domain_functions_def ring_functions_axioms)
  by (simp add: F_def) 
    
sublocale field_functions < ring_functions
  apply (simp add: ring_functions_axioms)
  by (simp add: F_def) 

sublocale field_functions < cring_functions
  apply (simp add: cring_functions_axioms)
  by (simp add: F_def)

abbreviation(input) ring_function_ring:: "('a, 'b) ring_scheme \<Rightarrow> ('a, 'a \<Rightarrow> 'a) module" ("Fun") where
"ring_function_ring R \<equiv> function_ring (carrier R) R"


  (**************************************************************************************************)
  (**************************************************************************************************)
  subsection\<open>Algebraic Properties of the Basic Operations\<close>
  (**************************************************************************************************)
  (**************************************************************************************************)

    (**************************************************************************************************)
    (**************************************************************************************************)
    subsubsection\<open>Basic Carrier Facts\<close>
    (**************************************************************************************************)
    (**************************************************************************************************)

lemma(in ring_functions) function_ring_defs:
"carrier F = extensional_funcset S (carrier R)"
"(\<otimes>\<^bsub>F\<^esub>) = (function_mult S R)"
"(\<oplus>\<^bsub>F\<^esub>) = (function_add S R)"
"\<one>\<^bsub>F\<^esub> = function_one S R"
"\<zero>\<^bsub>F\<^esub> = function_zero S R"
"(\<odot>\<^bsub>F\<^esub>) = function_scalar_mult S R"
  unfolding F_def 
  by ( auto simp add: function_ring_def)

lemma(in ring_functions) function_ring_car_memE:
  assumes "a \<in> carrier F"
  shows "a \<in> extensional S"
        "a \<in> S \<rightarrow> carrier R"
  using assms function_ring_defs apply auto[1]
  using assms function_ring_defs  PiE_iff apply blast
  using assms  function_ring_defs(1) by fastforce
  
lemma(in ring_functions) function_ring_car_closed:
  assumes "a \<in> S"
  assumes "f \<in> carrier F"
  shows "f a \<in> carrier R"
  using assms   unfolding function_ring_def F_def by auto 
  
lemma(in ring_functions)  function_ring_not_car:
  assumes "a \<notin> S"
  assumes "f \<in> carrier F"
  shows "f a = undefined"
    using assms   unfolding function_ring_def F_def by auto 
    
lemma(in ring_functions)  function_ring_car_eqI:
  assumes "f \<in> carrier F"
  assumes "g \<in> carrier F"
  assumes "\<And>a. a \<in> S \<Longrightarrow> f a = g a"
  shows "f = g"
  using assms(1) assms(2) assms(3) extensionalityI function_ring_car_memE(1) by blast

lemma(in ring_functions) function_ring_car_memI:
  assumes "\<And>a. a \<in> S \<Longrightarrow> f a \<in> carrier R"
  assumes "\<And> a. a \<notin> S\<Longrightarrow> f a = undefined"
  shows "f \<in> carrier F"
  using function_ring_defs assms 
  unfolding extensional_funcset_def 
  by (simp add: \<open>\<And>a. a \<in> S \<Longrightarrow> f a \<in> carrier R\<close> extensional_def)

lemma(in ring) function_ring_car_memI:
  assumes "\<And>a. a \<in> S \<Longrightarrow> f a \<in> carrier R"
  assumes "\<And> a. a \<notin> S\<Longrightarrow> f a = undefined"
  shows "f \<in> carrier (function_ring S R)"
 by (simp add: assms(1) assms(2) local.ring_axioms ring_functions.function_ring_car_memI ring_functions.intro)

    (**************************************************************************************************)
    (**************************************************************************************************)
    subsubsection\<open>Basic Multiplication Facts\<close>
    (**************************************************************************************************)
    (**************************************************************************************************)

lemma(in ring_functions) function_mult_eval_car:
  assumes "a \<in> S"
  assumes "f \<in> carrier F"
  assumes "g \<in> carrier F"
  shows "(f \<otimes>\<^bsub>F\<^esub> g) a = (f a) \<otimes> (g a)"
  using assms function_ring_defs 
  unfolding function_mult_def 
  by simp

lemma(in ring_functions) function_mult_eval_closed:
  assumes "a \<in> S"
  assumes "f \<in> carrier F"
  assumes "g \<in> carrier F"
  shows "(f \<otimes>\<^bsub>F\<^esub> g) a \<in> carrier R"
  using assms function_mult_eval_car
  using F_def ring_functions.function_ring_car_closed ring_functions_axioms by fastforce
  
lemma(in ring_functions) fun_mult_closed:
  assumes "f \<in> carrier F"
  assumes "g \<in> carrier F"
  shows "f \<otimes>\<^bsub>F\<^esub> g \<in> carrier F"
  apply(rule function_ring_car_memI)
  apply (simp add: assms(1) assms(2) function_mult_eval_closed)
  by (simp add: function_mult_def function_ring_defs(2))

lemma(in ring_functions) fun_mult_eval_assoc:
  assumes "x \<in> carrier F"
  assumes "y \<in> carrier F" 
  assumes " z \<in> carrier F"
  assumes "a \<in> S"
  shows "(x \<otimes>\<^bsub>F\<^esub> y \<otimes>\<^bsub>F\<^esub> z) a = (x \<otimes>\<^bsub>F\<^esub> (y \<otimes>\<^bsub>F\<^esub> z)) a"
proof-
  have 0: "(x \<otimes>\<^bsub>F\<^esub> y \<otimes>\<^bsub>F\<^esub> z) a = (x a) \<otimes> (y a) \<otimes> (z a) "
    by (simp add: assms(1) assms(2) assms(3) assms(4) fun_mult_closed function_mult_eval_car)
  have 1: "(x \<otimes>\<^bsub>F\<^esub> (y \<otimes>\<^bsub>F\<^esub> z)) a = (x a) \<otimes> ((y a) \<otimes> (z a))"
    by (simp add: assms(1) assms(2) assms(3) assms(4) fun_mult_closed function_mult_eval_car)
  have 2:"(x \<otimes>\<^bsub>F\<^esub> (y \<otimes>\<^bsub>F\<^esub> z)) a = (x a) \<otimes> (y a) \<otimes> (z a)"
    using 1 assms 
    by (simp add: function_ring_car_closed m_assoc)    
  show ?thesis 
    using 0 2 by auto 
qed

lemma(in ring_functions) fun_mult_assoc:
  assumes "x \<in> carrier F"
  assumes "y \<in> carrier F" 
  assumes "z \<in> carrier F"
  shows "(x \<otimes>\<^bsub>F\<^esub> y \<otimes>\<^bsub>F\<^esub> z) = (x \<otimes>\<^bsub>F\<^esub> (y \<otimes>\<^bsub>F\<^esub> z))"
  using fun_mult_eval_assoc[of x]
  by (simp add: assms(1) assms(2) assms(3) fun_mult_closed function_ring_car_eqI)
    (**************************************************************************************************)
    (**************************************************************************************************)
    subsubsection\<open>Basic Addition Facts\<close>
    (**************************************************************************************************)
    (**************************************************************************************************)

lemma(in ring_functions) fun_add_eval_car:
  assumes "a \<in> S"
  assumes "f \<in> carrier F"
  assumes "g \<in> carrier F"
  shows "(f \<oplus>\<^bsub>F\<^esub> g) a = (f a) \<oplus> (g a)"
  by (simp add: assms(1) function_add_def function_ring_defs(3))

lemma(in ring_functions) fun_add_eval_closed:
  assumes "a \<in> S"
  assumes "f \<in> carrier F"
  assumes "g \<in> carrier F"
  shows "(f \<oplus>\<^bsub>F\<^esub> g) a \<in> carrier R"
  using assms unfolding F_def 
  using F_def fun_add_eval_car function_ring_car_closed 
  by auto

lemma(in ring_functions) fun_add_closed:
  assumes "f \<in> carrier F"
  assumes "g \<in> carrier F"
  shows "f \<oplus>\<^bsub>F\<^esub> g \<in> carrier F"
  apply(rule function_ring_car_memI)
  using assms unfolding F_def
  using F_def fun_add_eval_closed apply blast
  by (simp add: function_add_def function_ring_def)

lemma(in ring_functions) fun_add_eval_assoc:
  assumes "x \<in> carrier F"
  assumes "y \<in> carrier F" 
  assumes " z \<in> carrier F"
  assumes "a \<in> S"
  shows "(x \<oplus>\<^bsub>F\<^esub> y \<oplus>\<^bsub>F\<^esub> z) a = (x \<oplus>\<^bsub>F\<^esub> (y \<oplus>\<^bsub>F\<^esub> z)) a"
proof-
  have 0: "(x \<oplus>\<^bsub>F\<^esub> y \<oplus>\<^bsub>F\<^esub> z) a = (x a) \<oplus> (y a) \<oplus> (z a) "
    by (simp add: assms(1) assms(2) assms(3) assms(4) fun_add_closed fun_add_eval_car)
  have 1: "(x \<oplus>\<^bsub>F\<^esub> (y \<oplus>\<^bsub>F\<^esub> z)) a = (x a) \<oplus> ((y a) \<oplus> (z a))"
    by (simp add: assms(1) assms(2) assms(3) assms(4) fun_add_closed fun_add_eval_car)
  have 2:"(x \<oplus>\<^bsub>F\<^esub> (y \<oplus>\<^bsub>F\<^esub> z)) a = (x a) \<oplus> (y a) \<oplus> (z a)"
    using 1 assms 
    by (simp add: add.m_assoc function_ring_car_closed)   
  show ?thesis 
    using 0 2 by auto 
qed

lemma(in ring_functions) fun_add_assoc:
  assumes "x \<in> carrier F"
  assumes "y \<in> carrier F" 
  assumes " z \<in> carrier F"
  shows "x \<oplus>\<^bsub>F\<^esub> y \<oplus>\<^bsub>F\<^esub> z = x \<oplus>\<^bsub>F\<^esub> (y \<oplus>\<^bsub>F\<^esub> z)"
  apply(rule function_ring_car_eqI)
  using assms apply (simp add: fun_add_closed)
   apply (simp add: assms(1) assms(2) assms(3) fun_add_closed)
     by (simp add: assms(1) assms(2) assms(3) fun_add_eval_assoc)
  
lemma(in ring_functions) fun_add_eval_comm:
  assumes "a \<in> S"
  assumes "x \<in> carrier F"
  assumes "y \<in> carrier F" 
  shows "(x \<oplus>\<^bsub>F\<^esub> y) a = (y \<oplus>\<^bsub>F\<^esub> x) a"
  by (metis F_def assms(1) assms(2) assms(3) fun_add_eval_car ring.ring_simprules(10) ring_functions.function_ring_car_closed ring_functions_axioms ring_functions_def)
    
lemma(in ring_functions) fun_add_comm:
  assumes "x \<in> carrier F"
  assumes "y \<in> carrier F" 
  shows "x \<oplus>\<^bsub>F\<^esub> y = y \<oplus>\<^bsub>F\<^esub> x"
  using fun_add_eval_comm assms 
  by (metis (no_types, hide_lams) fun_add_closed function_ring_car_eqI)

    (**************************************************************************************************)
    (**************************************************************************************************)
    subsubsection\<open>Basic Facts About the Multiplicative Unit\<close>
    (**************************************************************************************************)
    (**************************************************************************************************)

lemma(in ring_functions) function_one_eval:
  assumes "a \<in> S"
  shows "\<one>\<^bsub>F\<^esub> a = \<one>"
  using assms function_ring_defs unfolding function_one_def  
  by simp
  
lemma(in ring_functions) function_one_closed:
"\<one>\<^bsub>F\<^esub> \<in>carrier F"
  apply(rule function_ring_car_memI)
  using function_ring_defs 
  using function_one_eval apply auto[1]
  by (simp add: function_one_def function_ring_defs(4))

lemma(in ring_functions) function_times_one_l:
  assumes "a \<in> carrier F"
  shows "\<one>\<^bsub>F\<^esub> \<otimes>\<^bsub>F\<^esub> a = a"
proof(rule function_ring_car_eqI)
  show "\<one>\<^bsub>F\<^esub> \<otimes>\<^bsub>F\<^esub> a \<in> carrier F"
    using assms fun_mult_closed function_one_closed 
    by blast
  show " a \<in> carrier F"
    using assms by simp 
  show "\<And>c. c \<in> S \<Longrightarrow> (\<one>\<^bsub>F\<^esub> \<otimes>\<^bsub>F\<^esub> a) c = a c "
    by (simp add: assms function_mult_eval_car function_one_eval function_one_closed function_ring_car_closed)
qed

lemma(in ring_functions) function_times_one_r:
  assumes "a \<in> carrier F"
  shows "a\<otimes>\<^bsub>F\<^esub> \<one>\<^bsub>F\<^esub>  = a"
proof(rule function_ring_car_eqI)
  show "a\<otimes>\<^bsub>F\<^esub> \<one>\<^bsub>F\<^esub> \<in> carrier F"
    using assms fun_mult_closed function_one_closed 
    by blast
  show " a \<in> carrier F"
    using assms by simp 
  show "\<And>c. c \<in> S \<Longrightarrow> (a\<otimes>\<^bsub>F\<^esub> \<one>\<^bsub>F\<^esub>) c = a c "
    using assms 
    by (simp add: function_mult_eval_car function_one_eval function_one_closed function_ring_car_closed)
qed

    (**************************************************************************************************)
    (**************************************************************************************************)
    subsubsection\<open>Basic Facts About the Additive Unit\<close>
    (**************************************************************************************************)
    (**************************************************************************************************)

lemma(in ring_functions) function_zero_eval:
  assumes "a \<in> S"
  shows "\<zero>\<^bsub>F\<^esub> a = \<zero>"
  using assms function_ring_defs 
  unfolding function_zero_def
  by simp
  
lemma(in ring_functions) function_zero_closed:
"\<zero>\<^bsub>F\<^esub> \<in>carrier F"
  apply(rule function_ring_car_memI)
  apply (simp add: function_zero_eval)
  by (simp add: function_ring_defs(5) function_zero_def)

lemma(in ring_functions) fun_add_zeroL:
  assumes "a \<in> carrier F"
  shows "\<zero>\<^bsub>F\<^esub> \<oplus>\<^bsub>F\<^esub> a = a"
proof(rule function_ring_car_eqI)
  show "\<zero>\<^bsub>F\<^esub> \<oplus>\<^bsub>F\<^esub> a \<in> carrier F"
    using assms fun_add_closed function_zero_closed 
    by blast
  show "a \<in> carrier F"
    using assms by simp 
  show "\<And>c. c \<in> S \<Longrightarrow> (\<zero>\<^bsub>F\<^esub> \<oplus>\<^bsub>F\<^esub> a) c = a c "
    using assms F_def fun_add_eval_car function_zero_closed 
      ring_functions.function_zero_eval ring_functions_axioms 
    by (simp add: ring_functions.function_zero_eval function_ring_car_closed)
qed

lemma(in ring_functions) fun_add_zeroR:
  assumes "a \<in> carrier F"
  shows "a \<oplus>\<^bsub>F\<^esub> \<zero>\<^bsub>F\<^esub> = a"
  using assms fun_add_comm fun_add_zeroL 
  by (simp add: function_zero_closed)

    (**************************************************************************************************)
    (**************************************************************************************************)
    subsubsection\<open>Distributive Laws\<close>
    (**************************************************************************************************)
    (**************************************************************************************************)

lemma(in ring_functions) function_mult_r_distr: 
  assumes "x \<in> carrier F"
  assumes" y \<in> carrier F"
  assumes " z \<in> carrier F"
  shows " (x \<oplus>\<^bsub>F\<^esub> y) \<otimes>\<^bsub>F\<^esub> z = x \<otimes>\<^bsub>F\<^esub> z \<oplus>\<^bsub>F\<^esub> y \<otimes>\<^bsub>F\<^esub> z"
proof(rule function_ring_car_eqI)
  show "(x \<oplus>\<^bsub>F\<^esub> y) \<otimes>\<^bsub>F\<^esub> z \<in> carrier F"
    by (simp add: assms(1) assms(2) assms(3) fun_add_closed fun_mult_closed)      
  show "x \<otimes>\<^bsub>F\<^esub> z \<oplus>\<^bsub>F\<^esub> y \<otimes>\<^bsub>F\<^esub> z \<in> carrier F"
    by (simp add: assms(1) assms(2) assms(3) fun_add_closed fun_mult_closed)   
  show  "\<And>a. a \<in> S \<Longrightarrow> ((x \<oplus>\<^bsub>F\<^esub> y) \<otimes>\<^bsub>F\<^esub> z) a = (x \<otimes>\<^bsub>F\<^esub> z \<oplus>\<^bsub>F\<^esub> y \<otimes>\<^bsub>F\<^esub> z) a"
  proof-
    fix a
    assume A: "a \<in> S"
    show "((x \<oplus>\<^bsub>F\<^esub> y) \<otimes>\<^bsub>F\<^esub> z) a = (x \<otimes>\<^bsub>F\<^esub> z \<oplus>\<^bsub>F\<^esub> y \<otimes>\<^bsub>F\<^esub> z) a"
      using A assms fun_add_eval_car[of a x y]  fun_add_eval_car[of a "x \<otimes>\<^bsub>F\<^esub>z" "y \<otimes>\<^bsub>F\<^esub> z"] 
            function_mult_eval_car[of a "x \<oplus>\<^bsub>F\<^esub> y" z] semiring_simprules(10) 
            F_def 
      by (smt fun_add_closed function_mult_eval_car function_ring_car_closed 
          ring_functions.fun_mult_closed ring_functions_axioms)            
  qed
qed    

lemma(in ring_functions) function_mult_l_distr:
  assumes "x \<in> carrier F"
  assumes" y \<in> carrier F"
  assumes " z \<in> carrier F"
  shows "z \<otimes>\<^bsub>F\<^esub> (x \<oplus>\<^bsub>F\<^esub> y) = z \<otimes>\<^bsub>F\<^esub> x \<oplus>\<^bsub>F\<^esub> z \<otimes>\<^bsub>F\<^esub> y"
proof(rule function_ring_car_eqI)
  show "z \<otimes>\<^bsub>F\<^esub> (x \<oplus>\<^bsub>F\<^esub> y) \<in> carrier F"
    by (simp add: assms(1) assms(2) assms(3) fun_add_closed fun_mult_closed)     
  show "z \<otimes>\<^bsub>F\<^esub> x \<oplus>\<^bsub>F\<^esub> z \<otimes>\<^bsub>F\<^esub> y \<in> carrier F"
    by (simp add: assms(1) assms(2) assms(3) fun_add_closed fun_mult_closed)   
  show  "\<And>a. a \<in> S \<Longrightarrow> (z \<otimes>\<^bsub>F\<^esub> (x \<oplus>\<^bsub>F\<^esub> y)) a = (z \<otimes>\<^bsub>F\<^esub> x \<oplus>\<^bsub>F\<^esub> z \<otimes>\<^bsub>F\<^esub> y) a"
  proof-
    fix a
    assume A: "a \<in> S"
    show "(z \<otimes>\<^bsub>F\<^esub> (x \<oplus>\<^bsub>F\<^esub> y)) a = (z \<otimes>\<^bsub>F\<^esub> x \<oplus>\<^bsub>F\<^esub> z \<otimes>\<^bsub>F\<^esub> y) a"
      using A assms function_ring_defs fun_add_closed fun_mult_closed 
            function_mult_eval_car[of a z "x \<oplus>\<^bsub>F\<^esub> y"] 
            function_mult_eval_car[of a z x] 
            function_mult_eval_car[of a z y] 
            fun_add_eval_car[of a x y]
            semiring_simprules(13) 
            fun_add_eval_car function_ring_car_closed by auto  
  qed
qed    

    (**************************************************************************************************)
    (**************************************************************************************************)
    subsubsection\<open>Additive Inverses\<close>
    (**************************************************************************************************)
    (**************************************************************************************************)

lemma(in ring_functions) function_uminus_closed:
  assumes "f \<in> carrier F"
  shows "function_uminus S R f \<in> carrier F"
proof(rule function_ring_car_memI)
  show "\<And>a. a \<in> S \<Longrightarrow> function_uminus S R f a \<in> carrier R"
    using assms function_ring_car_closed[of _ f] unfolding function_uminus_def 
    by simp       
  show "\<And>a. a \<notin> S \<Longrightarrow> function_uminus S R f a = undefined"
    by (simp add: function_uminus_def)
qed

lemma(in ring_functions) function_uminus_eval:
  assumes "a \<in> S"
  assumes "f \<in> carrier F"
  shows "(function_uminus S R f) a = \<ominus> (f a)"
  using assms unfolding function_uminus_def 
  by simp

lemma(in ring_functions) function_uminus_add_r:
  assumes "a \<in> S"
  assumes "f \<in> carrier F"
  shows "f \<oplus>\<^bsub>F\<^esub> function_uminus S R f = \<zero>\<^bsub>F\<^esub>"
  apply(rule function_ring_car_eqI) 
  using assms  fun_add_closed function_uminus_closed apply blast
    unfolding F_def  using F_def function_zero_closed apply blast
      using F_def assms(2) fun_add_eval_car function_ring_car_closed function_uminus_closed 
      function_uminus_eval function_zero_eval r_neg by auto

lemma(in ring_functions) function_uminus_add_l:
  assumes "a \<in> S"
  assumes "f \<in> carrier F"
  shows "function_uminus S R f \<oplus>\<^bsub>F\<^esub> f = \<zero>\<^bsub>F\<^esub>"
  using assms(1) assms(2) fun_add_comm function_uminus_add_r function_uminus_closed by auto
  

    (**************************************************************************************************)
    (**************************************************************************************************)
    subsubsection\<open>Scalar Multiplication\<close>
    (**************************************************************************************************)
    (**************************************************************************************************)

lemma(in ring_functions) function_smult_eval:
  assumes "a \<in> carrier R"
  assumes  "f \<in> carrier F"
  assumes "b \<in> S"
  shows "(a \<odot>\<^bsub>F\<^esub> f) b = a \<otimes> (f b)"
  using function_ring_defs(6) unfolding function_scalar_mult_def 
  by(simp add: assms)

lemma(in ring_functions) function_smult_closed:
  assumes "a \<in> carrier R"
  assumes  "f \<in> carrier F"
  shows "a \<odot>\<^bsub>F\<^esub> f \<in> carrier F"
  apply(rule function_ring_car_memI)
  using function_smult_eval assms 
  apply (simp add: function_ring_car_closed)
  using function_scalar_mult_def F_def 
  by (metis function_ring_defs(6) restrict_apply)

lemma(in ring_functions) function_smult_assoc1:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  assumes  "f \<in> carrier F"
  shows "b \<odot>\<^bsub>F\<^esub> (a \<odot>\<^bsub>F\<^esub> f)  = (b \<otimes> a)\<odot>\<^bsub>F\<^esub>f"
  apply(rule function_ring_car_eqI)
  using assms function_smult_closed apply simp
    using assms function_smult_closed apply simp
       by (metis F_def assms(1) assms(2) assms(3) function_mult_eval_closed function_one_closed
        function_smult_eval function_times_one_r m_assoc m_closed ring_functions.function_smult_closed ring_functions_axioms)

lemma(in ring_functions) function_smult_assoc2:
  assumes "a \<in> carrier R"
  assumes  "f \<in> carrier F"
  assumes "g \<in> carrier F"
  shows "(a \<odot>\<^bsub>F\<^esub> f)\<otimes>\<^bsub>F\<^esub>g  = a \<odot>\<^bsub>F\<^esub> (f \<otimes>\<^bsub>F\<^esub> g)"
  apply(rule function_ring_car_eqI)
  using assms function_smult_closed apply (simp add: fun_mult_closed)
   apply (simp add: assms(1) assms(2) assms(3) fun_mult_closed function_smult_closed)
     by (metis (full_types) F_def assms(1) assms(2) assms(3) fun_mult_closed 
      function_mult_eval_car function_smult_closed function_smult_eval m_assoc ring_functions.function_ring_car_closed ring_functions_axioms)     

lemma(in ring_functions) function_smult_one:
  assumes  "f \<in> carrier F"
  shows "\<one>\<odot>\<^bsub>F\<^esub>f = f"
  apply(rule function_ring_car_eqI)
  apply (simp add: assms function_smult_closed)
   apply (simp add: assms)
     by (simp add: assms function_ring_car_closed function_smult_eval)
     
lemma(in ring_functions) function_smult_l_distr:
"[| a \<in> carrier R; b \<in> carrier R; x \<in> carrier F |] ==>
      (a \<oplus> b) \<odot>\<^bsub>F\<^esub> x = a \<odot>\<^bsub>F\<^esub> x \<oplus>\<^bsub>F\<^esub> b \<odot>\<^bsub>F\<^esub> x"
  apply(rule function_ring_car_eqI)
  apply (simp add: function_smult_closed)
   apply (simp add: fun_add_closed function_smult_closed)   
    using function_smult_eval 
    by (simp add: fun_add_eval_car function_ring_car_closed function_smult_closed l_distr)
    
lemma(in ring_functions) function_smult_r_distr:
 "[| a \<in> carrier R; x \<in> carrier F; y \<in> carrier F |] ==>
      a \<odot>\<^bsub>F\<^esub> (x \<oplus>\<^bsub>F\<^esub> y) = a \<odot>\<^bsub>F\<^esub> x \<oplus>\<^bsub>F\<^esub> a \<odot>\<^bsub>F\<^esub> y"
  apply(rule function_ring_car_eqI)
  apply (simp add: fun_add_closed function_smult_closed)
   apply (simp add: fun_add_closed function_smult_closed)
    by (simp add: fun_add_closed fun_add_eval_car function_ring_car_closed function_smult_closed function_smult_eval r_distr) 

    (**************************************************************************************************)
    (**************************************************************************************************)
    subsubsection\<open>The Ring of Functions Forms an Algebra\<close>
    (**************************************************************************************************)
    (**************************************************************************************************)

lemma(in ring_functions) function_ring_is_abelian_group:
"abelian_group F"
  apply(rule abelian_groupI)
  apply (simp add: fun_add_closed)
      apply (simp add: function_zero_closed)
        using fun_add_assoc apply simp  
          apply (simp add: fun_add_comm)
            apply (simp add: fun_add_comm fun_add_zeroR function_zero_closed)
              using fun_add_zeroL function_ring_car_eqI function_uminus_add_l 
                  function_uminus_closed function_zero_closed by blast

lemma(in ring_functions) function_ring_is_monoid:
"monoid F"
  apply(rule monoidI)
    apply (simp add: fun_mult_closed)
     apply (simp add: function_one_closed)
      apply (simp add: fun_mult_assoc)
       apply (simp add: function_times_one_l)
        by (simp add: function_times_one_r)
      
lemma(in ring_functions) function_ring_is_ring:
"ring F"
  apply(rule ringI)
     apply (simp add: function_ring_is_abelian_group)
      apply (simp add: function_ring_is_monoid)
        apply (simp add: function_mult_r_distr)
          by (simp add: function_mult_l_distr)

sublocale ring_functions < F?: ring F
  by (rule function_ring_is_ring)

lemma(in cring_functions) function_mult_comm: 
  assumes "x \<in> carrier F"
  assumes" y \<in> carrier F"
  shows "x \<otimes>\<^bsub>F\<^esub> y = y \<otimes>\<^bsub>F\<^esub> x"
  apply(rule function_ring_car_eqI)
  apply (simp add: assms(1) assms(2) fun_mult_closed)
   apply (simp add: assms(1) assms(2) fun_mult_closed)
    by (simp add: assms(1) assms(2) function_mult_eval_car function_ring_car_closed m_comm)  

lemma(in cring_functions) function_ring_is_comm_monoid:
"comm_monoid F"
  apply(rule comm_monoidI)
  using fun_mult_assoc function_one_closed
  apply (simp add: fun_mult_closed)
     apply (simp add: function_one_closed)
      apply (simp add: fun_mult_assoc)
        apply (simp add: function_times_one_l)
          by (simp add: function_mult_comm)    
    
lemma(in cring_functions) function_ring_is_cring:
"cring F"
  apply(rule cringI)
    apply (simp add: function_ring_is_abelian_group)
      apply (simp add: function_ring_is_comm_monoid)
        by (simp add: function_mult_r_distr)

lemma(in cring_functions) function_ring_is_algebra:
"algebra R F"
  apply(rule algebraI)
   apply (simp add: is_cring)
    apply (simp add: function_ring_is_cring)
     using function_smult_closed apply blast
      apply (simp add: function_smult_l_distr)
       apply (simp add: function_smult_r_distr)
        apply (simp add: function_smult_assoc1)
         apply (simp add: function_smult_one)
          by (simp add: function_smult_assoc2)
            
lemma(in ring_functions) function_uminus:
  assumes "f \<in> carrier F"
  shows "\<ominus>\<^bsub>F\<^esub> f = (function_uminus S R) f"
  using assms a_inv_def[of F] 
  by (metis F_def abelian_group.a_group abelian_group.r_neg function_uminus_add_r function_uminus_closed group.inv_closed partial_object.select_convs(1) ring.ring_simprules(18) ring_functions.function_ring_car_eqI ring_functions.function_ring_is_abelian_group ring_functions.function_ring_is_ring ring_functions_axioms)

lemma(in ring_functions) function_uminus_eval':
  assumes "f \<in> carrier F"
  assumes "a \<in> S"
  shows "(\<ominus>\<^bsub>F\<^esub> f) a = (function_uminus S R) f a"
  using assms 
  by (simp add: function_uminus)

lemma(in ring_functions) function_uminus_eval'':
  assumes "f \<in> carrier F"
  assumes "a \<in> S"
  shows "(\<ominus>\<^bsub>F\<^esub> f) a = \<ominus> (f a)"
  using assms(1) assms(2) function_uminus 
  by (simp add: function_uminus_eval)

sublocale cring_functions < F?: algebra R F
  using function_ring_is_algebra by auto 

    (**************************************************************************************************)
    (**************************************************************************************************)
    subsection\<open>Constant Functions\<close>
    (**************************************************************************************************)
    (**************************************************************************************************)

definition constant_function  where
"constant_function S a =(\<lambda>x \<in> S. a)"

abbreviation(in ring_functions)(input) const   where
"const \<equiv> constant_function S"

lemma(in ring_functions) constant_function_closed:
  assumes "a \<in> carrier R"
  shows "const a \<in> carrier F"
  apply(rule function_ring_car_memI)
  unfolding constant_function_def 
  apply (simp add: assms)
    by simp

lemma(in ring_functions) constant_functionE: 
  assumes "a \<in> carrier R"
  assumes "b \<in> S"
  shows "const a b = a"
  by (simp add: assms(2) constant_function_def)

lemma(in ring_functions) constant_function_add: 
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "const (a \<oplus>\<^bsub>R\<^esub> b) = (const a) \<oplus>\<^bsub>F\<^esub> (const b) " 
  apply(rule function_ring_car_eqI)
    apply (simp add: constant_function_closed assms(1) assms(2))
      using assms(1) constant_function_closed assms(2) fun_add_closed apply auto[1]
        by (simp add: assms(1) assms(2) constant_function_closed constant_functionE fun_add_eval_car)

lemma(in ring_functions) constant_function_mult: 
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "const (a \<otimes>\<^bsub>R\<^esub> b) = (const a) \<otimes>\<^bsub>F\<^esub> (const b)" 
  apply(rule function_ring_car_eqI)
    apply (simp add: constant_function_closed assms(1) assms(2))
      using assms(1) constant_function_closed assms(2) fun_mult_closed apply auto[1]
        by (simp add: constant_function_closed assms(1) assms(2) constant_functionE function_mult_eval_car)
      
lemma(in ring_functions) constant_function_minus: 
  assumes "a \<in> carrier R"
  shows "\<ominus>\<^bsub>F\<^esub>(const a) = (const (\<ominus>\<^bsub>R\<^esub> a)) " 
apply(rule function_ring_car_eqI)
  apply (simp add: constant_function_closed assms local.function_uminus)
   apply (simp add: constant_function_closed assms function_uminus_closed)
    apply (simp add: constant_function_closed assms)
      by (simp add: constant_function_closed assms constant_functionE function_uminus_eval'')

lemma(in ring_functions) function_one_is_constant:
"const \<one> = \<one>\<^bsub>F\<^esub>"
  unfolding F_def 
  apply(rule function_ring_car_eqI)
  apply (simp add: constant_function_closed)
  using F_def function_one_closed apply auto[1]
  using F_def constant_functionE function_one_eval by auto

lemma(in ring_functions) function_zero_is_constant:
"const \<zero> = \<zero>\<^bsub>F\<^esub>"
   apply(rule function_ring_car_eqI)
  apply (simp add: constant_function_closed)
  using F_def function_zero_closed apply auto[1]
  using F_def constant_functionE function_zero_eval by auto


  (**************************************************************************************************)
  (**************************************************************************************************)
  subsection\<open>Special Examples of Functions Rings\<close>
  (**************************************************************************************************)
  (**************************************************************************************************)

    (**************************************************************************************************)
    (**************************************************************************************************)
    subsubsection\<open>Functions from the Carrier of a Ring to Itself\<close>
    (**************************************************************************************************)
    (**************************************************************************************************)


locale U_function_ring = ring

locale U_function_cring = U_function_ring + cring

sublocale U_function_ring <  S?: struct_functions R "carrier R" 
  done 

sublocale U_function_ring  <  FunR?: ring_functions R "carrier R" "Fun R"
  apply (simp add: local.ring_axioms ring_functions.intro)
    by simp

sublocale U_function_cring <  FunR?: cring_functions R "carrier R" "Fun R"
  apply (simp add: cring_functions_def is_cring ring_functions_axioms)
    by simp
    
abbreviation(in U_function_ring)(input) ring_compose :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" where
"ring_compose \<equiv> compose (carrier R)"
  
lemma(in U_function_ring) ring_function_ring_comp:
  assumes "f \<in> carrier (Fun R)"
  assumes "g \<in> carrier (Fun R)"
  shows "ring_compose f g \<in> carrier (Fun R)"
  apply(rule function_ring_car_memI) 
  apply (simp add: assms(1) assms(2) compose_eq)
   apply (simp add: assms(1) assms(2) function_ring_car_closed)
     by (meson compose_extensional extensional_arb)
  
abbreviation(in U_function_ring)(input) ring_const ("\<cc>\<index>") where
"ring_const \<equiv> constant_function (carrier R)"

lemma(in ring_functions) function_nat_pow_eval:
  assumes "f \<in> carrier F"
  assumes "s \<in> S"
  shows "(f[^]\<^bsub>F\<^esub>(n::nat)) s = (f s)[^]n"
  apply(induction n)
  using assms(2) function_one_eval apply auto[1]
  by (simp add: assms(1) assms(2) function_mult_eval_car function_ring_is_monoid monoid.nat_pow_closed)
    

context U_function_ring 
begin

definition a_translate :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"a_translate = (\<lambda> r \<in> carrier R. restrict ((add R) r) (carrier R))"

definition m_translate :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"m_translate  = (\<lambda> r \<in> carrier R. restrict ((mult R) r) (carrier R))"

definition nat_power :: "nat \<Rightarrow> 'a \<Rightarrow> 'a" where 
"nat_power = (\<lambda>(n::nat). restrict (\<lambda>a.  a[^]\<^bsub>R\<^esub>n) (carrier R)) "

text\<open>Restricted operations are in Fs\<close>

lemma a_translate_functions:
  assumes "c \<in> carrier R"
  shows "a_translate c \<in> carrier (Fun R)"
  apply(rule function_ring_car_memI)
  using assms a_translate_def 
   apply simp
  using assms a_translate_def 
  by simp  

lemma m_translate_functions:
  assumes "c \<in> carrier R"
  shows "m_translate c \<in> carrier (Fun R)"
  apply(rule function_ring_car_memI)
  using assms m_translate_def 
  apply simp
    using assms m_translate_def 
  by simp

lemma nat_power_functions:
  shows "nat_power n \<in> carrier (Fun R)"
  apply(rule function_ring_car_memI)
  using  nat_power_def 
   apply simp
  by (simp add: nat_power_def)

text\<open>Restricted operations simps\<close>

lemma a_translate_eq:
  assumes "c \<in> carrier R"
  assumes "a \<in> carrier R"
  shows "a_translate c a = c \<oplus> a"
  by (simp add: a_translate_def assms(1) assms(2))

lemma a_translate_eq':
  assumes "c \<in> carrier R"
  assumes "a \<notin> carrier R"
  shows "a_translate c a = undefined"
  by (meson a_translate_functions assms(1) assms(2) function_ring_not_car)

lemma a_translate_eq'':
  assumes "c \<notin> carrier R"
  shows "a_translate c = undefined"
  by (simp add: a_translate_def assms)

lemma m_translate_eq:
  assumes "c \<in> carrier R"
  assumes "a \<in> carrier R"
  shows "m_translate c a = c \<otimes> a"
  by (simp add: m_translate_def assms(1) assms(2))

lemma m_translate_eq':
  assumes "c \<in> carrier R"
  assumes "a \<notin> carrier R"
  shows "m_translate c a = undefined "
  by (meson m_translate_functions assms(1) assms(2) function_ring_not_car)

lemma m_translate_eq'':
  assumes "c \<notin> carrier R"
  shows "m_translate c = undefined"
  by (simp add: m_translate_def assms)

lemma nat_power_eq:
  assumes "a \<in> carrier R"
  shows "nat_power n a = a[^]\<^bsub>R\<^esub> n"
  by (simp add: assms nat_power_def)

lemma nat_power_eq':
  assumes "a \<notin> carrier R"
  shows "nat_power n a = undefined"
  by (simp add: assms nat_power_def)

text\<open>Constant ring\_function properties\<close>

lemma constant_function_eq:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "\<cc>\<^bsub>a\<^esub> b = a"
  using assms 
    
  by (simp add: constant_functionE)
    
lemma constant_function_eq':
  assumes "a \<in> carrier R"
  assumes "b \<notin> carrier R"
  shows "\<cc>\<^bsub>a\<^esub> b = undefined"
  by (simp add: constant_function_closed assms(1) assms(2) function_ring_not_car)
    
text\<open>Compound expressions from algebraic operations\<close>
end 

definition monomial_function where
"monomial_function R c (n::nat) = (\<lambda> x \<in> carrier R. c \<otimes>\<^bsub>R\<^esub> (x[^]\<^bsub>R\<^esub>n))"

context U_function_ring
begin

abbreviation monomial where
"monomial \<equiv> monomial_function R"

lemma monomial_functions:
  assumes "c \<in> carrier R"
  shows "monomial c n \<in> carrier (Fun R)"
  apply(rule function_ring_car_memI)
  unfolding monomial_function_def 
  apply (simp add: assms)
  by simp

definition ring_id  where
"ring_id \<equiv> restrict (\<lambda>x. x) (carrier R) "

lemma ring_id_closed[simp]:
"ring_id \<in> carrier (Fun R)"
  by (simp add: function_ring_car_memI ring_id_def)

lemma ring_id_eval:
  assumes "a \<in> carrier R"
  shows "ring_id a = a"
  using assms unfolding ring_id_def
  by simp
  
lemma constant_a_trans: 
  assumes "a \<in>carrier R"
  shows "m_translate a  = \<cc>\<^bsub>a\<^esub> \<otimes>\<^bsub>Fun R\<^esub> ring_id"
proof(rule function_ring_car_eqI)
   show "m_translate a \<in> carrier (Fun R)"
     using assms
     using m_translate_functions by blast
   show "\<cc>\<^bsub>a\<^esub> \<otimes>\<^bsub>Fun R\<^esub> ring_id \<in> carrier (Fun R)"
     unfolding ring_id_def 
     using assms ring_id_closed ring_id_def 
     by (simp add: constant_function_closed fun_mult_closed)      
  show "\<And>x. x \<in> carrier R \<Longrightarrow> m_translate a x = (\<cc>\<^bsub>a\<^esub> \<otimes>\<^bsub>Fun R\<^esub> ring_id) x"
    by (simp add: constant_function_closed assms constant_function_eq function_mult_eval_car m_translate_eq ring_id_eval)    
qed

text\<open>polynomials in one variable\<close>

fun polynomial :: "'a list \<Rightarrow> ('a \<Rightarrow> 'a)" where
"polynomial []  = \<zero>\<^bsub>Fun R\<^esub> "|
"polynomial (a#as) = (\<lambda>x \<in> carrier R. a \<oplus> x \<otimes> (polynomial as x))"

lemma polynomial_induct_lemma:
  assumes "f \<in> carrier (Fun R)"
  assumes "a \<in> carrier R"
  shows "(\<lambda>x \<in> carrier R. a \<oplus> x \<otimes> (f x)) \<in> carrier (Fun R)"
proof(rule function_ring_car_memI)
  show "\<And>aa. aa \<in> carrier R \<Longrightarrow> (\<lambda>x\<in>carrier R. a \<oplus> x \<otimes> f x) aa \<in> carrier R"
  proof- fix y assume A: "y \<in> carrier R"
    have "a \<oplus> y \<otimes> f y \<in> carrier R"
      using A assms(1) assms(2) function_ring_car_closed by blast
    thus "(\<lambda>x\<in>carrier R. a \<oplus> x \<otimes> f x) y \<in> carrier R"
      using A by auto 
  qed  
  show "\<And>aa. aa \<notin> carrier R \<Longrightarrow> (\<lambda>x\<in>carrier R. a \<oplus> x \<otimes> f x) aa = undefined"
    by auto 
qed

lemma polynomial_function: 
  shows "set as \<subseteq> carrier R \<Longrightarrow> polynomial as \<in> carrier (Fun R)"
proof(induction as)
  case Nil
  then show ?case 
    by (simp add: function_zero_closed)  
next
  case (Cons a as)
  then show "polynomial (a # as) \<in> carrier (function_ring (carrier R) R)"
    using polynomial.simps(2)[of a as] polynomial_induct_lemma[of "polynomial as" a]
    by simp
qed
  
lemma polynomial_constant:
  assumes "a \<in> carrier R"
  shows "polynomial [a] = \<cc>\<^bsub>a\<^esub>"
  apply(rule function_ring_car_eqI)
      using assms polynomial_function 
      apply (metis (full_types) list.distinct(1) list.set_cases set_ConsD subset_code(1))
        apply (simp add: constant_function_closed assms)
          using polynomial.simps(2)[of a "[]"] polynomial.simps(1) assms 
          by (simp add: constant_function_eq function_zero_eval)
          

end

    (**************************************************************************************************)
    (**************************************************************************************************)
    subsubsection\<open>Sequences Indexed by the Natural Numbers\<close>
    (**************************************************************************************************)
    (**************************************************************************************************)

definition nat_seqs ("_\<^bsup>\<omega>\<^esup>")where
"nat_seqs R \<equiv> function_ring (UNIV::nat set) R"
 
abbreviation(input) closed_seqs where
"closed_seqs R \<equiv> carrier (R\<^bsup>\<omega>\<^esup>)"

lemma closed_seqs_memI:
  assumes "\<And>k. s k \<in> carrier R"
  shows "s \<in> closed_seqs R"
  unfolding nat_seqs_def function_ring_def 
  by (simp add: PiE_UNIV_domain assms)

lemma closed_seqs_memE:
  assumes "s \<in> closed_seqs R"
  shows "s k \<in> carrier R"
  using assms unfolding nat_seqs_def function_ring_def 
  by (simp add: PiE_iff)  

definition is_constant_fun  where
"is_constant_fun R f = (\<exists>x \<in> carrier R. f = constant_function (carrier R) R x)"

definition is_constant_seq where
"is_constant_seq R s = (\<exists>x \<in> carrier R. s = constant_function (UNIV::nat set) x)"

lemma is_constant_seqI:
  fixes a
  assumes "s \<in> closed_seqs R"
  assumes "\<And>k. s k = a"
  shows "is_constant_seq R s"
  unfolding is_constant_seq_def constant_function_def 
  by (metis assms(1) assms(2) closed_seqs_memE restrict_UNIV restrict_ext)
   
lemma is_constant_seqE:
  assumes "is_constant_seq R s"
  assumes "s k = a"
  shows "s n = a"
  using assms unfolding is_constant_seq_def 
  by (metis constant_function_def restrict_UNIV)
  
lemma is_constant_seq_imp_closed:
  assumes "is_constant_seq R s"
  shows "s \<in> closed_seqs R"
  apply(rule closed_seqs_memI)
  using assms unfolding is_constant_seq_def constant_function_def 
  by auto
  
context U_function_ring
begin

text\<open>Sequence sums and products are closed\<close>

lemma seq_plus_closed:
  assumes "s \<in> closed_seqs R"
  assumes "s' \<in> closed_seqs R"
  shows "s \<oplus>\<^bsub>R\<^bsup>\<omega>\<^esup>\<^esub> s' \<in> closed_seqs R"
  by (metis assms(1) assms(2) nat_seqs_def ring_functions.fun_add_closed ring_functions_axioms)
 
lemma seq_mult_closed:
  assumes "s \<in> closed_seqs R"
  assumes "s' \<in> closed_seqs R"
  shows "s \<otimes>\<^bsub>R\<^bsup>\<omega>\<^esup>\<^esub> s' \<in> closed_seqs R"
  apply(rule closed_seqs_memI)
  by (metis assms(1) assms(2) closed_seqs_memE nat_seqs_def ring_functions.fun_mult_closed ring_functions_axioms)
 
lemma constant_function_comp_is_closed_seq:
  assumes "a \<in> carrier R"
  assumes "s \<in> closed_seqs R"
  shows "(const a \<circ> s) \<in> closed_seqs R" 
  by (simp add: constant_functionE assms(1) assms(2) closed_seqs_memE closed_seqs_memI)

lemma constant_function_comp_is_constant_seq:
  assumes "a \<in> carrier R"
  assumes "s \<in> closed_seqs R"
  shows "is_constant_seq R ((const a) \<circ> s)" 
  apply(rule is_constant_seqI[of _ _ a] )
  apply (simp add: assms(1) assms(2) constant_function_comp_is_closed_seq)
    using assms(1) assms(2) closed_seqs_memE 
    by (simp add: closed_seqs_memE constant_functionE)
      
lemma function_comp_is_closed_seq:
  assumes "s \<in> closed_seqs R"
  assumes "f \<in> carrier (Fun R)"
  shows "f \<circ> s \<in> closed_seqs R" 
  apply(rule closed_seqs_memI)
  using assms(1) assms(2) closed_seqs_memE 
  by (metis comp_apply fun_add_eval_closed fun_add_zeroR function_zero_closed)
  
lemma function_sum_comp_is_seq_sum:
  assumes "s \<in> closed_seqs R"
  assumes "f \<in> carrier (Fun R)"
  assumes "g \<in> carrier (Fun R)"
  shows "(f \<oplus>\<^bsub>Fun R\<^esub> g) \<circ> s = (f \<circ> s) \<oplus>\<^bsub>R\<^bsup>\<omega>\<^esup>\<^esub> (g \<circ> s)"
  apply(rule ring_functions.function_ring_car_eqI[of R _ "UNIV :: nat set"])
  apply (simp add: ring_functions_axioms)
    using function_comp_is_closed_seq 
    apply (metis assms(1) assms(2) assms(3) fun_add_closed nat_seqs_def)
     apply (metis assms(1) assms(2) assms(3) function_comp_is_closed_seq nat_seqs_def seq_plus_closed)
  by (smt UNIV_eq_I assms(1) assms(2) assms(3) closed_seqs_memE comp_apply function_comp_is_closed_seq nat_seqs_def ring_functions.fun_add_eval_car ring_functions_axioms)

lemma function_mult_comp_is_seq_mult:
  assumes "s \<in> closed_seqs R"
  assumes "f \<in> carrier (Fun R)"
  assumes "g \<in> carrier (Fun R)"
  shows "(f \<otimes>\<^bsub>Fun R\<^esub> g) \<circ> s = (f \<circ> s) \<otimes>\<^bsub>R\<^bsup>\<omega>\<^esup>\<^esub> (g \<circ> s)"
  apply(rule ring_functions.function_ring_car_eqI[of R _ "UNIV :: nat set"])
  apply (simp add: ring_functions_axioms)
  using function_comp_is_closed_seq 
  apply (metis assms(1) assms(2) assms(3) fun_mult_closed nat_seqs_def)
  apply (metis assms(1) assms(2) assms(3) function_comp_is_closed_seq nat_seqs_def seq_mult_closed)
  by (metis (no_types, lifting) assms(1) assms(2) assms(3) comp_apply function_comp_is_closed_seq nat_seqs_def ring_functions.function_mult_eval_car ring_functions.function_ring_car_closed ring_functions_axioms)

lemma seq_plus_simp:
  assumes "s \<in> closed_seqs R"
  assumes "t \<in> closed_seqs R"
  shows "(s \<oplus>\<^bsub>R\<^bsup>\<omega>\<^esup>\<^esub> t) k = s k \<oplus> t k"
  using assms unfolding nat_seqs_def 
  by (simp add: ring_functions.fun_add_eval_car ring_functions_axioms)

lemma seq_mult_simp:
  assumes "s \<in> closed_seqs R"
  assumes "t \<in> closed_seqs R"
  shows "(s \<otimes>\<^bsub>R\<^bsup>\<omega>\<^esup>\<^esub> t) k = s k \<otimes> t k"
  using assms unfolding nat_seqs_def 
  by (simp add: ring_functions.function_mult_eval_car ring_functions_axioms)

lemma seq_one_simp:
"\<one>\<^bsub>R\<^bsup>\<omega>\<^esup>\<^esub> k = \<one>"
  by (simp add: nat_seqs_def ring_functions.function_one_eval ring_functions_axioms)

lemma seq_zero_simp:
"\<zero>\<^bsub>R\<^bsup>\<omega>\<^esup>\<^esub> k = \<zero>"
  by (simp add: nat_seqs_def ring_functions.function_zero_eval ring_functions_axioms)

lemma(in U_function_ring) ring_id_seq_comp:
  assumes "s \<in> closed_seqs R"
  shows "ring_id \<circ> s = s"
  apply(rule ring_functions.function_ring_car_eqI[of R _ "UNIV::nat set"])
  using ring_functions_axioms apply auto[1]
  apply (metis assms function_comp_is_closed_seq nat_seqs_def ring_id_closed)  
  apply (metis assms nat_seqs_def)
  by (simp add: assms closed_seqs_memE ring_id_eval)
  
lemma(in U_function_ring) ring_seq_smult_closed:
  assumes "s \<in> closed_seqs R"
  assumes "a \<in> carrier R"
  shows "a \<odot>\<^bsub>R\<^bsup>\<omega>\<^esup>\<^esub> s \<in> closed_seqs R"
  apply(rule closed_seqs_memI) 
  by (metis assms(1) assms(2) closed_seqs_memE nat_seqs_def ring_functions.function_smult_closed ring_functions_axioms)

lemma(in U_function_ring) ring_seq_smult_eval:
  assumes "s \<in> closed_seqs R"
  assumes "a \<in> carrier R"
  shows "(a \<odot>\<^bsub>R\<^bsup>\<omega>\<^esup>\<^esub> s) k = a \<otimes> (s k)"
  by (metis UNIV_I assms(1) assms(2) nat_seqs_def ring_functions.function_smult_eval ring_functions_axioms)

lemma(in U_function_ring) ring_seq_smult_comp_assoc:
  assumes "s \<in> closed_seqs R"
  assumes "f \<in> carrier (Fun R)"
  assumes "a \<in> carrier R"
  shows "((a \<odot>\<^bsub>Fun R\<^esub> f) \<circ> s) = a \<odot>\<^bsub>R\<^bsup>\<omega>\<^esup>\<^esub> (f \<circ> s)"
  apply(rule ext)
  using function_smult_eval[of a f] ring_seq_smult_eval[of "f \<circ> s" a] 
  by (simp add: assms(1) assms(2) assms(3) closed_seqs_memE function_comp_is_closed_seq)
  
end 

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Extensional Maps Between the Carriers of two Structures\<close>
(**************************************************************************************************)
(**************************************************************************************************)

definition struct_maps :: "('a, 'c) partial_object_scheme \<Rightarrow> ('b, 'd) partial_object_scheme 
                              \<Rightarrow> ('a \<Rightarrow> 'b) set" where
"struct_maps T S = {f. (f \<in> (carrier T) \<rightarrow> (carrier S)) \<and> f = restrict f (carrier T) }"

definition to_struct_map where
"to_struct_map T f = restrict f (carrier T)"

lemma to_struct_map_closed:
  assumes "f \<in> (carrier T) \<rightarrow> (carrier S)"
  shows "to_struct_map T f \<in> (struct_maps T S)"
  by (smt PiE_restrict Pi_iff assms mem_Collect_eq restrict_PiE struct_maps_def to_struct_map_def)
  
lemma struct_maps_memI:
  assumes "\<And> x. x \<in> carrier T \<Longrightarrow> f x \<in> carrier S"
  assumes "\<And>x. x \<notin> carrier T \<Longrightarrow> f x = undefined"
  shows "f \<in> struct_maps T S"
proof-
  have 0: " (f \<in> (carrier T) \<rightarrow> (carrier S))" 
    using assms 
    by blast
  have 1: "f  = restrict f (carrier T)"
    using assms 
    by (simp add: extensional_def extensional_restrict)
  show ?thesis 
    using 0 1 
    unfolding struct_maps_def 
    by blast   
qed

lemma struct_maps_memE:
  assumes "f \<in> struct_maps T S"
  shows  "\<And> x. x \<in> carrier T \<Longrightarrow> f x \<in> carrier S"
         "\<And>x. x \<notin> carrier T \<Longrightarrow> f x = undefined"
  using assms unfolding struct_maps_def 
  apply blast
    using assms unfolding struct_maps_def 
    by (metis (mono_tags, lifting) mem_Collect_eq restrict_apply)

text\<open>An abbreviation for restricted composition of function of functions. This is necessary for the composition of two struct maps to again be a struct map.\<close>
abbreviation(input) rcomp 
  where "rcomp \<equiv> FuncSet.compose"

lemma struct_map_comp:
  assumes "g \<in> (struct_maps T S)"
  assumes "f \<in> (struct_maps S U)"
  shows "rcomp (carrier T) f g \<in> (struct_maps T U)"
proof(rule struct_maps_memI)
  show "\<And>x. x \<in> carrier T \<Longrightarrow> rcomp (carrier T) f g x \<in> carrier U"
    using assms struct_maps_memE(1) 
    by (metis compose_eq)    
  show " \<And>x. x \<notin> carrier T \<Longrightarrow> rcomp (carrier T) f g x = undefined"
    by (meson compose_extensional extensional_arb)
qed

lemma r_comp_is_compose:
  assumes "g \<in> (struct_maps T S)"
  assumes "f \<in> (struct_maps S U)"
  assumes "a \<in> (carrier T)"
  shows "(rcomp (carrier T) f g) a = (f \<circ> g) a"
  by (simp add: FuncSet.compose_def assms(3))

lemma r_comp_not_in_car:
  assumes "g \<in> (struct_maps T S)"
  assumes "f \<in> (struct_maps S U)"
  assumes "a \<notin> (carrier T)"
  shows "(rcomp (carrier T) f g) a = undefined"
  by (simp add: FuncSet.compose_def assms(3))

text\<open>The reverse composition of two struct maps:\<close>

definition pullback ::
    "('a, 'd) partial_object_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c)" where
"pullback T f g = rcomp (carrier T) g f"

lemma pullback_closed:
  assumes "f \<in> (struct_maps T S)"
  assumes "g \<in> (struct_maps S U)"
  shows "pullback T f g \<in> (struct_maps T U)"
  by (metis assms(1) assms(2) pullback_def struct_map_comp)

text\<open>Composition of struct maps which takes the structure itself rather than the carrier as a parameter:\<close>

definition pushforward :: 
    "('a, 'd) partial_object_scheme \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b)  \<Rightarrow> ('a \<Rightarrow> 'c)" where
"pushforward T f g \<equiv> rcomp (carrier T) f g"

lemma pushforward_closed:
  assumes "g \<in> (struct_maps T S)"
  assumes "f \<in> (struct_maps S U)"
  shows "pushforward T f g \<in> (struct_maps T U)"
  using assms(1) assms(2) struct_map_comp 
  by (metis pushforward_def)
  

end

