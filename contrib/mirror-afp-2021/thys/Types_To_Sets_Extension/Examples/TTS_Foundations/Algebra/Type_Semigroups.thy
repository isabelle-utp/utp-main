(* Title: Examples/TTS_Foundations/Algebra/Type_Semigroups.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Abstract semigroups on types\<close>
theory Type_Semigroups
  imports Main
begin



subsection\<open>Background\<close>

text\<open>The results presented in this section were ported 
(with amendments and additions) from the theory \<^text>\<open>Groups\<close> in the main 
library of Isabelle/HOL.\<close>



subsection\<open>Preliminaries\<close>

named_theorems tts_ac_simps "assoc. and comm. simplification rules"
  and tts_algebra_simps "algebra simplification rules"
  and tts_field_simps "algebra simplification rules for fields"



subsection\<open>Binary operations\<close>


text\<open>Abstract operation.\<close>

locale binary_op = 
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

locale binary_op_syntax = binary_op f for f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
begin

notation f (infixl \<open>\<oplus>\<^sub>a\<close> 65)

end


text\<open>Concrete syntax.\<close>

locale plus = binary_op plus for plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
begin

notation plus (infixl \<open>+\<^sub>a\<close> 65)

end

locale minus = binary_op minus for minus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
begin

notation minus (infixl \<open>-\<^sub>a\<close> 65)

end

locale times = binary_op times for times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
begin

notation times (infixl \<open>*\<^sub>a\<close> 70)

end

locale divide = binary_op divide for divide :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
begin

notation divide (infixl \<open>'/\<^sub>a\<close> 70)

end


text\<open>Pairs.\<close>

locale binary_op_pair = alg\<^sub>a: binary_op f\<^sub>a + alg\<^sub>b: binary_op f\<^sub>b
  for f\<^sub>a :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and f\<^sub>b :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"

locale binary_op_pair_syntax = binary_op_pair f\<^sub>a f\<^sub>b
  for f\<^sub>a :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and f\<^sub>b :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
begin

notation f\<^sub>a (infixl \<open>\<oplus>\<^sub>a\<close> 65)
notation f\<^sub>b (infixl \<open>\<oplus>\<^sub>b\<close> 65)

end



subsection\<open>Simple semigroups\<close>


subsubsection\<open>Definitions\<close>


text\<open>Abstract semigroups.\<close>

locale semigroup = binary_op f for f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" +
  assumes assoc[tts_ac_simps, tts_algebra_simps]: "f (f a b) c = f a (f b c)"

locale semigroup_syntax = binary_op_syntax f for f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"


text\<open>Concrete syntax.\<close>

locale semigroup_add = semigroup plus for plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
begin

sublocale plus plus .

end

locale semigroup_mult = semigroup times for times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
begin

sublocale times times .

end


text\<open>Pairs.\<close>

locale semigroup_pair = alg\<^sub>a: semigroup f\<^sub>a + alg\<^sub>b: semigroup f\<^sub>b 
  for f\<^sub>a :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and f\<^sub>b :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
begin

sublocale binary_op_pair f\<^sub>a f\<^sub>b .
sublocale rev: semigroup_pair f\<^sub>b f\<^sub>a ..

end

locale semigroup_pair_syntax = binary_op_pair_syntax



subsection\<open>Commutative semigroups\<close>


subsubsection\<open>Definitions\<close>


text\<open>Abstract commutative semigroup.\<close>

locale comm_semigroup = semigroup f for f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" +
  assumes commute[tts_ac_simps, tts_algebra_simps]: "f a b = f b a"

locale comm_semigroup_syntax = semigroup_syntax


text\<open>Concrete syntax.\<close>

locale comm_semigroup_add = comm_semigroup plus for plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
begin

sublocale semigroup_add plus ..

end

locale comm_semigroup_mult = comm_semigroup times for times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
begin

sublocale semigroup_mult times ..

end


text\<open>Pairs.\<close>

locale comm_semigroup_pair = alg\<^sub>a: comm_semigroup f\<^sub>a + alg\<^sub>b: comm_semigroup f\<^sub>b 
  for f\<^sub>a :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and f\<^sub>b :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
begin

sublocale semigroup_pair f\<^sub>a f\<^sub>b ..
sublocale rev: comm_semigroup_pair f\<^sub>b f\<^sub>a ..

end

locale comm_semigroup_pair_syntax = semigroup_pair_syntax



subsubsection\<open>Results\<close>

context comm_semigroup
begin

interpretation comm_semigroup_syntax f .

lemma left_commute[tts_ac_simps, tts_algebra_simps, field_simps]: 
  "b \<oplus>\<^sub>a (a \<oplus>\<^sub>a c) = a \<oplus>\<^sub>a (b \<oplus>\<^sub>a c)"
proof -
  have "(b \<oplus>\<^sub>a a) \<oplus>\<^sub>a c = (a \<oplus>\<^sub>a b) \<oplus>\<^sub>a c" by (simp add: commute)
  then show ?thesis by (simp only: assoc)
qed

end



subsection\<open>Cancellative semigroups\<close>


subsubsection\<open>Definitions\<close>


text\<open>Abstract cancellative semigroup.\<close>

locale cancel_semigroup = semigroup f for f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" +
  assumes add_left_imp_eq: "f a b = f a c \<Longrightarrow> b = c"
  assumes add_right_imp_eq: "f b a = f c a \<Longrightarrow> b = c"

locale cancel_semigroup_syntax = semigroup_syntax f for f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"


text\<open>Concrete syntax.\<close>

locale cancel_semigroup_add = cancel_semigroup plus 
  for plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
begin

sublocale semigroup_add plus ..

end

locale cancel_semigroup_mult = cancel_semigroup times 
  for times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
begin

sublocale semigroup_mult times ..

end


text\<open>Pairs.\<close>

locale cancel_semigroup_pair = 
  alg\<^sub>a: cancel_semigroup f\<^sub>a + alg\<^sub>b: cancel_semigroup f\<^sub>b 
  for f\<^sub>a :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and f\<^sub>b :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
begin

sublocale semigroup_pair f\<^sub>a f\<^sub>b ..
sublocale rev: cancel_semigroup_pair f\<^sub>b f\<^sub>a ..

end

locale cancel_semigroup_pair_syntax = semigroup_pair_syntax f\<^sub>a f\<^sub>b
  for f\<^sub>a :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and f\<^sub>b :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"


subsubsection\<open>Results\<close>

context cancel_semigroup
begin

interpretation cancel_semigroup_syntax f .

lemma add_left_cancel[simp]: "a \<oplus>\<^sub>a b = a \<oplus>\<^sub>a c \<longleftrightarrow> b = c"
  by (blast dest: add_left_imp_eq)

lemma add_right_cancel[simp]: "b \<oplus>\<^sub>a a = c \<oplus>\<^sub>a a \<longleftrightarrow> b = c"
  by (blast dest: add_right_imp_eq)

lemma inj_on_add[simp]: "inj_on ((\<oplus>\<^sub>a) a) A" by (rule inj_onI) simp

lemma inj_on_add'[simp]: "inj_on (\<lambda>b. b \<oplus>\<^sub>a a) A" by (rule inj_onI) simp

lemma bij_betw_add[simp]: "bij_betw ((\<oplus>\<^sub>a) a) A B \<longleftrightarrow> (\<oplus>\<^sub>a) a ` A = B"
  by (simp add: bij_betw_def)

end



subsection\<open>Cancellative commutative semigroups\<close>


subsubsection\<open>Definitions\<close>


text\<open>Abstract cancellative commutative semigroups.\<close>

locale cancel_comm_semigroup = comm: comm_semigroup f + binary_op fi 
  for f fi :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" +
  assumes add_diff_cancel_left'[simp]: "fi (f a b) a = b"
    and diff_diff_add[tts_algebra_simps, tts_field_simps]: 
    "fi (fi a b) c = fi a (f b c)"

locale cancel_comm_semigroup_syntax = comm_semigroup_syntax f + binary_op fi 
  for f fi :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
begin

notation fi (infixl \<open>\<ominus>\<^sub>a\<close> 65)

end


text\<open>Concrete syntax.\<close>

locale cancel_comm_semigroup_add = cancel_comm_semigroup plus minus 
  for plus minus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
begin

sublocale comm_semigroup_add plus ..
sublocale minus minus .

end

locale cancel_comm_semigroup_mult = cancel_comm_semigroup times divide 
  for times divide :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
begin

sublocale comm_semigroup_mult times ..
sublocale divide divide .

end


text\<open>Pairs.\<close>

locale cancel_comm_semigroup_pair = 
  alg\<^sub>a: cancel_comm_semigroup f\<^sub>a fi\<^sub>a + alg\<^sub>b: cancel_comm_semigroup f\<^sub>b fi\<^sub>b
  for f\<^sub>a fi\<^sub>a :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and f\<^sub>b fi\<^sub>b :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
begin

sublocale comm_semigroup_pair f\<^sub>a f\<^sub>b ..
sublocale rev: cancel_comm_semigroup_pair f\<^sub>b fi\<^sub>b f\<^sub>a fi\<^sub>a ..

end

locale cancel_comm_semigroup_pair_syntax = 
  comm_semigroup_pair_syntax f\<^sub>a f\<^sub>b + binary_op fi\<^sub>a + binary_op fi\<^sub>b
  for f\<^sub>a fi\<^sub>a f\<^sub>b fi\<^sub>b
begin

notation fi\<^sub>a (infixl \<open>\<ominus>\<^sub>a\<close> 65)
notation fi\<^sub>b (infixl \<open>\<ominus>\<^sub>b\<close> 65)

end


subsubsection\<open>Results\<close>

context cancel_comm_semigroup
begin

interpretation cancel_comm_semigroup_syntax .

lemma add_diff_cancel_right'[simp]: "(a \<oplus>\<^sub>a b) \<ominus>\<^sub>a b = a"
  using add_diff_cancel_left'[of b a] by (simp add: tts_ac_simps)

sublocale cancel: cancel_semigroup
proof
  fix a b c :: 'a
  assume "a \<oplus>\<^sub>a b = a \<oplus>\<^sub>a c"
  then have "a \<oplus>\<^sub>a b \<ominus>\<^sub>a a = a \<oplus>\<^sub>a c \<ominus>\<^sub>a a" by simp
  then show "b = c" by simp
next
  fix a b c :: 'a
  assume "b \<oplus>\<^sub>a a = c \<oplus>\<^sub>a a"
  then have "b \<oplus>\<^sub>a a \<ominus>\<^sub>a a = c \<oplus>\<^sub>a a \<ominus>\<^sub>a a" by simp
  then show "b = c" by simp
qed

lemmas cancel_semigroup_axioms = cancel.cancel_semigroup_axioms

lemma add_diff_cancel_left[simp]: "(c \<oplus>\<^sub>a a) \<ominus>\<^sub>a (c \<oplus>\<^sub>a b) = a \<ominus>\<^sub>a b"
  unfolding diff_diff_add[symmetric] by simp

lemma add_diff_cancel_right[simp]: "(a \<oplus>\<^sub>a c) \<ominus>\<^sub>a (b \<oplus>\<^sub>a c) = a \<ominus>\<^sub>a b"
  using add_diff_cancel_left[symmetric] by (simp add: tts_ac_simps)

lemma diff_right_commute: "a \<ominus>\<^sub>a c \<ominus>\<^sub>a b = a \<ominus>\<^sub>a b \<ominus>\<^sub>a c"
  by (simp add: diff_diff_add comm.commute)

end

context cancel_comm_semigroup_pair
begin

sublocale cancel: cancel_semigroup_pair ..

lemmas cancel_semigroup_pair_axioms = cancel.cancel_semigroup_pair_axioms

end

text\<open>\newpage\<close>

end