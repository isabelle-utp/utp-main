(* Title: Examples/TTS_Foundations/Algebra/Set_Semigroups.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Abstract semigroups on sets\<close>
theory Set_Semigroups
  imports 
    Type_Semigroups 
    FNDS_Auxiliary
    "../Foundations/FNDS_Lifting_Set_Ext"
begin



subsection\<open>Background\<close>

text\<open>The results presented in this section were ported 
(with amendments and additions) from the theory \<^text>\<open>Groups\<close> in the main 
library of Isabelle/HOL.\<close>



subsection\<open>Binary operations\<close>


text\<open>Abstract binary operation.\<close>

locale binary_op_base_ow = 
  fixes U :: "'a set" and f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

locale binary_op_ow = binary_op_base_ow U f for U :: "'a set" and f +
  assumes op_closed: "x \<in> U \<Longrightarrow> y \<in> U \<Longrightarrow> f x y \<in> U"

locale binary_op_syntax_ow = binary_op_base_ow U f for U :: "'a set" and f
begin

notation f (infixl \<open>\<oplus>\<^sub>a\<close> 70)

end


text\<open>Concrete syntax.\<close>

locale plus_ow = binary_op_ow U plus for U :: "'a set" and plus
begin

notation plus (infixl \<open>+\<^sub>a\<close> 65)

end

locale minus_ow = binary_op_ow U minus for U :: "'a set" and minus
begin

notation minus (infixl \<open>-\<^sub>a\<close> 65)

end

locale times_ow = binary_op_ow U times for U :: "'a set" and times
begin

notation times (infixl \<open>*\<^sub>a\<close> 70)

end

locale divide_ow = binary_op_ow U divide for U :: "'a set" and divide
begin

notation divide (infixl \<open>'/\<^sub>a\<close> 70)

end


text\<open>Pairs.\<close>

locale binary_op_base_pair_ow = 
  alg\<^sub>a: binary_op_base_ow U\<^sub>a f\<^sub>a + alg\<^sub>b: binary_op_base_ow U\<^sub>b f\<^sub>b
  for U\<^sub>a :: "'a set" and f\<^sub>a and U\<^sub>b :: "'b set" and f\<^sub>b

locale binary_op_pair_ow = alg\<^sub>a: binary_op_ow U\<^sub>a f\<^sub>a + alg\<^sub>b: binary_op_ow U\<^sub>b f\<^sub>b
  for U\<^sub>a :: "'a set" and f\<^sub>a and U\<^sub>b :: "'b set" and f\<^sub>b
begin

sublocale binary_op_base_pair_ow U\<^sub>a f\<^sub>a U\<^sub>b f\<^sub>b .
sublocale rev: binary_op_base_pair_ow U\<^sub>b f\<^sub>b U\<^sub>a f\<^sub>a .

end

locale binary_op_pair_syntax_ow = binary_op_base_pair_ow U\<^sub>a f\<^sub>a U\<^sub>b f\<^sub>b
  for U\<^sub>a :: "'a set" and f\<^sub>a and U\<^sub>b :: "'b set" and f\<^sub>b
begin

notation f\<^sub>a (infixl \<open>\<oplus>\<^sub>a\<close> 70)
notation f\<^sub>b (infixl \<open>\<oplus>\<^sub>b\<close> 70)

end


subsubsection\<open>Results\<close>

context binary_op_ow
begin

interpretation binary_op_syntax_ow .

lemma op_closed'[simp]: "\<forall>x\<in>U. \<forall>y\<in>U. x \<oplus>\<^sub>a y \<in> U" by (simp add: op_closed)

tts_register_sbts \<open>(\<oplus>\<^sub>a)\<close> | U by (rule tts_AA_A_transfer[OF op_closed])

end



subsection\<open>Simple semigroups\<close>


subsubsection\<open>Definitions\<close>


text\<open>Abstract semigroup.\<close>

locale semigroup_ow = binary_op_ow U f for U :: "'a set" and f +
  assumes assoc[tts_ac_simps]: 
    "\<lbrakk> a \<in> U; b \<in> U; c \<in> U \<rbrakk> \<Longrightarrow> f (f a b) c = f a (f b c)"

locale semigroup_syntax_ow = binary_op_syntax_ow U f for U :: "'a set" and f


text\<open>Concrete syntax.\<close>

locale semigroup_add_ow = semigroup_ow U plus for U :: "'a set" and plus
begin

sublocale plus_ow U plus ..

end

locale semigroup_mult_ow = semigroup_ow U times for U :: "'a set" and times
begin

sublocale times_ow U times ..

end


text\<open>Pairs.\<close>

locale semigroup_pair_ow = alg\<^sub>a: semigroup_ow U\<^sub>a f\<^sub>a + alg\<^sub>b: semigroup_ow U\<^sub>b f\<^sub>b 
  for U\<^sub>a :: "'a set" and f\<^sub>a and U\<^sub>b :: "'b set" and f\<^sub>b
begin

sublocale binary_op_pair_ow U\<^sub>a f\<^sub>a U\<^sub>b f\<^sub>b ..
sublocale rev: semigroup_pair_ow U\<^sub>b f\<^sub>b U\<^sub>a f\<^sub>a ..

end

locale semigroup_pair_syntax_ow = binary_op_pair_syntax_ow U\<^sub>a f\<^sub>a U\<^sub>b f\<^sub>b
  for U\<^sub>a :: "'a set" and f\<^sub>a and U\<^sub>b :: "'b set" and f\<^sub>b


subsubsection\<open>Transfer rules\<close>

lemma semigroup_ow[ud_with]: "semigroup = semigroup_ow UNIV"
  unfolding 
    semigroup_def semigroup_ow_def semigroup_ow_axioms_def binary_op_ow_def
  by simp

lemma semigroup_pair_ow[ud_with]: 
  "semigroup_pair = (\<lambda>f\<^sub>a f\<^sub>b. semigroup_pair_ow UNIV f\<^sub>a UNIV f\<^sub>b)"
  unfolding semigroup_pair_def semigroup_pair_ow_def ud_with by simp

context
  includes lifting_syntax
begin

lemma semigroup_ow_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(rel_set A ===> (A ===> A ===> A) ===> (=)) semigroup_ow semigroup_ow"
  by 
    (
      ow_locale_transfer locale_defs: 
        semigroup_ow_def semigroup_ow_axioms_def binary_op_ow_def
    )

lemma semigroup_pair_ow_transfer[transfer_rule]:
  assumes [transfer_rule]: 
    "bi_unique A" "right_total A" "bi_unique B" "right_total B"
  shows 
    "(
      rel_set A ===> (A ===> A ===> A) ===>  
      rel_set B ===> (B ===> B ===> B) ===> 
      (=)
    ) 
    semigroup_pair_ow semigroup_pair_ow"
  by (ow_locale_transfer locale_defs: semigroup_pair_ow_def)

end



subsection\<open>Commutative semigroups\<close>


subsubsection\<open>Definitions\<close>


text\<open>Abstract commutative semigroup.\<close>

locale comm_semigroup_ow = semigroup_ow U f for U :: "'a set" and f +
  assumes commute[tts_ac_simps]: "a \<in> U \<Longrightarrow> b \<in> U \<Longrightarrow> f a b = f b a"

locale comm_semigroup_syntax_ow = semigroup_syntax_ow U f 
  for U :: "'a set" and f


text\<open>Concrete syntax.\<close>

locale comm_semigroup_add_ow = comm_semigroup_ow U plus 
  for U :: "'a set" and plus
begin

sublocale semigroup_add_ow U plus ..

end

locale comm_semigroup_mult_ow = comm_semigroup_ow U times 
  for U :: "'a set" and times
begin

sublocale semigroup_mult_ow U times ..

end


text\<open>Pairs.\<close>

locale comm_semigroup_pair_ow = 
  alg\<^sub>a: comm_semigroup_ow U\<^sub>a f\<^sub>a + alg\<^sub>b: comm_semigroup_ow U\<^sub>b f\<^sub>b  
  for U\<^sub>a :: "'a set" and f\<^sub>a and U\<^sub>b :: "'b set" and f\<^sub>b
begin

sublocale semigroup_pair_ow U\<^sub>a f\<^sub>a U\<^sub>b f\<^sub>b ..
sublocale rev: comm_semigroup_pair_ow U\<^sub>b f\<^sub>b U\<^sub>a f\<^sub>a ..

end

locale comm_semigroup_pair_syntax_ow = semigroup_pair_syntax_ow U\<^sub>a f\<^sub>a U\<^sub>b f\<^sub>b
  for U\<^sub>a :: "'a set" and f\<^sub>a and U\<^sub>b :: "'b set" and f\<^sub>b


subsubsection\<open>Transfer rules\<close>

lemma comm_semigroup_ow[ud_with]: "comm_semigroup = comm_semigroup_ow UNIV"
  unfolding 
    comm_semigroup_def comm_semigroup_axioms_def
    comm_semigroup_ow_def comm_semigroup_ow_axioms_def 
    ud_with
  by simp

lemma comm_semigroup_pair_ow[ud_with]: 
  "comm_semigroup_pair = (\<lambda>f\<^sub>a f\<^sub>b. comm_semigroup_pair_ow UNIV f\<^sub>a UNIV f\<^sub>b)"
  unfolding comm_semigroup_pair_def comm_semigroup_pair_ow_def ud_with 
  by simp

context
  includes lifting_syntax
begin

lemma comm_semigroup_ow_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(rel_set A ===> (A ===> A ===> A) ===> (=)) 
      comm_semigroup_ow comm_semigroup_ow"
  by 
    (
      ow_locale_transfer locale_defs: 
        comm_semigroup_ow_def comm_semigroup_ow_axioms_def
    )

lemma comm_semigroup_pair_ow_transfer[transfer_rule]:
  assumes [transfer_rule]: 
    "bi_unique A" "right_total A" "bi_unique B" "right_total B"
  shows 
    "(
      rel_set A ===> (A ===> A ===> A) ===>  
      rel_set B ===> (B ===> B ===> B) ===> 
      (=)
    ) 
    comm_semigroup_pair_ow comm_semigroup_pair_ow"
  by (ow_locale_transfer locale_defs: comm_semigroup_pair_ow_def)

end


subsubsection\<open>Relativization\<close>

context comm_semigroup_ow
begin

interpretation comm_semigroup_syntax_ow .

tts_context
  tts: (?'a to U)
  substituting comm_semigroup_ow_axioms
  eliminating through auto
begin

tts_lemma left_commute:
  assumes "b \<in> U"
    and "a \<in> U"
    and "c \<in> U"
  shows "b \<oplus>\<^sub>a (a \<oplus>\<^sub>a c) = a \<oplus>\<^sub>a (b \<oplus>\<^sub>a c)"
    is comm_semigroup.left_commute.

end

end



subsection\<open>Cancellative semigroups\<close>


subsubsection\<open>Definitions\<close>


text\<open>Abstract cancellative semigroup.\<close>

locale cancel_semigroup_ow = semigroup_ow U f for U :: "'a set" and f +
  assumes add_left_imp_eq: 
    "\<lbrakk> a \<in> U; b \<in> U; c \<in> U; f a b = f a c \<rbrakk> \<Longrightarrow> b = c"
  assumes add_right_imp_eq: 
    "\<lbrakk> b \<in> U; a \<in> U; c \<in> U; f b a = f c a \<rbrakk> \<Longrightarrow> b = c"

locale cancel_semigroup_syntax_ow = semigroup_syntax_ow U f 
  for U :: "'a set" and f


text\<open>Concrete syntax.\<close>

locale cancel_semigroup_add_ow = cancel_semigroup_ow U plus 
  for U :: "'a set" and plus
begin

sublocale semigroup_add_ow U plus ..

end

locale cancel_semigroup_mult_ow = cancel_semigroup_ow U times 
  for U :: "'a set" and times
begin

sublocale semigroup_mult_ow U times ..

end


text\<open>Pairs.\<close>

locale cancel_semigroup_pair_ow = 
  alg\<^sub>a: cancel_semigroup_ow U\<^sub>a f\<^sub>a + alg\<^sub>b: cancel_semigroup_ow U\<^sub>b f\<^sub>b 
  for U\<^sub>a :: "'a set" and f\<^sub>a and U\<^sub>b :: "'b set" and f\<^sub>b
begin

sublocale semigroup_pair_ow U\<^sub>a f\<^sub>a U\<^sub>b f\<^sub>b ..
sublocale rev: cancel_semigroup_pair_ow U\<^sub>b f\<^sub>b U\<^sub>a f\<^sub>a ..

end

locale cancel_semigroup_pair_syntax_ow = semigroup_pair_syntax_ow U\<^sub>a f\<^sub>a U\<^sub>b f\<^sub>b
  for U\<^sub>a :: "'a set" and f\<^sub>a and U\<^sub>b :: "'b set" and f\<^sub>b


subsubsection\<open>Transfer rules\<close>

lemma cancel_semigroup_ow[ud_with]: 
  "cancel_semigroup = cancel_semigroup_ow UNIV"
  unfolding 
    cancel_semigroup_def cancel_semigroup_axioms_def
    cancel_semigroup_ow_def cancel_semigroup_ow_axioms_def 
    ud_with
  by simp

lemma cancel_semigroup_pair_ow[ud_with]: 
  "cancel_semigroup_pair = (\<lambda>f\<^sub>a f\<^sub>b. cancel_semigroup_pair_ow UNIV f\<^sub>a UNIV f\<^sub>b)"
  unfolding cancel_semigroup_pair_def cancel_semigroup_pair_ow_def ud_with 
  by simp

context
  includes lifting_syntax
begin

lemma cancel_semigroup_ow_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(rel_set A ===> (A ===> A ===> A) ===> (=)) 
      cancel_semigroup_ow cancel_semigroup_ow"
  by 
    (
      ow_locale_transfer locale_defs: 
        cancel_semigroup_ow_def cancel_semigroup_ow_axioms_def
    )

lemma cancel_semigroup_pair_ow_transfer[transfer_rule]:
  assumes [transfer_rule]: 
    "bi_unique A" "right_total A" "bi_unique B" "right_total B"
  shows 
    "(
      rel_set A ===> (A ===> A ===> A) ===>  
      rel_set B ===> (B ===> B ===> B) ===> 
      (=)
    ) cancel_semigroup_pair_ow cancel_semigroup_pair_ow"
  by (ow_locale_transfer locale_defs: cancel_semigroup_pair_ow_def)

end


subsubsection\<open>Relativization\<close>

context cancel_semigroup_ow
begin

interpretation cancel_semigroup_syntax_ow .

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting cancel_semigroup_ow_axioms
  eliminating through auto
begin

tts_lemma add_right_cancel:
  assumes "b \<in> U" and "a \<in> U" and "c \<in> U"
  shows "(b \<oplus>\<^sub>a a = c \<oplus>\<^sub>a a) = (b = c)"
    is cancel_semigroup.add_right_cancel.

tts_lemma add_left_cancel:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U"
  shows "(a \<oplus>\<^sub>a b = a \<oplus>\<^sub>a c) = (b = c)"
    is cancel_semigroup.add_left_cancel.    
  
tts_lemma inj_on_add':
  assumes "a \<in> U" and "A \<subseteq> U"
  shows "inj_on (\<lambda>b. b \<oplus>\<^sub>a a) A"
    is cancel_semigroup.inj_on_add'.

tts_lemma inj_on_add:
  assumes "a \<in> U" and "A \<subseteq> U"
  shows "inj_on ((\<oplus>\<^sub>a) a) A"
    is cancel_semigroup.inj_on_add.

tts_lemma bij_betw_add:
  assumes "a \<in> U" and "A \<subseteq> U" and "B \<subseteq> U"
  shows "bij_betw ((\<oplus>\<^sub>a) a) A B = ((\<oplus>\<^sub>a) a ` A = B)"
    is cancel_semigroup.bij_betw_add.

end

end



subsection\<open>Cancellative commutative semigroups\<close>


subsubsection\<open>Definitions\<close>


text\<open>Abstract cancellative commutative semigroups.\<close>

locale cancel_comm_semigroup_ow = comm_semigroup_ow U f + binary_op_ow U fi 
  for U :: "'a set" and f fi +
  assumes add_diff_cancel_left'[simp]: "\<lbrakk> a \<in> U; b \<in> U \<rbrakk> \<Longrightarrow> fi (f a b) a = b"
    and diff_diff_add[tts_algebra_simps, tts_field_simps]: 
    "\<lbrakk> a \<in> U; b \<in> U; c \<in> U \<rbrakk> \<Longrightarrow> fi (fi a b) c = fi a (f b c)"

locale cancel_comm_semigroup_syntax_ow = 
  comm_semigroup_syntax_ow U f + binary_op_base_ow U fi 
  for U :: "'a set" and f fi 
begin

notation fi (infixl \<open>\<ominus>\<^sub>a\<close> 65)

end


text\<open>Concrete syntax.\<close>

locale cancel_comm_semigroup_add_ow = cancel_comm_semigroup_ow U plus minus 
  for U :: "'a set" and plus minus
begin

sublocale comm_semigroup_add_ow U plus ..
sublocale minus_ow U minus ..

end

locale cancel_comm_semigroup_mult = cancel_comm_semigroup_ow U times divide 
  for U :: "'a set" and times divide
begin

sublocale comm_semigroup_mult_ow U times ..
sublocale divide_ow U divide ..

end


text\<open>Pairs.\<close>

locale cancel_comm_semigroup_pair_ow = 
  alg\<^sub>a: cancel_comm_semigroup_ow U\<^sub>a f\<^sub>a fi\<^sub>a + 
  alg\<^sub>b: cancel_comm_semigroup_ow U\<^sub>b f\<^sub>b fi\<^sub>b
  for U\<^sub>a :: "'a set" and f\<^sub>a fi\<^sub>a and U\<^sub>b :: "'b set" and f\<^sub>b fi\<^sub>b
begin

sublocale comm_semigroup_pair_ow U\<^sub>a f\<^sub>a U\<^sub>b f\<^sub>b ..
sublocale rev: cancel_comm_semigroup_pair_ow U\<^sub>b f\<^sub>b fi\<^sub>b U\<^sub>a f\<^sub>a fi\<^sub>a ..

end

locale cancel_comm_semigroup_pair_syntax_ow = 
  comm_semigroup_pair_syntax_ow U\<^sub>a f\<^sub>a U\<^sub>b f\<^sub>b + 
  binary_op_ow U\<^sub>a fi\<^sub>a + 
  binary_op_ow U\<^sub>b fi\<^sub>b
  for U\<^sub>a :: "'a set" and f\<^sub>a fi\<^sub>a and U\<^sub>b :: "'b set" and f\<^sub>b fi\<^sub>b
begin

notation fi\<^sub>a (infixl \<open>\<ominus>\<^sub>a\<close> 65)
notation fi\<^sub>b (infixl \<open>\<ominus>\<^sub>b\<close> 65)

end


subsubsection\<open>Transfer rules\<close>

lemma cancel_comm_semigroup_ow[ud_with]: 
  "cancel_comm_semigroup = cancel_comm_semigroup_ow UNIV"
  unfolding 
    cancel_comm_semigroup_def cancel_comm_semigroup_axioms_def
    cancel_comm_semigroup_ow_def cancel_comm_semigroup_ow_axioms_def 
    binary_op_ow_def
    ud_with
  by simp

lemma cancel_comm_semigroup_pair_ow[ud_with]: 
  "cancel_comm_semigroup_pair = 
    (\<lambda>f\<^sub>a fi\<^sub>a f\<^sub>b fi\<^sub>b. cancel_comm_semigroup_pair_ow UNIV f\<^sub>a fi\<^sub>a UNIV f\<^sub>b fi\<^sub>b)"
  unfolding 
    cancel_comm_semigroup_pair_def cancel_comm_semigroup_pair_ow_def ud_with 
  by simp

context
  includes lifting_syntax
begin

lemma cancel_comm_semigroup_ow_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(rel_set A ===> (A ===> A ===> A) ===> (A ===> A ===> A) ===> (=)) 
      cancel_comm_semigroup_ow cancel_comm_semigroup_ow"
  by 
    (
      ow_locale_transfer locale_defs: 
        cancel_comm_semigroup_ow_def 
        cancel_comm_semigroup_ow_axioms_def
        binary_op_ow_def
    )

lemma cancel_comm_semigroup_pair_ow_transfer[transfer_rule]:
  assumes [transfer_rule]: 
    "bi_unique A" "right_total A" "bi_unique B" "right_total B"
  shows 
    "(
      rel_set A ===> (A ===> A ===> A) ===> (A ===> A ===> A) ===>  
      rel_set B ===> (B ===> B ===> B) ===> (B ===> B ===> B) ===> 
      (=)
    ) cancel_comm_semigroup_pair_ow cancel_comm_semigroup_pair_ow"
  by (ow_locale_transfer locale_defs: cancel_comm_semigroup_pair_ow_def)

end


subsubsection\<open>Relativization\<close>

context cancel_comm_semigroup_ow
begin

interpretation cancel_comm_semigroup_syntax_ow .

tts_context
  tts: (?'a to U)
  sbterms: (\<open>?f::?'a \<Rightarrow> ?'a \<Rightarrow> ?'a\<close> to f)
    and (\<open>?fi::?'a \<Rightarrow> ?'a \<Rightarrow> ?'a\<close> to fi)
  rewriting ctr_simps
  substituting cancel_comm_semigroup_ow_axioms
  eliminating through auto
begin

tts_lemma add_diff_cancel_right':
  assumes "a \<in> U" and "b \<in> U"
  shows "a \<oplus>\<^sub>a b \<ominus>\<^sub>a b = a"
    is cancel_comm_semigroup.add_diff_cancel_right'.
    
tts_lemma add_diff_cancel_right:
  assumes "a \<in> U" and "c \<in> U" and "b \<in> U"
  shows "a \<oplus>\<^sub>a c \<ominus>\<^sub>a b \<oplus>\<^sub>a c = a \<ominus>\<^sub>a b"
    is cancel_comm_semigroup.add_diff_cancel_right.

tts_lemma add_diff_cancel_left:
  assumes "c \<in> U" and "a \<in> U" and "b \<in> U"
  shows "c \<oplus>\<^sub>a a \<ominus>\<^sub>a c \<oplus>\<^sub>a b = a \<ominus>\<^sub>a b"
    is cancel_comm_semigroup.add_diff_cancel_left.

tts_lemma diff_right_commute:
  assumes "a \<in> U" and "c \<in> U" and "b \<in> U"
  shows "a \<ominus>\<^sub>a c \<ominus>\<^sub>a b = a \<ominus>\<^sub>a b \<ominus>\<^sub>a c"
    is cancel_comm_semigroup.diff_right_commute.

tts_lemma cancel_semigroup_axioms:
  assumes "U \<noteq> {}"
  shows "cancel_semigroup_ow U (\<oplus>\<^sub>a)"
    is cancel_comm_semigroup.cancel_semigroup_axioms.

end

sublocale cancel_semigroup_ow
  using 
    cancel_semigroup_axioms 
    cancel_semigroup_ow.intro 
    cancel_semigroup_ow_axioms_def 
    semigroup_ow_axioms 
  by auto

end

context cancel_comm_semigroup_pair_ow
begin

sublocale cancel_semigroup_pair_ow ..

end

text\<open>\newpage\<close>

end