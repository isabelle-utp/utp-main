(*  Title:      Uint16.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter \<open>Unsigned words of 16 bits\<close>

theory Uint16 imports
  Code_Target_Word_Base
begin

text \<open>
  Restriction for ML code generation:
  This theory assumes that the ML system provides a Word16
  implementation (mlton does, but PolyML 5.5 does not).
  Therefore, the code setup lives in the target \<open>SML_word\<close>
  rather than \<open>SML\<close>.  This ensures that code generation still
  works as long as \<open>uint16\<close> is not involved.
  For the target \<open>SML\<close> itself, no special code generation 
  for this type is set up. Nevertheless, it should work by emulation via @{typ "16 word"} 
  if the theory \<open>Code_Target_Bits_Int\<close> is imported.

  Restriction for OCaml code generation:
  OCaml does not provide an int16 type, so no special code generation 
  for this type is set up.
\<close>

declare prod.Quotient[transfer_rule]

section \<open>Type definition and primitive operations\<close>

typedef uint16 = "UNIV :: 16 word set" ..

setup_lifting type_definition_uint16

text \<open>Use an abstract type for code generation to disable pattern matching on @{term Abs_uint16}.\<close>
declare Rep_uint16_inverse[code abstype]

declare Quotient_uint16[transfer_rule]

instantiation uint16 :: comm_ring_1
begin
lift_definition zero_uint16 :: uint16 is "0 :: 16 word" .
lift_definition one_uint16 :: uint16 is "1" .
lift_definition plus_uint16 :: "uint16 \<Rightarrow> uint16 \<Rightarrow> uint16" is "(+) :: 16 word \<Rightarrow> _" .
lift_definition minus_uint16 :: "uint16 \<Rightarrow> uint16 \<Rightarrow> uint16" is "(-)" .
lift_definition uminus_uint16 :: "uint16 \<Rightarrow> uint16" is uminus .
lift_definition times_uint16 :: "uint16 \<Rightarrow> uint16 \<Rightarrow> uint16" is "(*)" .
instance by (standard; transfer) (simp_all add: algebra_simps)
end

instantiation uint16 :: semiring_modulo
begin
lift_definition divide_uint16 :: "uint16 \<Rightarrow> uint16 \<Rightarrow> uint16" is "(div)" .
lift_definition modulo_uint16 :: "uint16 \<Rightarrow> uint16 \<Rightarrow> uint16" is "(mod)" .
instance by (standard; transfer) (fact word_mod_div_equality)
end

instantiation uint16 :: linorder begin
lift_definition less_uint16 :: "uint16 \<Rightarrow> uint16 \<Rightarrow> bool" is "(<)" .
lift_definition less_eq_uint16 :: "uint16 \<Rightarrow> uint16 \<Rightarrow> bool" is "(\<le>)" .
instance by (standard; transfer) (simp_all add: less_le_not_le linear)
end

lemmas [code] = less_uint16.rep_eq less_eq_uint16.rep_eq

context
  includes lifting_syntax
  notes
    transfer_rule_of_bool [transfer_rule]
    transfer_rule_numeral [transfer_rule]
begin

lemma [transfer_rule]:
  "((=) ===> cr_uint16) of_bool of_bool"
  by transfer_prover

lemma transfer_rule_numeral_uint [transfer_rule]:
  "((=) ===> cr_uint16) numeral numeral"
  by transfer_prover

lemma [transfer_rule]:
  \<open>(cr_uint16 ===> (\<longleftrightarrow>)) even ((dvd) 2 :: uint16 \<Rightarrow> bool)\<close>
  by (unfold dvd_def) transfer_prover

end

instantiation uint16 :: semiring_bits
begin

lift_definition bit_uint16 :: \<open>uint16 \<Rightarrow> nat \<Rightarrow> bool\<close> is bit .

instance
  by (standard; transfer)
    (fact bit_iff_odd even_iff_mod_2_eq_zero odd_iff_mod_2_eq_one odd_one bits_induct
       bits_div_0 bits_div_by_1 bits_mod_div_trivial even_succ_div_2
       even_mask_div_iff exp_div_exp_eq div_exp_eq mod_exp_eq mult_exp_mod_exp_eq
       div_exp_mod_exp_eq even_mult_exp_div_exp_iff)+

end

instantiation uint16 :: semiring_bit_shifts
begin
lift_definition push_bit_uint16 :: \<open>nat \<Rightarrow> uint16 \<Rightarrow> uint16\<close> is push_bit .
lift_definition drop_bit_uint16 :: \<open>nat \<Rightarrow> uint16 \<Rightarrow> uint16\<close> is drop_bit .
lift_definition take_bit_uint16 :: \<open>nat \<Rightarrow> uint16 \<Rightarrow> uint16\<close> is take_bit .
instance by (standard; transfer)
  (fact push_bit_eq_mult drop_bit_eq_div take_bit_eq_mod)+
end

instantiation uint16 :: ring_bit_operations
begin
lift_definition not_uint16 :: \<open>uint16 \<Rightarrow> uint16\<close> is NOT .
lift_definition and_uint16 :: \<open>uint16 \<Rightarrow> uint16 \<Rightarrow> uint16\<close> is \<open>(AND)\<close> .
lift_definition or_uint16 :: \<open>uint16 \<Rightarrow> uint16 \<Rightarrow> uint16\<close> is \<open>(OR)\<close> .
lift_definition xor_uint16 :: \<open>uint16 \<Rightarrow> uint16 \<Rightarrow> uint16\<close> is \<open>(XOR)\<close> .
lift_definition mask_uint16 :: \<open>nat \<Rightarrow> uint16\<close> is mask .
instance by (standard; transfer)
  (simp_all add: bit_and_iff bit_or_iff bit_xor_iff bit_not_iff minus_eq_not_minus_1 mask_eq_decr_exp)
end

lemma [code]:
  \<open>take_bit n a = a AND mask n\<close> for a :: uint16
  by (fact take_bit_eq_mask)

lemma [code]:
  \<open>mask (Suc n) = push_bit n (1 :: uint16) OR mask n\<close>
  \<open>mask 0 = (0 :: uint16)\<close>
  by (simp_all add: mask_Suc_exp push_bit_of_1)

instance uint16 :: semiring_bit_syntax ..

context
  includes lifting_syntax
begin

lemma test_bit_uint16_transfer [transfer_rule]:
  \<open>(cr_uint16 ===> (=)) bit (!!)\<close>
  unfolding test_bit_eq_bit by transfer_prover

lemma shiftl_uint16_transfer [transfer_rule]:
  \<open>(cr_uint16 ===> (=) ===> cr_uint16) (\<lambda>k n. push_bit n k) (<<)\<close>
  unfolding shiftl_eq_push_bit by transfer_prover

lemma shiftr_uint16_transfer [transfer_rule]:
  \<open>(cr_uint16 ===> (=) ===> cr_uint16) (\<lambda>k n. drop_bit n k) (>>)\<close>
  unfolding shiftr_eq_drop_bit by transfer_prover

end

instantiation uint16 :: lsb
begin
lift_definition lsb_uint16 :: \<open>uint16 \<Rightarrow> bool\<close> is lsb .
instance by (standard; transfer)
  (fact lsb_odd)
end

instantiation uint16 :: msb
begin
lift_definition msb_uint16 :: \<open>uint16 \<Rightarrow> bool\<close> is msb .
instance ..
end

instantiation uint16 :: set_bit
begin
lift_definition set_bit_uint16 :: \<open>uint16 \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> uint16\<close> is set_bit .
instance
  apply standard
  apply transfer
  apply (simp add: bit_simps)
  done
end

instantiation uint16 :: bit_comprehension begin
lift_definition set_bits_uint16 :: "(nat \<Rightarrow> bool) \<Rightarrow> uint16" is "set_bits" .
instance by (standard; transfer) (fact set_bits_bit_eq)
end

lemmas [code] = bit_uint16.rep_eq lsb_uint16.rep_eq msb_uint16.rep_eq

instantiation uint16 :: equal begin
lift_definition equal_uint16 :: "uint16 \<Rightarrow> uint16 \<Rightarrow> bool" is "equal_class.equal" .
instance by standard (transfer, simp add: equal_eq)
end

lemmas [code] = equal_uint16.rep_eq

instantiation uint16 :: size begin
lift_definition size_uint16 :: "uint16 \<Rightarrow> nat" is "size" .
instance ..
end

lemmas [code] = size_uint16.rep_eq

lift_definition sshiftr_uint16 :: "uint16 \<Rightarrow> nat \<Rightarrow> uint16" (infixl ">>>" 55) is \<open>\<lambda>w n. signed_drop_bit n w\<close> .

lift_definition uint16_of_int :: "int \<Rightarrow> uint16" is "word_of_int" .

definition uint16_of_nat :: "nat \<Rightarrow> uint16"
where "uint16_of_nat = uint16_of_int \<circ> int"

lift_definition int_of_uint16 :: "uint16 \<Rightarrow> int" is "uint" .
lift_definition nat_of_uint16 :: "uint16 \<Rightarrow> nat" is "unat" .

definition integer_of_uint16 :: "uint16 \<Rightarrow> integer"
where "integer_of_uint16 = integer_of_int o int_of_uint16"

text \<open>Use pretty numerals from integer for pretty printing\<close>

context includes integer.lifting begin

lift_definition Uint16 :: "integer \<Rightarrow> uint16" is "word_of_int" .

lemma Rep_uint16_numeral [simp]: "Rep_uint16 (numeral n) = numeral n"
by(induction n)(simp_all add: one_uint16_def Abs_uint16_inverse numeral.simps plus_uint16_def)

lemma Rep_uint16_neg_numeral [simp]: "Rep_uint16 (- numeral n) = - numeral n"
by(simp only: uminus_uint16_def)(simp add: Abs_uint16_inverse)

lemma numeral_uint16_transfer [transfer_rule]:
  "(rel_fun (=) cr_uint16) numeral numeral"
by(auto simp add: cr_uint16_def)

lemma numeral_uint16 [code_unfold]: "numeral n = Uint16 (numeral n)"
by transfer simp

lemma neg_numeral_uint16 [code_unfold]: "- numeral n = Uint16 (- numeral n)"
by transfer(simp add: cr_uint16_def)

end

lemma Abs_uint16_numeral [code_post]: "Abs_uint16 (numeral n) = numeral n"
by(induction n)(simp_all add: one_uint16_def numeral.simps plus_uint16_def Abs_uint16_inverse)

lemma Abs_uint16_0 [code_post]: "Abs_uint16 0 = 0"
by(simp add: zero_uint16_def)

lemma Abs_uint16_1 [code_post]: "Abs_uint16 1 = 1"
by(simp add: one_uint16_def)

section \<open>Code setup\<close>

code_printing code_module Uint16 \<rightharpoonup> (SML_word)
\<open>(* Test that words can handle numbers between 0 and 15 *)
val _ = if 4 <= Word.wordSize then () else raise (Fail ("wordSize less than 4"));

structure Uint16 : sig
  val set_bit : Word16.word -> IntInf.int -> bool -> Word16.word
  val shiftl : Word16.word -> IntInf.int -> Word16.word
  val shiftr : Word16.word -> IntInf.int -> Word16.word
  val shiftr_signed : Word16.word -> IntInf.int -> Word16.word
  val test_bit : Word16.word -> IntInf.int -> bool
end = struct

fun set_bit x n b =
  let val mask = Word16.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))
  in if b then Word16.orb (x, mask)
     else Word16.andb (x, Word16.notb mask)
  end

fun shiftl x n =
  Word16.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word16.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word16.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word16.andb (x, Word16.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word16.fromInt 0

end; (* struct Uint16 *)\<close>
code_reserved SML_word Uint16

code_printing code_module Uint16 \<rightharpoonup> (Haskell)
 \<open>module Uint16(Int16, Word16) where

  import Data.Int(Int16)
  import Data.Word(Word16)\<close>
code_reserved Haskell Uint16

text \<open>Scala provides unsigned 16-bit numbers as Char.\<close>

code_printing code_module Uint16 \<rightharpoonup> (Scala)
\<open>object Uint16 {

def set_bit(x: scala.Char, n: BigInt, b: Boolean) : scala.Char =
  if (b)
    (x | (1.toChar << n.intValue)).toChar
  else
    (x & (1.toChar << n.intValue).unary_~).toChar

def shiftl(x: scala.Char, n: BigInt) : scala.Char = (x << n.intValue).toChar

def shiftr(x: scala.Char, n: BigInt) : scala.Char = (x >>> n.intValue).toChar

def shiftr_signed(x: scala.Char, n: BigInt) : scala.Char = (x.toShort >> n.intValue).toChar

def test_bit(x: scala.Char, n: BigInt) : Boolean = (x & (1.toChar << n.intValue)) != 0

} /* object Uint16 */\<close>
code_reserved Scala Uint16

text \<open>
  Avoid @{term Abs_uint16} in generated code, use @{term Rep_uint16'} instead. 
  The symbolic implementations for code\_simp use @{term Rep_uint16}.

  The new destructor @{term Rep_uint16'} is executable.
  As the simplifier is given the [code abstract] equations literally, 
  we cannot implement @{term Rep_uint16} directly, because that makes code\_simp loop.

  If code generation raises Match, some equation probably contains @{term Rep_uint16} 
  ([code abstract] equations for @{typ uint16} may use @{term Rep_uint16} because
  these instances will be folded away.)

  To convert @{typ "16 word"} values into @{typ uint16}, use @{term "Abs_uint16'"}.
\<close>

definition Rep_uint16' where [simp]: "Rep_uint16' = Rep_uint16"

lemma Rep_uint16'_transfer [transfer_rule]:
  "rel_fun cr_uint16 (=) (\<lambda>x. x) Rep_uint16'"
unfolding Rep_uint16'_def by(rule uint16.rep_transfer)

lemma Rep_uint16'_code [code]: "Rep_uint16' x = (BITS n. bit x n)"
  by transfer (simp add: set_bits_bit_eq)

lift_definition Abs_uint16' :: "16 word \<Rightarrow> uint16" is "\<lambda>x :: 16 word. x" .

lemma Abs_uint16'_code [code]:
  "Abs_uint16' x = Uint16 (integer_of_int (uint x))"
including integer.lifting by transfer simp

declare [[code drop: "term_of_class.term_of :: uint16 \<Rightarrow> _"]]

lemma term_of_uint16_code [code]:
  defines "TR \<equiv> typerep.Typerep" and "bit0 \<equiv> STR ''Numeral_Type.bit0''" shows
  "term_of_class.term_of x = 
   Code_Evaluation.App (Code_Evaluation.Const (STR ''Uint16.uint16.Abs_uint16'') (TR (STR ''fun'') [TR (STR ''Word.word'') [TR bit0 [TR bit0 [TR bit0 [TR bit0 [TR (STR ''Numeral_Type.num1'') []]]]]], TR (STR ''Uint16.uint16'') []]))
       (term_of_class.term_of (Rep_uint16' x))"
by(simp add: term_of_anything)

lemma Uin16_code [code abstract]: "Rep_uint16 (Uint16 i) = word_of_int (int_of_integer_symbolic i)"
unfolding Uint16_def int_of_integer_symbolic_def by(simp add: Abs_uint16_inverse)

code_printing
  type_constructor uint16 \<rightharpoonup>
  (SML_word) "Word16.word" and
  (Haskell) "Uint16.Word16" and
  (Scala) "scala.Char"
| constant Uint16 \<rightharpoonup>
  (SML_word) "Word16.fromLargeInt (IntInf.toLarge _)" and
  (Haskell) "(Prelude.fromInteger _ :: Uint16.Word16)" and
  (Haskell_Quickcheck) "(Prelude.fromInteger (Prelude.toInteger _) :: Uint16.Word16)" and
  (Scala) "_.charValue"
| constant "0 :: uint16" \<rightharpoonup>
  (SML_word) "(Word16.fromInt 0)" and
  (Haskell) "(0 :: Uint16.Word16)" and
  (Scala) "0"
| constant "1 :: uint16" \<rightharpoonup>
  (SML_word) "(Word16.fromInt 1)" and
  (Haskell) "(1 :: Uint16.Word16)" and
  (Scala) "1"
| constant "plus :: uint16 \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
  (SML_word) "Word16.+ ((_), (_))" and
  (Haskell) infixl 6 "+" and
  (Scala) "(_ +/ _).toChar"
| constant "uminus :: uint16 \<Rightarrow> _" \<rightharpoonup>
  (SML_word) "Word16.~" and
  (Haskell) "negate" and
  (Scala) "(- _).toChar"
| constant "minus :: uint16 \<Rightarrow> _" \<rightharpoonup>
  (SML_word) "Word16.- ((_), (_))" and
  (Haskell) infixl 6 "-" and
  (Scala) "(_ -/ _).toChar"
| constant "times :: uint16 \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
  (SML_word) "Word16.* ((_), (_))" and
  (Haskell) infixl 7 "*" and
  (Scala) "(_ */ _).toChar"
| constant "HOL.equal :: uint16 \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
  (SML_word) "!((_ : Word16.word) = _)" and
  (Haskell) infix 4 "==" and
  (Scala) infixl 5 "=="
| class_instance uint16 :: equal \<rightharpoonup> (Haskell) -
| constant "less_eq :: uint16 \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
  (SML_word) "Word16.<= ((_), (_))" and
  (Haskell) infix 4 "<=" and
  (Scala) infixl 4 "<="
| constant "less :: uint16 \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
  (SML_word) "Word16.< ((_), (_))" and
  (Haskell) infix 4 "<" and
  (Scala) infixl 4 "<"
| constant "NOT :: uint16 \<Rightarrow> _" \<rightharpoonup>
  (SML_word) "Word16.notb" and
  (Haskell) "Data'_Bits.complement" and
  (Scala) "_.unary'_~.toChar"
| constant "(AND) :: uint16 \<Rightarrow> _" \<rightharpoonup>
  (SML_word) "Word16.andb ((_),/ (_))" and
  (Haskell) infixl 7 "Data_Bits..&." and
  (Scala) "(_ & _).toChar"
| constant "(OR) :: uint16 \<Rightarrow> _" \<rightharpoonup>
  (SML_word) "Word16.orb ((_),/ (_))" and
  (Haskell) infixl 5 "Data_Bits..|." and
  (Scala) "(_ | _).toChar"
| constant "(XOR) :: uint16 \<Rightarrow> _" \<rightharpoonup>
  (SML_word) "Word16.xorb ((_),/ (_))" and
  (Haskell) "Data'_Bits.xor" and
  (Scala) "(_ ^ _).toChar"

definition uint16_div :: "uint16 \<Rightarrow> uint16 \<Rightarrow> uint16" 
where "uint16_div x y = (if y = 0 then undefined ((div) :: uint16 \<Rightarrow> _) x (0 :: uint16) else x div y)"

definition uint16_mod :: "uint16 \<Rightarrow> uint16 \<Rightarrow> uint16" 
where "uint16_mod x y = (if y = 0 then undefined ((mod) :: uint16 \<Rightarrow> _) x (0 :: uint16) else x mod y)"

context includes undefined_transfer begin

lemma div_uint16_code [code]: "x div y = (if y = 0 then 0 else uint16_div x y)"
unfolding uint16_div_def by transfer (simp add: word_div_def)

lemma mod_uint16_code [code]: "x mod y = (if y = 0 then x else uint16_mod x y)"
unfolding uint16_mod_def by transfer (simp add: word_mod_def)

lemma uint16_div_code [code abstract]:
  "Rep_uint16 (uint16_div x y) =
  (if y = 0 then Rep_uint16 (undefined ((div) :: uint16 \<Rightarrow> _) x (0 :: uint16)) else Rep_uint16 x div Rep_uint16 y)"
unfolding uint16_div_def by transfer simp

lemma uint16_mod_code [code abstract]:
  "Rep_uint16 (uint16_mod x y) =
  (if y = 0 then Rep_uint16 (undefined ((mod) :: uint16 \<Rightarrow> _) x (0 :: uint16)) else Rep_uint16 x mod Rep_uint16 y)"
unfolding uint16_mod_def by transfer simp

end

code_printing constant uint16_div \<rightharpoonup>
  (SML_word) "Word16.div ((_), (_))" and
  (Haskell) "Prelude.div" and
  (Scala) "(_ '/ _).toChar"
| constant uint16_mod \<rightharpoonup>
  (SML_word) "Word16.mod ((_), (_))" and
  (Haskell) "Prelude.mod" and
  (Scala) "(_ % _).toChar"

definition uint16_test_bit :: "uint16 \<Rightarrow> integer \<Rightarrow> bool"
where [code del]:
  "uint16_test_bit x n =
  (if n < 0 \<or> 15 < n then undefined (bit :: uint16 \<Rightarrow> _) x n
   else bit x (nat_of_integer n))"

lemma test_bit_uint16_code [code]:
  "bit x n \<longleftrightarrow> n < 16 \<and> uint16_test_bit x (integer_of_nat n)"
  including undefined_transfer integer.lifting unfolding uint16_test_bit_def
  by (transfer, simp, transfer, simp)

lemma uint16_test_bit_code [code]:
  "uint16_test_bit w n =
  (if n < 0 \<or> 15 < n then undefined (bit :: uint16 \<Rightarrow> _) w n else bit (Rep_uint16 w) (nat_of_integer n))"
  unfolding uint16_test_bit_def by (simp add: bit_uint16.rep_eq)

code_printing constant uint16_test_bit \<rightharpoonup>
  (SML_word) "Uint16.test'_bit" and
  (Haskell) "Data'_Bits.testBitBounded" and
  (Scala) "Uint16.test'_bit"

definition uint16_set_bit :: "uint16 \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> uint16"
where [code del]:
  "uint16_set_bit x n b =
  (if n < 0 \<or> 15 < n then undefined (set_bit :: uint16 \<Rightarrow> _) x n b
   else set_bit x (nat_of_integer n) b)"

lemma set_bit_uint16_code [code]:
  "set_bit x n b = (if n < 16 then uint16_set_bit x (integer_of_nat n) b else x)"
including undefined_transfer integer.lifting unfolding uint16_set_bit_def
by(transfer)(auto cong: conj_cong simp add: not_less set_bit_beyond word_size)

lemma uint16_set_bit_code [code abstract]:
  "Rep_uint16 (uint16_set_bit w n b) = 
  (if n < 0 \<or> 15 < n then Rep_uint16 (undefined (set_bit :: uint16 \<Rightarrow> _) w n b)
   else set_bit (Rep_uint16 w) (nat_of_integer n) b)"
including undefined_transfer unfolding uint16_set_bit_def by transfer simp

code_printing constant uint16_set_bit \<rightharpoonup>
  (SML_word) "Uint16.set'_bit" and
  (Haskell) "Data'_Bits.setBitBounded" and
  (Scala) "Uint16.set'_bit"

lift_definition uint16_set_bits :: "(nat \<Rightarrow> bool) \<Rightarrow> uint16 \<Rightarrow> nat \<Rightarrow> uint16" is set_bits_aux .

lemma uint16_set_bits_code [code]:
  "uint16_set_bits f w n =
  (if n = 0 then w 
   else let n' = n - 1 in uint16_set_bits f ((push_bit 1 w) OR (if f n' then 1 else 0)) n')"
  apply (transfer fixing: n)
  apply (cases n)
   apply (simp_all add: shiftl_eq_push_bit)
  done

lemma set_bits_uint16 [code]:
  "(BITS n. f n) = uint16_set_bits f 0 16"
by transfer(simp add: set_bits_conv_set_bits_aux)


lemma lsb_code [code]: fixes x :: uint16 shows "lsb x \<longleftrightarrow> bit x 0"
  by transfer (simp add: lsb_odd)

definition uint16_shiftl :: "uint16 \<Rightarrow> integer \<Rightarrow> uint16"
where [code del]:
  "uint16_shiftl x n = (if n < 0 \<or> 16 \<le> n then undefined (push_bit :: nat \<Rightarrow> uint16 \<Rightarrow> _) x n else push_bit (nat_of_integer n) x)"

lemma shiftl_uint16_code [code]: "push_bit n x = (if n < 16 then uint16_shiftl x (integer_of_nat n) else 0)"
  including undefined_transfer integer.lifting unfolding uint16_shiftl_def
  by transfer simp

lemma uint16_shiftl_code [code abstract]:
  "Rep_uint16 (uint16_shiftl w n) =
  (if n < 0 \<or> 16 \<le> n then Rep_uint16 (undefined (push_bit :: nat \<Rightarrow> uint16 \<Rightarrow> _) w n)
   else push_bit (nat_of_integer n) (Rep_uint16 w))"
  including undefined_transfer unfolding uint16_shiftl_def
  by transfer simp

code_printing constant uint16_shiftl \<rightharpoonup>
  (SML_word) "Uint16.shiftl" and
  (Haskell) "Data'_Bits.shiftlBounded" and
  (Scala) "Uint16.shiftl"

definition uint16_shiftr :: "uint16 \<Rightarrow> integer \<Rightarrow> uint16"
where [code del]:
  "uint16_shiftr x n = (if n < 0 \<or> 16 \<le> n then undefined (drop_bit :: nat \<Rightarrow> uint16 \<Rightarrow> _) x n else drop_bit (nat_of_integer n) x)"

lemma shiftr_uint16_code [code]: "drop_bit n x = (if n < 16 then uint16_shiftr x (integer_of_nat n) else 0)"
  including undefined_transfer integer.lifting unfolding uint16_shiftr_def
  by transfer simp

lemma uint16_shiftr_code [code abstract]:
  "Rep_uint16 (uint16_shiftr w n) =
  (if n < 0 \<or> 16 \<le> n then Rep_uint16 (undefined (drop_bit :: nat \<Rightarrow> uint16 \<Rightarrow> _) w n)
   else drop_bit (nat_of_integer n) (Rep_uint16 w))"
including undefined_transfer unfolding uint16_shiftr_def by transfer simp

code_printing constant uint16_shiftr \<rightharpoonup>
  (SML_word) "Uint16.shiftr" and
  (Haskell) "Data'_Bits.shiftrBounded" and
  (Scala) "Uint16.shiftr"

definition uint16_sshiftr :: "uint16 \<Rightarrow> integer \<Rightarrow> uint16"
where [code del]:
  "uint16_sshiftr x n =
  (if n < 0 \<or> 16 \<le> n then undefined sshiftr_uint16 x n else sshiftr_uint16 x (nat_of_integer n))"

lemma sshiftr_uint16_code [code]:
  "x >>> n = 
  (if n < 16 then uint16_sshiftr x (integer_of_nat n) else if bit x 15 then -1 else 0)"
including undefined_transfer integer.lifting unfolding uint16_sshiftr_def
by transfer (simp add: not_less signed_drop_bit_beyond word_size)

lemma uint16_sshiftr_code [code abstract]:
  "Rep_uint16 (uint16_sshiftr w n) =
  (if n < 0 \<or> 16 \<le> n then Rep_uint16 (undefined sshiftr_uint16 w n)
   else signed_drop_bit (nat_of_integer n) (Rep_uint16 w))"
including undefined_transfer unfolding uint16_sshiftr_def by transfer simp

code_printing constant uint16_sshiftr \<rightharpoonup>
  (SML_word) "Uint16.shiftr'_signed" and
  (Haskell) 
    "(Prelude.fromInteger (Prelude.toInteger (Data'_Bits.shiftrBounded (Prelude.fromInteger (Prelude.toInteger _) :: Uint16.Int16) _)) :: Uint16.Word16)" and
  (Scala) "Uint16.shiftr'_signed"

lemma uint16_msb_test_bit: "msb x \<longleftrightarrow> bit (x :: uint16) 15"
  by transfer (simp add: msb_word_iff_bit)

lemma msb_uint16_code [code]: "msb x \<longleftrightarrow> uint16_test_bit x 15"
  by (simp add: uint16_test_bit_def uint16_msb_test_bit)

lemma uint16_of_int_code [code]: "uint16_of_int i = Uint16 (integer_of_int i)"
including integer.lifting by transfer simp

lemma int_of_uint16_code [code]:
  "int_of_uint16 x = int_of_integer (integer_of_uint16 x)"
by(simp add: integer_of_uint16_def)

lemma nat_of_uint16_code [code]:
  "nat_of_uint16 x = nat_of_integer (integer_of_uint16 x)"
unfolding integer_of_uint16_def including integer.lifting by transfer simp

lemma integer_of_uint16_code [code]:
  "integer_of_uint16 n = integer_of_int (uint (Rep_uint16' n))"
unfolding integer_of_uint16_def by transfer auto

code_printing
  constant "integer_of_uint16" \<rightharpoonup>
  (SML_word) "Word16.toInt _ : IntInf.int" and
  (Haskell) "Prelude.toInteger" and
  (Scala) "BigInt"

section \<open>Quickcheck setup\<close>

definition uint16_of_natural :: "natural \<Rightarrow> uint16"
where "uint16_of_natural x \<equiv> Uint16 (integer_of_natural x)"

instantiation uint16 :: "{random, exhaustive, full_exhaustive}" begin
definition "random_uint16 \<equiv> qc_random_cnv uint16_of_natural"
definition "exhaustive_uint16 \<equiv> qc_exhaustive_cnv uint16_of_natural"
definition "full_exhaustive_uint16 \<equiv> qc_full_exhaustive_cnv uint16_of_natural"
instance ..
end

instantiation uint16 :: narrowing begin

interpretation quickcheck_narrowing_samples
  "\<lambda>i. let x = Uint16 i in (x, 0xFFFF - x)" "0"
  "Typerep.Typerep (STR ''Uint16.uint16'') []" .

definition "narrowing_uint16 d = qc_narrowing_drawn_from (narrowing_samples d) d"
declare [[code drop: "partial_term_of :: uint16 itself \<Rightarrow> _"]]
lemmas partial_term_of_uint16 [code] = partial_term_of_code

instance ..
end

no_notation sshiftr_uint16 (infixl ">>>" 55)

end
