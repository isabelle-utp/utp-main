(*  Title:      Code_Target_Bits_Int.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter \<open>Implementation of bit operations on int by target language operations\<close>

theory Code_Target_Bits_Int
imports
  Bits_Integer
  "HOL-Library.Code_Target_Int"
begin

declare [[code drop:
  "(AND) :: int \<Rightarrow> _" "(OR) :: int \<Rightarrow> _" "(XOR) :: int \<Rightarrow> _" "(NOT) :: int \<Rightarrow> _"
  "lsb :: int \<Rightarrow> _" "set_bit :: int \<Rightarrow> _" "bit :: int \<Rightarrow> _"
  "push_bit :: _ \<Rightarrow> int \<Rightarrow> _" "drop_bit :: _ \<Rightarrow> int \<Rightarrow> _"
  int_of_integer_symbolic
  ]]

declare bitval_bin_last [code_unfold]

lemma [code_unfold]:
  \<open>bit x n \<longleftrightarrow> x AND (push_bit n 1) \<noteq> 0\<close> for x :: int
  by (fact bit_iff_and_push_bit_not_eq_0)

context
includes integer.lifting
begin

lemma bit_int_code [code]:
  "bit (int_of_integer x) n = bit x n"
  by transfer simp

lemma and_int_code [code]:
  "int_of_integer i AND int_of_integer j = int_of_integer (i AND j)"
  by transfer simp

lemma or_int_code [code]:
  "int_of_integer i OR int_of_integer j = int_of_integer (i OR j)"
  by transfer simp

lemma xor_int_code [code]:
  "int_of_integer i XOR int_of_integer j = int_of_integer (i XOR j)"
  by transfer simp

lemma not_int_code [code]:
  "NOT (int_of_integer i) = int_of_integer (NOT i)"
  by transfer simp

lemma push_bit_int_code [code]:
  \<open>push_bit n (int_of_integer x) = int_of_integer (push_bit n x)\<close>
  by transfer simp

lemma drop_bit_int_code [code]:
  \<open>drop_bit n (int_of_integer x) = int_of_integer (drop_bit n x)\<close>
  by transfer simp

lemma take_bit_int_code [code]:
  \<open>take_bit n (int_of_integer x) = int_of_integer (take_bit n x)\<close>
  by transfer simp

lemma lsb_int_code [code]:
  "lsb (int_of_integer x) = lsb x"
  by transfer simp

lemma set_bit_int_code [code]:
  "set_bit (int_of_integer x) n b = int_of_integer (set_bit x n b)"
  by transfer simp

lemma int_of_integer_symbolic_code [code]:
  "int_of_integer_symbolic = int_of_integer"
  by (simp add: int_of_integer_symbolic_def)

context
begin

qualified definition even :: \<open>int \<Rightarrow> bool\<close>
  where [code_abbrev]: \<open>even = Parity.even\<close>

end

lemma [code]:
  \<open>Code_Target_Bits_Int.even i \<longleftrightarrow> i AND 1 = 0\<close>
  by (simp add: Code_Target_Bits_Int.even_def even_iff_mod_2_eq_zero and_one_eq)

lemma bin_rest_code:
  "bin_rest (int_of_integer i) = int_of_integer (bin_rest_integer i)"
  by transfer simp

end

end
