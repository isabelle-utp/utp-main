(*  Title:      Code_Symbolic_Bits_Int.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter \<open>Symbolic implementation of bit operations on int\<close>

theory Code_Symbolic_Bits_Int
imports
  "Word_Lib.Generic_set_bit"
  "Word_Lib.Least_significant_bit"
  More_Bits_Int
begin

section \<open>Implementations of bit operations on \<^typ>\<open>int\<close> operating on symbolic representation\<close>

lemma test_bit_int_code [code]:
  "bit (0::int)          n = False"
  "bit (Int.Neg num.One) n = True"
  "bit (Int.Pos num.One)      0 = True"
  "bit (Int.Pos (num.Bit0 m)) 0 = False"
  "bit (Int.Pos (num.Bit1 m)) 0 = True"
  "bit (Int.Neg (num.Bit0 m)) 0 = False"
  "bit (Int.Neg (num.Bit1 m)) 0 = True"
  "bit (Int.Pos num.One)      (Suc n) = False"
  "bit (Int.Pos (num.Bit0 m)) (Suc n) = bit (Int.Pos m) n"
  "bit (Int.Pos (num.Bit1 m)) (Suc n) = bit (Int.Pos m) n"
  "bit (Int.Neg (num.Bit0 m)) (Suc n) = bit (Int.Neg m) n"
  "bit (Int.Neg (num.Bit1 m)) (Suc n) = bit (Int.Neg (Num.inc m)) n"
  by (simp_all add: Num.add_One bit_Suc)

lemma int_not_code [code]:
  "NOT (0 :: int) = -1"
  "NOT (Int.Pos n) = Int.Neg (Num.inc n)"
  "NOT (Int.Neg n) = Num.sub n num.One"
by(simp_all add: Num.add_One int_not_def)

lemma int_and_code [code]: fixes i j :: int shows
  "0 AND j = 0"
  "i AND 0 = 0"
  "Int.Pos n AND Int.Pos m = (case bitAND_num n m of None \<Rightarrow> 0 | Some n' \<Rightarrow> Int.Pos n')"
  "Int.Neg n AND Int.Neg m = NOT (Num.sub n num.One OR Num.sub m num.One)"
  "Int.Pos n AND Int.Neg num.One = Int.Pos n"
  "Int.Pos n AND Int.Neg (num.Bit0 m) = Num.sub (bitORN_num (Num.BitM m) n) num.One"
  "Int.Pos n AND Int.Neg (num.Bit1 m) = Num.sub (bitORN_num (num.Bit0 m) n) num.One"
  "Int.Neg num.One AND Int.Pos m = Int.Pos m"
  "Int.Neg (num.Bit0 n) AND Int.Pos m = Num.sub (bitORN_num (Num.BitM n) m) num.One"
  "Int.Neg (num.Bit1 n) AND Int.Pos m = Num.sub (bitORN_num (num.Bit0 n) m) num.One"
           apply (simp_all add: int_numeral_bitAND_num Num.add_One
              sub_inc_One_eq inc_BitM_eq not_minus_numeral_inc_eq
              flip: int_not_neg_numeral int_or_not_bitORN_num split: option.split)
   apply (simp_all add: ac_simps)
  done

lemma int_or_code [code]: fixes i j :: int shows
  "0 OR j = j"
  "i OR 0 = i"
  "Int.Pos n OR Int.Pos m = Int.Pos (bitOR_num n m)"
  "Int.Neg n OR Int.Neg m = NOT (Num.sub n num.One AND Num.sub m num.One)"
  "Int.Pos n OR Int.Neg num.One = Int.Neg num.One"
  "Int.Pos n OR Int.Neg (num.Bit0 m) = (case bitANDN_num (Num.BitM m) n of None \<Rightarrow> -1 | Some n' \<Rightarrow> Int.Neg (Num.inc n'))"
  "Int.Pos n OR Int.Neg (num.Bit1 m) = (case bitANDN_num (num.Bit0 m) n of None \<Rightarrow> -1 | Some n' \<Rightarrow> Int.Neg (Num.inc n'))"
  "Int.Neg num.One OR Int.Pos m = Int.Neg num.One"
  "Int.Neg (num.Bit0 n) OR Int.Pos m = (case bitANDN_num (Num.BitM n) m of None \<Rightarrow> -1 | Some n' \<Rightarrow> Int.Neg (Num.inc n'))"
  "Int.Neg (num.Bit1 n) OR Int.Pos m = (case bitANDN_num (num.Bit0 n) m of None \<Rightarrow> -1 | Some n' \<Rightarrow> Int.Neg (Num.inc n'))"
           apply (simp_all add: int_numeral_bitOR_num flip: int_not_neg_numeral)
     apply (simp_all add: or_int_def int_and_comm int_not_and_bitANDN_num del: int_not_simps(4) split: option.split)
     apply (simp_all add: Num.add_One)
  done

lemma int_xor_code [code]: fixes i j :: int shows
  "0 XOR j = j"
  "i XOR 0 = i"
  "Int.Pos n XOR Int.Pos m = (case bitXOR_num n m of None \<Rightarrow> 0 | Some n' \<Rightarrow> Int.Pos n')"
  "Int.Neg n XOR Int.Neg m = Num.sub n num.One XOR Num.sub m num.One"
  "Int.Neg n XOR Int.Pos m = NOT (Num.sub n num.One XOR Int.Pos m)"
  "Int.Pos n XOR Int.Neg m = NOT (Int.Pos n XOR Num.sub m num.One)"
  by(fold int_not_neg_numeral)(simp_all add: int_numeral_bitXOR_num int_xor_not cong: option.case_cong)

lemma bin_rest_code: "bin_rest i = i >> 1"
  by (simp add: shiftr_int_def)

lemma set_bits_code [code]: 
  "set_bits = Code.abort (STR ''set_bits is unsupported on type int'') (\<lambda>_. set_bits :: _ \<Rightarrow> int)"
by simp

lemma fixes i :: int 
  shows int_set_bit_True_conv_OR [code]: "set_bit i n True = i OR (1 << n)"
  and int_set_bit_False_conv_NAND [code]: "set_bit i n False = i AND NOT (1 << n)"
  and int_set_bit_conv_ops: "set_bit i n b = (if b then i OR (1 << n) else i AND NOT (1 << n))"
by(simp_all add: set_bit_int_def bin_set_conv_OR bin_clr_conv_NAND)

declare [[code drop: \<open>drop_bit :: nat \<Rightarrow> int \<Rightarrow> int\<close>]]

lemma drop_bit_int_code [code]: fixes i :: int shows
  "drop_bit 0 i = i"
  "drop_bit (Suc n) 0 = (0 :: int)"
  "drop_bit (Suc n) (Int.Pos num.One) = 0"
  "drop_bit (Suc n) (Int.Pos (num.Bit0 m)) = drop_bit n (Int.Pos m)"
  "drop_bit (Suc n) (Int.Pos (num.Bit1 m)) = drop_bit n (Int.Pos m)"
  "drop_bit (Suc n) (Int.Neg num.One) = - 1"
  "drop_bit (Suc n) (Int.Neg (num.Bit0 m)) = drop_bit n (Int.Neg m)"
  "drop_bit (Suc n) (Int.Neg (num.Bit1 m)) = drop_bit n (Int.Neg (Num.inc m))"
  by (simp_all add: shiftr_eq_drop_bit drop_bit_Suc add_One)

declare [[code drop: \<open>push_bit :: nat \<Rightarrow> int \<Rightarrow> int\<close>]]

lemma push_bit_int_code [code]:
  "push_bit 0 i = i"
  "push_bit (Suc n) i = push_bit n (Int.dup i)"
  by (simp_all add: ac_simps)

lemma int_lsb_code [code]:
  "lsb (0 :: int) = False"
  "lsb (Int.Pos num.One) = True"
  "lsb (Int.Pos (num.Bit0 w)) = False"
  "lsb (Int.Pos (num.Bit1 w)) = True"
  "lsb (Int.Neg num.One) = True"
  "lsb (Int.Neg (num.Bit0 w)) = False"
  "lsb (Int.Neg (num.Bit1 w)) = True"
  by simp_all

end
