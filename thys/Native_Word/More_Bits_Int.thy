(*  Title:      Bits_Int.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter \<open>More bit operations on integers\<close>

theory More_Bits_Int
imports
  "Word_Lib.Bits_Int"
  "Word_Lib.Bit_Comprehension"
begin

text \<open>Preliminaries\<close>

lemma last_rev' [simp]: "last (rev xs) = hd xs" \<comment> \<open>TODO define \<open>last []\<close> as \<open>hd []\<close>?\<close>
  by (cases xs) (simp add: last_def hd_def, simp)

lemma nat_LEAST_True: "(LEAST _ :: nat. True) = 0"
  by (rule Least_equality) simp_all

text \<open>
  Use this function to convert numeral @{typ integer}s quickly into @{typ int}s.
  By default, it works only for symbolic evaluation; normally generated code raises
  an exception at run-time. If theory \<open>Code_Target_Bits_Int\<close> is imported,
  it works again, because then @{typ int} is implemented in terms of @{typ integer}
  even for symbolic evaluation.
\<close>

definition int_of_integer_symbolic :: "integer \<Rightarrow> int"
  where "int_of_integer_symbolic = int_of_integer"

lemma int_of_integer_symbolic_aux_code [code nbe]:
  "int_of_integer_symbolic 0 = 0"
  "int_of_integer_symbolic (Code_Numeral.Pos n) = Int.Pos n"
  "int_of_integer_symbolic (Code_Numeral.Neg n) = Int.Neg n"
  by (simp_all add: int_of_integer_symbolic_def)


section \<open>Symbolic bit operations on numerals and @{typ int}s\<close>

fun bitOR_num :: "num \<Rightarrow> num \<Rightarrow> num"
where
  "bitOR_num num.One num.One = num.One"
| "bitOR_num num.One (num.Bit0 n) = num.Bit1 n"
| "bitOR_num num.One (num.Bit1 n) = num.Bit1 n"
| "bitOR_num (num.Bit0 m) num.One = num.Bit1 m"
| "bitOR_num (num.Bit0 m) (num.Bit0 n) = num.Bit0 (bitOR_num m n)"
| "bitOR_num (num.Bit0 m) (num.Bit1 n) = num.Bit1 (bitOR_num m n)"
| "bitOR_num (num.Bit1 m) num.One = num.Bit1 m"
| "bitOR_num (num.Bit1 m) (num.Bit0 n) = num.Bit1 (bitOR_num m n)"
| "bitOR_num (num.Bit1 m) (num.Bit1 n) = num.Bit1 (bitOR_num m n)"

fun bitAND_num :: "num \<Rightarrow> num \<Rightarrow> num option"
where
  "bitAND_num num.One num.One = Some num.One"
| "bitAND_num num.One (num.Bit0 n) = None"
| "bitAND_num num.One (num.Bit1 n) = Some num.One"
| "bitAND_num (num.Bit0 m) num.One = None"
| "bitAND_num (num.Bit0 m) (num.Bit0 n) = map_option num.Bit0 (bitAND_num m n)"
| "bitAND_num (num.Bit0 m) (num.Bit1 n) = map_option num.Bit0 (bitAND_num m n)"
| "bitAND_num (num.Bit1 m) num.One = Some num.One"
| "bitAND_num (num.Bit1 m) (num.Bit0 n) = map_option num.Bit0 (bitAND_num m n)"
| "bitAND_num (num.Bit1 m) (num.Bit1 n) = (case bitAND_num m n of None \<Rightarrow> Some num.One | Some n' \<Rightarrow> Some (num.Bit1 n'))"

fun bitXOR_num :: "num \<Rightarrow> num \<Rightarrow> num option"
where
  "bitXOR_num num.One num.One = None"
| "bitXOR_num num.One (num.Bit0 n) = Some (num.Bit1 n)"
| "bitXOR_num num.One (num.Bit1 n) = Some (num.Bit0 n)"
| "bitXOR_num (num.Bit0 m) num.One = Some (num.Bit1 m)"
| "bitXOR_num (num.Bit0 m) (num.Bit0 n) = map_option num.Bit0 (bitXOR_num m n)"
| "bitXOR_num (num.Bit0 m) (num.Bit1 n) = Some (case bitXOR_num m n of None \<Rightarrow> num.One | Some n' \<Rightarrow> num.Bit1 n')"
| "bitXOR_num (num.Bit1 m) num.One = Some (num.Bit0 m)"
| "bitXOR_num (num.Bit1 m) (num.Bit0 n) = Some (case bitXOR_num m n of None \<Rightarrow> num.One | Some n' \<Rightarrow> num.Bit1 n')"
| "bitXOR_num (num.Bit1 m) (num.Bit1 n) = map_option num.Bit0 (bitXOR_num m n)"

fun bitORN_num :: "num \<Rightarrow> num \<Rightarrow> num"
where
  "bitORN_num num.One num.One = num.One"
| "bitORN_num num.One (num.Bit0 m) = num.Bit1 m"
| "bitORN_num num.One (num.Bit1 m) = num.Bit1 m"
| "bitORN_num (num.Bit0 n) num.One = num.Bit0 num.One"
| "bitORN_num (num.Bit0 n) (num.Bit0 m) = Num.BitM (bitORN_num n m)"
| "bitORN_num (num.Bit0 n) (num.Bit1 m) = num.Bit0 (bitORN_num n m)"
| "bitORN_num (num.Bit1 n) num.One = num.One"
| "bitORN_num (num.Bit1 n) (num.Bit0 m) = Num.BitM (bitORN_num n m)"
| "bitORN_num (num.Bit1 n) (num.Bit1 m) = Num.BitM (bitORN_num n m)"

fun bitANDN_num :: "num \<Rightarrow> num \<Rightarrow> num option"
where
  "bitANDN_num num.One num.One = None"
| "bitANDN_num num.One (num.Bit0 n) = Some num.One"
| "bitANDN_num num.One (num.Bit1 n) = None"
| "bitANDN_num (num.Bit0 m) num.One = Some (num.Bit0 m)"
| "bitANDN_num (num.Bit0 m) (num.Bit0 n) = map_option num.Bit0 (bitANDN_num m n)"
| "bitANDN_num (num.Bit0 m) (num.Bit1 n) = map_option num.Bit0 (bitANDN_num m n)"
| "bitANDN_num (num.Bit1 m) num.One = Some (num.Bit0 m)"
| "bitANDN_num (num.Bit1 m) (num.Bit0 n) = (case bitANDN_num m n of None \<Rightarrow> Some num.One | Some n' \<Rightarrow> Some (num.Bit1 n'))"
| "bitANDN_num (num.Bit1 m) (num.Bit1 n) = map_option num.Bit0 (bitANDN_num m n)"

lemma int_numeral_bitOR_num: "numeral n OR numeral m = (numeral (bitOR_num n m) :: int)"
by(induct n m rule: bitOR_num.induct) simp_all

lemma int_numeral_bitAND_num: "numeral n AND numeral m = (case bitAND_num n m of None \<Rightarrow> 0 :: int | Some n' \<Rightarrow> numeral n')"
by(induct n m rule: bitAND_num.induct)(simp_all split: option.split)

lemma int_numeral_bitXOR_num:
  "numeral m XOR numeral n = (case bitXOR_num m n of None \<Rightarrow> 0 :: int | Some n' \<Rightarrow> numeral n')"
by(induct m n rule: bitXOR_num.induct)(simp_all split: option.split)

lemma int_or_not_bitORN_num:
  "numeral n OR NOT (numeral m) = (- numeral (bitORN_num n m) :: int)"
  by (induction n m rule: bitORN_num.induct) (simp_all add: add_One BitM_inc_eq)

lemma int_and_not_bitANDN_num:
  "numeral n AND NOT (numeral m) = (case bitANDN_num n m of None \<Rightarrow> 0 :: int | Some n' \<Rightarrow> numeral n')"
  by (induction n m rule: bitANDN_num.induct) (simp_all add: add_One BitM_inc_eq split: option.split)

lemma int_not_and_bitANDN_num:
  "NOT (numeral m) AND numeral n = (case bitANDN_num n m of None \<Rightarrow> 0 :: int | Some n' \<Rightarrow> numeral n')"
by(simp add: int_and_not_bitANDN_num[symmetric] int_and_comm)

code_identifier
  code_module More_Bits_Int \<rightharpoonup>
  (SML) Bit_Operations and (OCaml) Bit_Operations and (Haskell) Bit_Operations and (Scala) Bit_Operations

end
