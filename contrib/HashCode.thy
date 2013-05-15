(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header {* \isaheader {The hashable Typeclass} *}
theory HashCode
imports Main
begin
text_raw {*\label{thy:HashCode}*}


text {*
  In this theory a typeclass of hashable types is established.
  For hashable types, there is a function @{text hashcode}, that
  maps any entity of this type to an integer value.

  This theory defines the hashable typeclass and provides instantiations 
  for a couple of standard types.
*}

type_synonym 
  hashcode = "nat"

class hashable =
  fixes hashcode :: "'a \<Rightarrow> hashcode"
  and bounded_hashcode :: "nat \<Rightarrow> 'a \<Rightarrow> hashcode"
  and def_hashmap_size :: "'a itself \<Rightarrow> nat"
  assumes bounded_hashcode_bounds: "1 < n \<Longrightarrow> bounded_hashcode n a < n"
  and def_hashmap_size: "1 < def_hashmap_size TYPE('a)"

instantiation unit :: hashable 
begin
  definition [simp]: "hashcode (u :: unit) = 0"
  definition [simp]: "bounded_hashcode n (u :: unit) = 0"
  definition "def_hashmap_size = (\<lambda>_ :: unit itself. 2)"
  instance by(intro_classes)(simp_all add: def_hashmap_size_unit_def)
end

instantiation bool :: hashable
begin
  definition [simp]: "hashcode (b :: bool) = (if b then 1 else 0)"
  definition [simp]: "bounded_hashcode n (b :: bool) = (if b then 1 else 0)"
  definition "def_hashmap_size = (\<lambda>_ :: bool itself. 2)"
  instance by(intro_classes)(simp_all add: def_hashmap_size_bool_def)
end

instantiation "int" :: hashable
begin
  definition [simp]: "hashcode (i :: int) = nat (abs i)"
  definition [simp]: "bounded_hashcode n (i :: int) = nat (abs i) mod n"
  definition "def_hashmap_size = (\<lambda>_ :: int itself. 16)"
  instance by(intro_classes)(simp_all add: def_hashmap_size_int_def)
end

instantiation "nat" :: hashable
begin
  definition [simp]: "hashcode (n :: nat) = n"
  definition [simp]: "bounded_hashcode n' (n :: nat) == n mod n'"
  definition "def_hashmap_size = (\<lambda>_ :: nat itself. 16)"
  instance by(intro_classes)(simp_all add: def_hashmap_size_nat_def)
end

fun num_of_nibble :: "nibble \<Rightarrow> nat"
  where
  "num_of_nibble Nibble0 = 0" |
  "num_of_nibble Nibble1 = 1" |
  "num_of_nibble Nibble2 = 2" |
  "num_of_nibble Nibble3 = 3" |
  "num_of_nibble Nibble4 = 4" |
  "num_of_nibble Nibble5 = 5" |
  "num_of_nibble Nibble6 = 6" |
  "num_of_nibble Nibble7 = 7" |
  "num_of_nibble Nibble8 = 8" |
  "num_of_nibble Nibble9 = 9" |
  "num_of_nibble NibbleA = 10" |
  "num_of_nibble NibbleB = 11" |
  "num_of_nibble NibbleC = 12" |
  "num_of_nibble NibbleD = 13" |
  "num_of_nibble NibbleE = 14" |
  "num_of_nibble NibbleF = 15"

instantiation "nibble" :: hashable
begin
  definition [simp]: "hashcode (c :: nibble) = num_of_nibble c"
  definition [simp]: "bounded_hashcode n c == num_of_nibble c mod n"
  definition "def_hashmap_size = (\<lambda>_ :: nibble itself. 16)"
  instance by(intro_classes)(simp_all add: def_hashmap_size_nibble_def)
end

instantiation char :: hashable 
begin
  fun hashcode_of_char :: " char \<Rightarrow> hashcode" where
    "hashcode_of_char (Char a b) = num_of_nibble a * 16 + num_of_nibble b"

  definition [simp]: "hashcode c == hashcode_of_char c"
  definition [simp]: "bounded_hashcode n c == hashcode_of_char c mod n"
  definition "def_hashmap_size = (\<lambda>_ :: char itself. 32)"
  instance by(intro_classes)(simp_all add: def_hashmap_size_char_def)
end

instantiation prod :: (hashable, hashable) hashable
begin
  definition "hashcode x == (hashcode (fst x) * 33 + hashcode (snd x))"
  definition "bounded_hashcode n x == (bounded_hashcode n (fst x) * 33 + bounded_hashcode n (snd x)) mod n"
  definition "def_hashmap_size = (\<lambda>_ :: ('a \<times> 'b) itself. def_hashmap_size TYPE('a) + def_hashmap_size TYPE('b))"
  instance using def_hashmap_size[where ?'a="'a"] def_hashmap_size[where ?'a="'b"]
    by(intro_classes)(simp_all add: bounded_hashcode_prod_def def_hashmap_size_prod_def)
end

instantiation sum :: (hashable, hashable) hashable
begin
  definition "hashcode x == (case x of Inl a \<Rightarrow> 2 * hashcode a | Inr b \<Rightarrow> 2 * hashcode b + 1)"
  definition "bounded_hashcode n x == (case x of Inl a \<Rightarrow> bounded_hashcode n a | Inr b \<Rightarrow> (n - 1 - bounded_hashcode n b))"
  definition "def_hashmap_size = (\<lambda>_ :: ('a + 'b) itself. def_hashmap_size TYPE('a) + def_hashmap_size TYPE('b))"
  instance using def_hashmap_size[where ?'a="'a"] def_hashmap_size[where ?'a="'b"]
    by(intro_classes)(simp_all add: bounded_hashcode_sum_def bounded_hashcode_bounds def_hashmap_size_sum_def split: sum.split)
end

instantiation list :: (hashable) hashable
begin
  definition "hashcode = foldl (\<lambda>h x. h * 33 + hashcode x) 5381"
  definition "bounded_hashcode n = foldl (\<lambda>h x. (h * 33 + bounded_hashcode n x) mod n) (5381 mod n)"
  definition "def_hashmap_size = (\<lambda>_ :: 'a list itself. 2 * def_hashmap_size TYPE('a))"
  instance 
  proof
    fix n :: nat and xs :: "'a list"
    assume "1 < n"
    thus "bounded_hashcode n xs < n" unfolding bounded_hashcode_list_def
      by(cases xs rule: rev_cases) simp_all
  next
    from def_hashmap_size[where ?'a = "'a"]
    show "1 < def_hashmap_size TYPE('a list)"
      by(simp add: def_hashmap_size_list_def)
  qed
end

instantiation option :: (hashable) hashable
begin
  definition "hashcode opt = (case opt of None \<Rightarrow> 0 | Some a \<Rightarrow> hashcode a + 1)"
  definition "bounded_hashcode n opt = (case opt of None \<Rightarrow> 0 | Some a \<Rightarrow> (bounded_hashcode n a + 1) mod n)"
  definition "def_hashmap_size = (\<lambda>_ :: 'a option itself. def_hashmap_size TYPE('a) + 1)"
  instance using def_hashmap_size[where ?'a = "'a"]
    by(intro_classes)(simp_all add: bounded_hashcode_option_def def_hashmap_size_option_def split: option.split)
end

lemma hashcode_option_simps [simp]:
  "hashcode None = 0"
  "hashcode (Some a) = 1 + hashcode a"
  by(simp_all add: hashcode_option_def)

lemma bounded_hashcode_option_simps [simp]:
  "bounded_hashcode n None = 0"
  "bounded_hashcode n (Some a) = (bounded_hashcode n a + 1) mod n"
  by(simp_all add: bounded_hashcode_option_def)

end
