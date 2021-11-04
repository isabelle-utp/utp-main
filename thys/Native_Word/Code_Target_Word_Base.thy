(*  Title:      Code_Target_Word_Base.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter \<open>Common base for target language implementations of word types\<close>

theory Code_Target_Word_Base imports
  "HOL-Library.Word"
  "Word_Lib.Signed_Division_Word"
  Bits_Integer
begin

text \<open>More lemmas\<close>

lemma div_half_nat:
  fixes x y :: nat
  assumes "y \<noteq> 0"
  shows "(x div y, x mod y) = (let q = 2 * (x div 2 div y); r = x - q * y in if y \<le> r then (q + 1, r - y) else (q, r))"
proof -
  let ?q = "2 * (x div 2 div y)"
  have q: "?q = x div y - x div y mod 2"
    by(metis div_mult2_eq mult.commute minus_mod_eq_mult_div [symmetric])
  let ?r = "x - ?q * y"
  have r: "?r = x mod y + x div y mod 2 * y"
    by(simp add: q diff_mult_distrib minus_mod_eq_div_mult [symmetric])(metis diff_diff_cancel mod_less_eq_dividend mod_mult2_eq add.commute mult.commute)

  show ?thesis
  proof(cases "y \<le> x - ?q * y")
    case True
    with assms q have "x div y mod 2 \<noteq> 0" unfolding r
      by (metis Nat.add_0_right diff_0_eq_0 diff_Suc_1 le_div_geq mod2_gr_0 mod_div_trivial mult_0 neq0_conv numeral_1_eq_Suc_0 numerals(1)) 
    hence "x div y = ?q + 1" unfolding q
      by simp
    moreover hence "x mod y = ?r - y"
      by simp(metis minus_div_mult_eq_mod [symmetric] diff_commute diff_diff_left mult_Suc)
    ultimately show ?thesis using True by(simp add: Let_def)
  next
    case False
    hence "x div y mod 2 = 0" unfolding r
      by(simp add: not_le)(metis Nat.add_0_right assms div_less div_mult_self2 mod_div_trivial mult.commute)
    hence "x div y = ?q" unfolding q by simp
    moreover hence "x mod y = ?r" by (metis minus_div_mult_eq_mod [symmetric])
    ultimately show ?thesis using False by(simp add: Let_def)
  qed
qed

lemma div_half_word:
  fixes x y :: "'a :: len word"
  assumes "y \<noteq> 0"
  shows "(x div y, x mod y) = (let q = (x >> 1) div y << 1; r = x - q * y in if y \<le> r then (q + 1, r - y) else (q, r))"
proof -
  obtain n where n: "x = of_nat n" "n < 2 ^ LENGTH('a)"
    by (rule that [of \<open>unat x\<close>]) simp_all
  moreover obtain m where m: "y = of_nat m" "m < 2 ^ LENGTH('a)"
    by (rule that [of \<open>unat y\<close>]) simp_all
  ultimately have [simp]: \<open>unat (of_nat n :: 'a word) = n\<close> \<open>unat (of_nat m :: 'a word) = m\<close>
    by (transfer, simp add: take_bit_of_nat take_bit_nat_eq_self_iff)+
  let ?q = "(x >> 1) div y << 1"
  let ?q' = "2 * (n div 2 div m)"
  have "n div 2 div m < 2 ^ LENGTH('a)" using n by (metis of_nat_inverse unat_lt2p uno_simps(2))
  hence q: "?q = of_nat ?q'" using n m
    by (auto simp add: shiftr_word_eq drop_bit_eq_div shiftl_t2n word_arith_nat_div uno_simps take_bit_nat_eq_self)
  from assms have "m \<noteq> 0" using m by -(rule notI, simp)

  from n have "2 * (n div 2 div m) < 2 ^ LENGTH('a)"
    by(metis mult.commute div_mult2_eq minus_mod_eq_mult_div [symmetric] less_imp_diff_less of_nat_inverse unat_lt2p uno_simps(2))
  moreover
  have "2 * (n div 2 div m) * m < 2 ^ LENGTH('a)" using n unfolding div_mult2_eq[symmetric]
    by(subst (2) mult.commute)(simp add: minus_mod_eq_div_mult [symmetric] diff_mult_distrib minus_mod_eq_mult_div [symmetric] div_mult2_eq)
  moreover have "2 * (n div 2 div m) * m \<le> n"
    by (simp flip: div_mult2_eq ac_simps)
  ultimately
  have r: "x - ?q * y = of_nat (n - ?q' * m)"
    and "y \<le> x - ?q * y \<Longrightarrow> of_nat (n - ?q' * m) - y = of_nat (n - ?q' * m - m)"
    using n m unfolding q
     apply (simp_all add: of_nat_diff)
    apply (subst of_nat_diff)
    apply (simp_all add: word_le_nat_alt take_bit_nat_eq_self unat_sub_if' unat_word_ariths)
    apply (cases \<open>2 \<le> LENGTH('a)\<close>)
    apply (simp_all add: unat_word_ariths take_bit_nat_eq_self)
    done
  then show ?thesis using n m div_half_nat [OF \<open>m \<noteq> 0\<close>, of n] unfolding q
    by (simp add: word_le_nat_alt word_div_def word_mod_def Let_def take_bit_nat_eq_self
      flip: zdiv_int zmod_int
      split del: if_split split: if_split_asm)
qed

lemma word_test_bit_set_bits: "(BITS n. f n :: 'a :: len word) !! n \<longleftrightarrow> n < LENGTH('a) \<and> f n"
  by (simp add: test_bit_eq_bit bit_set_bits_word_iff)

lemma word_of_int_conv_set_bits: "word_of_int i = (BITS n. i !! n)"
  by (rule word_eqI) (auto simp add: word_test_bit_set_bits)

lemma word_and_mask_or_conv_and_mask:
  "n !! index \<Longrightarrow> (n AND mask index) OR (1 << index) = n AND mask (index + 1)"
  for n :: \<open>'a::len word\<close>
by(rule word_eqI)(auto simp add: word_ao_nth word_size nth_shiftl simp del: shiftl_1)

lemma uint_and_mask_or_full:
  fixes n :: "'a :: len word"
  assumes "n !! (LENGTH('a) - 1)"
  and "mask1 = mask (LENGTH('a) - 1)"
  and "mask2 = 1 << LENGTH('a) - 1"
  shows "uint (n AND mask1) OR mask2 = uint n"
proof -
  have "mask2 = uint (1 << LENGTH('a) - 1 :: 'a word)" using assms
    by (simp add: uint_shiftl word_size bintrunc_shiftl del: shiftl_1)
  hence "uint (n AND mask1) OR mask2 = uint (n AND mask1 OR (1 << LENGTH('a) - 1 :: 'a word))"
    by(simp add: uint_or)
  also have "\<dots> = uint (n AND mask (LENGTH('a) - 1 + 1))"
    using assms by(simp only: word_and_mask_or_conv_and_mask)
  also have "\<dots> = uint n" by simp
  finally show ?thesis .
qed


text \<open>Division on @{typ "'a word"} is unsigned, but Scala and OCaml only have signed division and modulus.\<close>

lemmas word_sdiv_def = sdiv_word_def
lemmas word_smod_def = smod_word_def

lemma [code]:
  "x sdiv y =
   (let x' = sint x; y' = sint y;
        negative = (x' < 0) \<noteq> (y' < 0);
        result = abs x' div abs y'
    in word_of_int (if negative then -result else result))"
  for x y :: \<open>'a::len word\<close>
  by (simp add: sdiv_word_def signed_divide_int_def sgn_if Let_def not_less not_le)

lemma [code]:
  "x smod y =
   (let x' = sint x; y' = sint y;
        negative = (x' < 0);
        result = abs x' mod abs y'
    in word_of_int (if negative then -result else result))"
  for x y :: \<open>'a::len word\<close>
proof -
  have *: \<open>k mod l = k - k div l * l\<close> for k l :: int
    by (simp add: minus_div_mult_eq_mod)
  show ?thesis
    by (simp add: smod_word_def signed_modulo_int_def signed_divide_int_def * sgn_if Let_def)
qed

text \<open>
  This algorithm implements unsigned division in terms of signed division.
  Taken from Hacker's Delight.
\<close>

lemma divmod_via_sdivmod:
  fixes x y :: "'a :: len word"
  assumes "y \<noteq> 0"
  shows
  "(x div y, x mod y) =
  (if 1 << (LENGTH('a) - 1) \<le> y then if x < y then (0, x) else (1, x - y)
   else let q = ((x >> 1) sdiv y) << 1;
            r = x - q * y
        in if r \<ge> y then (q + 1, r - y) else (q, r))"
proof(cases "1 << (LENGTH('a) - 1) \<le> y")
  case True
  note y = this
  show ?thesis
  proof(cases "x < y")
    case True
    then have "x mod y = x"
      by transfer simp
    thus ?thesis using True y by(simp add: word_div_lt_eq_0)
  next
    case False
    obtain n where n: "y = of_nat n" "n < 2 ^ LENGTH('a)"
      by (rule that [of \<open>unat y\<close>]) simp_all
    have "unat x < 2 ^ LENGTH('a)" by(rule unat_lt2p)
    also have "\<dots> = 2 * 2 ^ (LENGTH('a) - 1)"
      by(metis Suc_pred len_gt_0 power_Suc One_nat_def)
    also have "\<dots> \<le> 2 * n" using y n
      by transfer (simp add: push_bit_of_1 take_bit_eq_mod)
    finally have div: "x div of_nat n = 1" using False n
      by (simp add: word_div_eq_1_iff take_bit_nat_eq_self)
    moreover have "x mod y = x - x div y * y"
      by (simp add: minus_div_mult_eq_mod)
    with div n have "x mod y = x - y" by simp
    ultimately show ?thesis using False y n by simp
  qed
next
  case False
  note y = this
  obtain n where n: "x = of_nat n" "n < 2 ^ LENGTH('a)"
    by (rule that [of \<open>unat x\<close>]) simp_all
  hence "int n div 2 + 2 ^ (LENGTH('a) - Suc 0) < 2 ^ LENGTH('a)"
    by (cases \<open>LENGTH('a)\<close>)
      (auto dest: less_imp_of_nat_less [where ?'a = int])
  with y n have "sint (x >> 1) = uint (x >> 1)"
    by (simp add: sint_uint sbintrunc_mod2p shiftr_div_2n take_bit_nat_eq_self)
  moreover have "uint y + 2 ^ (LENGTH('a) - Suc 0) < 2 ^ LENGTH('a)"
    using y by (cases "LENGTH('a)")
      (simp_all add: not_le word_2p_lem word_size)
  then have "sint y = uint y"
    by (simp add: sint_uint sbintrunc_mod2p)
  ultimately show ?thesis using y
    apply (subst div_half_word [OF assms])
    apply (simp add: sdiv_word_def signed_divide_int_def flip: uint_div)
    done
qed


text \<open>More implementations tailored towards target-language implementations\<close>

context
includes integer.lifting
begin
lift_definition word_of_integer :: "integer \<Rightarrow> 'a :: len word" is word_of_int .

lemma word_of_integer_code [code]: "word_of_integer n = word_of_int (int_of_integer n)"
by(simp add: word_of_integer.rep_eq)
end

lemma word_of_int_code:
  "uint (word_of_int x :: 'a word) = x AND mask (LENGTH('a :: len))"
  by (simp add: take_bit_eq_mask)

context fixes f :: "nat \<Rightarrow> bool" begin

definition set_bits_aux :: \<open>'a word \<Rightarrow> nat \<Rightarrow> 'a :: len word\<close>
  where \<open>set_bits_aux w n = push_bit n w OR take_bit n (set_bits f)\<close>

lemma set_bits_aux_conv:
  \<open>set_bits_aux w n = (w << n) OR (set_bits f AND mask n)\<close>
  for w :: \<open>'a::len word\<close>
  by (rule bit_word_eqI)
    (auto simp add: set_bits_aux_def shiftl_word_eq bit_and_iff bit_or_iff bit_push_bit_iff bit_take_bit_iff bit_mask_iff bit_set_bits_word_iff)

corollary set_bits_conv_set_bits_aux:
  \<open>set_bits f = (set_bits_aux 0 (LENGTH('a)) :: 'a :: len word)\<close>
  by (simp add: set_bits_aux_conv)

lemma set_bits_aux_0 [simp]:
  \<open>set_bits_aux w 0 = w\<close>
  by  (simp add: set_bits_aux_conv)

lemma set_bits_aux_Suc [simp]:
  \<open>set_bits_aux w (Suc n) = set_bits_aux ((w << 1) OR (if f n then 1 else 0)) n\<close>
  by (simp add: set_bits_aux_def shiftl_word_eq bit_eq_iff bit_or_iff bit_push_bit_iff bit_take_bit_iff bit_set_bits_word_iff)
    (auto simp add: bit_exp_iff not_less bit_1_iff less_Suc_eq_le)

lemma set_bits_aux_simps [code]:
  \<open>set_bits_aux w 0 = w\<close>
  \<open>set_bits_aux w (Suc n) = set_bits_aux ((w << 1) OR (if f n then 1 else 0)) n\<close>
  by simp_all

end

lemma word_of_int_via_signed:
  fixes mask
  assumes mask_def: "mask = Bit_Operations.mask (LENGTH('a))"
  and shift_def: "shift = 1 << LENGTH('a)"
  and index_def: "index = LENGTH('a) - 1"
  and overflow_def:"overflow = 1 << (LENGTH('a) - 1)"
  and least_def: "least = - overflow"
  shows
  "(word_of_int i :: 'a :: len word) =
   (let i' = i AND mask
    in if i' !! index then
         if i' - shift < least \<or> overflow \<le> i' - shift then arbitrary1 i' else word_of_int (i' - shift)
       else if i' < least \<or> overflow \<le> i' then arbitrary2 i' else word_of_int i')"
proof -
  define i' where "i' = i AND mask"
  have "shift = mask + 1" unfolding assms by(simp add: bin_mask_p1_conv_shift)
  hence "i' < shift" by(simp add: mask_def i'_def int_and_le)
  show ?thesis
  proof(cases "i' !! index")
    case True
    then have unf: "i' = overflow OR i'"
      apply (simp add: assms i'_def shiftl_eq_push_bit push_bit_of_1 flip: take_bit_eq_mask)
      apply (rule bit_eqI)
      apply (auto simp add: bit_take_bit_iff bit_or_iff bit_exp_iff)
      done
    have "overflow \<le> i'" by(subst unf)(rule le_int_or, simp add: bin_sign_and assms i'_def)
    hence "i' - shift < least \<longleftrightarrow> False" unfolding assms
      by(cases "LENGTH('a)")(simp_all add: not_less)
    moreover
    have "overflow \<le> i' - shift \<longleftrightarrow> False" using \<open>i' < shift\<close> unfolding assms
      by(cases "LENGTH('a)")(auto simp add: not_le elim: less_le_trans)
    moreover
    have "word_of_int (i' - shift) = (word_of_int i :: 'a word)" using \<open>i' < shift\<close>
      by (simp add: i'_def shift_def mask_def shiftl_eq_push_bit push_bit_of_1 word_of_int_eq_iff flip: take_bit_eq_mask)
    ultimately show ?thesis using True by(simp add: Let_def i'_def)
  next
    case False
    hence "i' = i AND Bit_Operations.mask (LENGTH('a) - 1)" unfolding assms i'_def
      by(clarsimp simp add: i'_def bin_nth_ops intro!: bin_eqI)(cases "LENGTH('a)", auto simp add: less_Suc_eq)
    also have "\<dots> \<le> Bit_Operations.mask (LENGTH('a) - 1)" by(rule int_and_le) simp
    also have "\<dots> < overflow" unfolding overflow_def
      by(simp add: bin_mask_p1_conv_shift[symmetric])
    also
    have "least \<le> 0" unfolding least_def overflow_def by simp
    have "0 \<le> i'" by (simp add: i'_def mask_def)
    hence "least \<le> i'" using \<open>least \<le> 0\<close> by simp
    moreover
    have "word_of_int i' = (word_of_int i :: 'a word)"
      by(rule word_eqI)(auto simp add: i'_def bin_nth_ops mask_def)
    ultimately show ?thesis using False by(simp add: Let_def i'_def)
  qed
qed



text \<open>Quickcheck conversion functions\<close>

context
  includes state_combinator_syntax
begin

definition qc_random_cnv ::
  "(natural \<Rightarrow> 'a::term_of) \<Rightarrow> natural \<Rightarrow> Random.seed
    \<Rightarrow> ('a \<times> (unit \<Rightarrow> Code_Evaluation.term)) \<times> Random.seed"
  where "qc_random_cnv a_of_natural i = Random.range (i + 1) \<circ>\<rightarrow> (\<lambda>k. Pair (
       let n = a_of_natural k
       in (n, \<lambda>_. Code_Evaluation.term_of n)))"

end

definition qc_exhaustive_cnv :: "(natural \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> (bool \<times> term list) option)
  \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option"
where
  "qc_exhaustive_cnv a_of_natural f d =
   Quickcheck_Exhaustive.exhaustive (%x. f (a_of_natural x)) d"

definition qc_full_exhaustive_cnv ::
  "(natural \<Rightarrow> ('a::term_of)) \<Rightarrow> ('a \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option)
  \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option"
where
  "qc_full_exhaustive_cnv a_of_natural f d = Quickcheck_Exhaustive.full_exhaustive
  (%(x, xt). f (a_of_natural x, %_. Code_Evaluation.term_of (a_of_natural x))) d"

declare [[quickcheck_narrowing_ghc_options = "-XTypeSynonymInstances"]]

definition qc_narrowing_drawn_from :: "'a list \<Rightarrow> integer \<Rightarrow> _"
where
  "qc_narrowing_drawn_from xs =
   foldr Quickcheck_Narrowing.sum (map Quickcheck_Narrowing.cons (butlast xs)) (Quickcheck_Narrowing.cons (last xs))"

locale quickcheck_narrowing_samples =
  fixes a_of_integer :: "integer \<Rightarrow> 'a \<times> 'a :: {partial_term_of, term_of}"
  and zero :: "'a"
  and tr :: "typerep"
begin

function narrowing_samples :: "integer \<Rightarrow> 'a list"
where
  "narrowing_samples i =
   (if i > 0 then let (a, a') = a_of_integer i in narrowing_samples (i - 1) @ [a, a'] else [zero])"
by pat_completeness auto
termination including integer.lifting
proof(relation "measure nat_of_integer")
  fix i :: integer
  assume "0 < i"
  thus "(i - 1, i) \<in> measure nat_of_integer"
    by simp(transfer, simp)
qed simp

definition partial_term_of_sample :: "integer \<Rightarrow> 'a"
where
  "partial_term_of_sample i =
  (if i < 0 then undefined
   else if i = 0 then zero
   else if i mod 2 = 0 then snd (a_of_integer (i div 2))
   else fst (a_of_integer (i div 2 + 1)))"

lemma partial_term_of_code:
  "partial_term_of (ty :: 'a itself) (Quickcheck_Narrowing.Narrowing_variable p t) \<equiv>
    Code_Evaluation.Free (STR ''_'') tr"
  "partial_term_of (ty :: 'a itself) (Quickcheck_Narrowing.Narrowing_constructor i []) \<equiv>
   Code_Evaluation.term_of (partial_term_of_sample i)"
by (rule partial_term_of_anything)+

end

lemmas [code] =
  quickcheck_narrowing_samples.narrowing_samples.simps
  quickcheck_narrowing_samples.partial_term_of_sample_def


text \<open>
  The separate code target \<open>SML_word\<close> collects setups for the
  code generator that PolyML does not provide.
\<close>

setup \<open>Code_Target.add_derived_target ("SML_word", [(Code_ML.target_SML, I)])\<close>

code_identifier code_module Code_Target_Word_Base \<rightharpoonup>
  (SML) Word and (Haskell) Word and (OCaml) Word and (Scala) Word

end
