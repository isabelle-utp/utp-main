(*  Based on HOL/Real_Vector_Spaces.thy by Brian Huffman, Johannes Hölzl
    Adapted to the complex case by Dominique Unruh *)

section \<open>\<open>Complex_Vector_Spaces0\<close> -- Vector Spaces and Algebras over the Complex Numbers\<close>

theory Complex_Vector_Spaces0
  imports HOL.Real_Vector_Spaces HOL.Topological_Spaces HOL.Vector_Spaces
    Complex_Main Jordan_Normal_Form.Conjugate
begin                                   

(* Jordan_Normal_Form.Conjugate declares these as simps. Seems too aggressive to me. *)
declare less_complex_def[simp del]
declare less_eq_complex_def[simp del]

subsection \<open>Complex vector spaces\<close>

class scaleC = scaleR +
  fixes scaleC :: "complex \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "*\<^sub>C" 75)
  assumes scaleR_scaleC: "scaleR r = scaleC (complex_of_real r)"
begin

abbreviation divideC :: "'a \<Rightarrow> complex \<Rightarrow> 'a"  (infixl "'/\<^sub>C" 70)
  where "x /\<^sub>C c \<equiv> inverse c *\<^sub>C x"

end

class complex_vector = scaleC + ab_group_add +
  assumes scaleC_add_right: "a *\<^sub>C (x + y) = (a *\<^sub>C x) + (a *\<^sub>C y)"
    and scaleC_add_left: "(a + b) *\<^sub>C x = (a *\<^sub>C x) + (b *\<^sub>C x)"
    and scaleC_scaleC[simp]: "a *\<^sub>C (b *\<^sub>C x) =  (a * b) *\<^sub>C x"
    and scaleC_one[simp]: "1 *\<^sub>C x = x"

(* Not present in Real_Vector_Spaces *)
subclass (in complex_vector) real_vector
  by (standard, simp_all add: scaleR_scaleC scaleC_add_right scaleC_add_left)

class complex_algebra = complex_vector + ring +
  assumes mult_scaleC_left [simp]: "a *\<^sub>C x * y = a *\<^sub>C (x * y)"
    and mult_scaleC_right [simp]: "x * a *\<^sub>C y = a *\<^sub>C (x * y)"

(* Not present in Real_Vector_Spaces *)
subclass (in complex_algebra) real_algebra
  by (standard, simp_all add: scaleR_scaleC)

class complex_algebra_1 = complex_algebra + ring_1

(* Not present in Real_Vector_Spaces *)
subclass (in complex_algebra_1) real_algebra_1 ..

class complex_div_algebra = complex_algebra_1 + division_ring

(* Not present in Real_Vector_Spaces *)
subclass (in complex_div_algebra) real_div_algebra ..

class complex_field = complex_div_algebra + field

(* Not present in Real_Vector_Spaces *)
subclass (in complex_field) real_field ..

instantiation complex :: complex_field
begin

definition complex_scaleC_def [simp]: "scaleC a x = a * x"

instance
proof intro_classes
  fix r :: real and a b x y :: complex
  show "((*\<^sub>R) r::complex \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)"
    by (auto simp add: scaleR_conv_of_real)
  show "a *\<^sub>C (x + y) = a *\<^sub>C x + a *\<^sub>C y"
    by (simp add: ring_class.ring_distribs(1))
  show "(a + b) *\<^sub>C x = a *\<^sub>C x + b *\<^sub>C x"
    by (simp add: algebra_simps)
  show "a *\<^sub>C b *\<^sub>C x = (a * b) *\<^sub>C x"
    by simp
  show "1 *\<^sub>C x = x"
    by simp
  show "a *\<^sub>C (x::complex) * y = a *\<^sub>C (x * y)"
    by simp
  show "(x::complex) * a *\<^sub>C y = a *\<^sub>C (x * y)"
    by simp
qed

end

locale clinear = Vector_Spaces.linear "scaleC::_\<Rightarrow>_\<Rightarrow>'a::complex_vector" "scaleC::_\<Rightarrow>_\<Rightarrow>'b::complex_vector"
begin

lemmas scaleC = scale

end

global_interpretation complex_vector: vector_space "scaleC :: complex \<Rightarrow> 'a \<Rightarrow> 'a :: complex_vector"
  rewrites "Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) = clinear"
    and "Vector_Spaces.linear (*) (*\<^sub>C) = clinear"
  defines cdependent_raw_def: cdependent = complex_vector.dependent
    and crepresentation_raw_def: crepresentation = complex_vector.representation
    and csubspace_raw_def: csubspace = complex_vector.subspace
    and cspan_raw_def: cspan = complex_vector.span
    and cextend_basis_raw_def: cextend_basis = complex_vector.extend_basis
    and cdim_raw_def: cdim = complex_vector.dim
proof unfold_locales
  show "Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) = clinear" "Vector_Spaces.linear (*) (*\<^sub>C) = clinear"
    by (force simp: clinear_def complex_scaleC_def[abs_def])+
qed (use scaleC_add_right scaleC_add_left in auto)


(* Not needed since we did the global_interpretation with mandatory complex_vector-prefix:
hide_const (open)\<comment> \<open>locale constants\<close>
  complex_vector.dependent
  complex_vector.independent
  complex_vector.representation
  complex_vector.subspace
  complex_vector.span
  complex_vector.extend_basis
  complex_vector.dim *)

abbreviation "cindependent x \<equiv> \<not> cdependent x"

global_interpretation complex_vector: vector_space_pair "scaleC::_\<Rightarrow>_\<Rightarrow>'a::complex_vector" "scaleC::_\<Rightarrow>_\<Rightarrow>'b::complex_vector"
  rewrites  "Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) = clinear"
    and "Vector_Spaces.linear (*) (*\<^sub>C) = clinear"
  defines cconstruct_raw_def: cconstruct = complex_vector.construct
proof unfold_locales
  show "Vector_Spaces.linear (*) (*\<^sub>C) = clinear"
    unfolding clinear_def complex_scaleC_def by auto
qed (auto simp: clinear_def)

(* Not needed since we did the global_interpretation with mandatory complex_vector-prefix:
hide_const (open)\<comment> \<open>locale constants\<close>
  complex_vector.construct *)

lemma clinear_compose: "clinear f \<Longrightarrow> clinear g \<Longrightarrow> clinear (g \<circ> f)"
  unfolding clinear_def by (rule Vector_Spaces.linear_compose)

text \<open>Recover original theorem names\<close>

lemmas scaleC_left_commute = complex_vector.scale_left_commute
lemmas scaleC_zero_left = complex_vector.scale_zero_left
lemmas scaleC_minus_left = complex_vector.scale_minus_left
lemmas scaleC_diff_left = complex_vector.scale_left_diff_distrib
lemmas scaleC_sum_left = complex_vector.scale_sum_left
lemmas scaleC_zero_right = complex_vector.scale_zero_right
lemmas scaleC_minus_right = complex_vector.scale_minus_right
lemmas scaleC_diff_right = complex_vector.scale_right_diff_distrib
lemmas scaleC_sum_right = complex_vector.scale_sum_right
lemmas scaleC_eq_0_iff = complex_vector.scale_eq_0_iff
lemmas scaleC_left_imp_eq = complex_vector.scale_left_imp_eq
lemmas scaleC_right_imp_eq = complex_vector.scale_right_imp_eq
lemmas scaleC_cancel_left = complex_vector.scale_cancel_left
lemmas scaleC_cancel_right = complex_vector.scale_cancel_right

lemma divideC_field_simps[field_simps]: (* In Real_Vector_Spaces, these lemmas are unnamed *)
  "c \<noteq> 0 \<Longrightarrow> a = b /\<^sub>C c \<longleftrightarrow> c *\<^sub>C a = b"
  "c \<noteq> 0 \<Longrightarrow> b /\<^sub>C c = a \<longleftrightarrow> b = c *\<^sub>C a"
  "c \<noteq> 0 \<Longrightarrow> a + b /\<^sub>C c = (c *\<^sub>C a + b) /\<^sub>C c"
  "c \<noteq> 0 \<Longrightarrow> a /\<^sub>C c + b = (a + c *\<^sub>C b) /\<^sub>C c"
  "c \<noteq> 0 \<Longrightarrow> a - b /\<^sub>C c = (c *\<^sub>C a - b) /\<^sub>C c"
  "c \<noteq> 0 \<Longrightarrow> a /\<^sub>C c - b = (a - c *\<^sub>C b) /\<^sub>C c"
  "c \<noteq> 0 \<Longrightarrow> - (a /\<^sub>C c) + b = (- a + c *\<^sub>C b) /\<^sub>C c"
  "c \<noteq> 0 \<Longrightarrow> - (a /\<^sub>C c) - b = (- a - c *\<^sub>C b) /\<^sub>C c"
  for a b :: "'a :: complex_vector"
  by (auto simp add: scaleC_add_right scaleC_add_left scaleC_diff_right scaleC_diff_left)


text \<open>Legacy names -- omitted\<close>

(* lemmas scaleC_left_distrib = scaleC_add_left
lemmas scaleC_right_distrib = scaleC_add_right
lemmas scaleC_left_diff_distrib = scaleC_diff_left
lemmas scaleC_right_diff_distrib = scaleC_diff_right *)

lemmas clinear_injective_0 = linear_inj_iff_eq_0
  and clinear_injective_on_subspace_0 = linear_inj_on_iff_eq_0
  and clinear_cmul = linear_scale
  and clinear_scaleC = linear_scale_self
  and csubspace_mul = subspace_scale
  and cspan_linear_image = linear_span_image
  and cspan_0 = span_zero
  and cspan_mul = span_scale
  and injective_scaleC = injective_scale

lemma scaleC_minus1_left [simp]: "scaleC (-1) x = - x"
  for x :: "'a::complex_vector"
  using scaleC_minus_left [of 1 x] by simp

lemma scaleC_2:
  fixes x :: "'a::complex_vector"
  shows "scaleC 2 x = x + x"
  unfolding one_add_one [symmetric] scaleC_add_left by simp

lemma scaleC_half_double [simp]:
  fixes a :: "'a::complex_vector"
  shows "(1 / 2) *\<^sub>C (a + a) = a"
proof -
  have "\<And>r. r *\<^sub>C (a + a) = (r * 2) *\<^sub>C a"
    by (metis scaleC_2 scaleC_scaleC)
  thus ?thesis
    by simp
qed

lemma clinear_scale_complex:
  fixes c::complex shows "clinear f \<Longrightarrow> f (c * b) = c * f b"
  using complex_vector.linear_scale by fastforce


interpretation scaleC_left: additive "(\<lambda>a. scaleC a x :: 'a::complex_vector)"
  by standard (rule scaleC_add_left)

interpretation scaleC_right: additive "(\<lambda>x. scaleC a x :: 'a::complex_vector)"
  by standard (rule scaleC_add_right)

lemma nonzero_inverse_scaleC_distrib:
  "a \<noteq> 0 \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> inverse (scaleC a x) = scaleC (inverse a) (inverse x)"
  for x :: "'a::complex_div_algebra"
  by (rule inverse_unique) simp

lemma inverse_scaleC_distrib: "inverse (scaleC a x) = scaleC (inverse a) (inverse x)"
  for x :: "'a::{complex_div_algebra,division_ring}"
  by (metis inverse_zero nonzero_inverse_scaleC_distrib complex_vector.scale_eq_0_iff)

(* lemmas sum_constant_scaleC = real_vector.sum_constant_scale\<comment> \<open>legacy name\<close> *)

(* Defined in Real_Vector_Spaces:
named_theorems vector_add_divide_simps "to simplify sums of scaled vectors" *)

lemma complex_add_divide_simps[vector_add_divide_simps]:  (* In Real_Vector_Spaces, these lemmas are unnamed *)
  "v + (b / z) *\<^sub>C w = (if z = 0 then v else (z *\<^sub>C v + b *\<^sub>C w) /\<^sub>C z)"
  "a *\<^sub>C v + (b / z) *\<^sub>C w = (if z = 0 then a *\<^sub>C v else ((a * z) *\<^sub>C v + b *\<^sub>C w) /\<^sub>C z)"
  "(a / z) *\<^sub>C v + w = (if z = 0 then w else (a *\<^sub>C v + z *\<^sub>C w) /\<^sub>C z)"
  "(a / z) *\<^sub>C v + b *\<^sub>C w = (if z = 0 then b *\<^sub>C w else (a *\<^sub>C v + (b * z) *\<^sub>C w) /\<^sub>C z)"
  "v - (b / z) *\<^sub>C w = (if z = 0 then v else (z *\<^sub>C v - b *\<^sub>C w) /\<^sub>C z)"
  "a *\<^sub>C v - (b / z) *\<^sub>C w = (if z = 0 then a *\<^sub>C v else ((a * z) *\<^sub>C v - b *\<^sub>C w) /\<^sub>C z)"
  "(a / z) *\<^sub>C v - w = (if z = 0 then -w else (a *\<^sub>C v - z *\<^sub>C w) /\<^sub>C z)"
  "(a / z) *\<^sub>C v - b *\<^sub>C w = (if z = 0 then -b *\<^sub>C w else (a *\<^sub>C v - (b * z) *\<^sub>C w) /\<^sub>C z)"
  for v :: "'a :: complex_vector"
  by (simp_all add: divide_inverse_commute scaleC_add_right scaleC_diff_right)

lemma ceq_vector_fraction_iff [vector_add_divide_simps]:
  fixes x :: "'a :: complex_vector"
  shows "(x = (u / v) *\<^sub>C a) \<longleftrightarrow> (if v=0 then x = 0 else v *\<^sub>C x = u *\<^sub>C a)"
  by auto (metis (no_types) divide_eq_1_iff divide_inverse_commute scaleC_one scaleC_scaleC)

lemma cvector_fraction_eq_iff [vector_add_divide_simps]:
  fixes x :: "'a :: complex_vector"
  shows "((u / v) *\<^sub>C a = x) \<longleftrightarrow> (if v=0 then x = 0 else u *\<^sub>C a = v *\<^sub>C x)"
  by (metis ceq_vector_fraction_iff)

lemma complex_vector_affinity_eq:
  fixes x :: "'a :: complex_vector"
  assumes m0: "m \<noteq> 0"
  shows "m *\<^sub>C x + c = y \<longleftrightarrow> x = inverse m *\<^sub>C y - (inverse m *\<^sub>C c)"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  hence "m *\<^sub>C x = y - c" by (simp add: field_simps)
  hence "inverse m *\<^sub>C (m *\<^sub>C x) = inverse m *\<^sub>C (y - c)" by simp
  thus "x = inverse m *\<^sub>C y - (inverse m *\<^sub>C c)"
    using m0
    by (simp add: complex_vector.scale_right_diff_distrib)
next
  assume ?rhs
  with m0 show "m *\<^sub>C x + c = y"
    by (simp add: complex_vector.scale_right_diff_distrib)
qed

lemma complex_vector_eq_affinity: "m \<noteq> 0 \<Longrightarrow> y = m *\<^sub>C x + c \<longleftrightarrow> inverse m *\<^sub>C y - (inverse m *\<^sub>C c) = x"
  for x :: "'a::complex_vector"
  using complex_vector_affinity_eq[where m=m and x=x and y=y and c=c]
  by metis

lemma scaleC_eq_iff [simp]: "b + u *\<^sub>C a = a + u *\<^sub>C b \<longleftrightarrow> a = b \<or> u = 1"
  for a :: "'a::complex_vector"
proof (cases "u = 1")
  case True
  thus ?thesis by auto
next
  case False
  have "a = b" if "b + u *\<^sub>C a = a + u *\<^sub>C b"
  proof -
    from that have "(u - 1) *\<^sub>C a = (u - 1) *\<^sub>C b"
      by (simp add: algebra_simps)
    with False show ?thesis
      by auto
  qed
  thus ?thesis by auto
qed

lemma scaleC_collapse [simp]: "(1 - u) *\<^sub>C a + u *\<^sub>C a = a"
  for a :: "'a::complex_vector"
  by (simp add: algebra_simps)

subsection \<open>Embedding of the Complex Numbers into any \<open>complex_algebra_1\<close>: \<open>of_complex\<close>\<close>


definition of_complex :: "complex \<Rightarrow> 'a::complex_algebra_1"
  where "of_complex c = scaleC c 1"


lemma scaleC_conv_of_complex: "scaleC r x = of_complex r * x"
  by (simp add: of_complex_def)

lemma of_complex_0 [simp]: "of_complex 0 = 0"
  by (simp add: of_complex_def)

lemma of_complex_1 [simp]: "of_complex 1 = 1"
  by (simp add: of_complex_def)

lemma of_complex_add [simp]: "of_complex (x + y) = of_complex x + of_complex y"
  by (simp add: of_complex_def scaleC_add_left)

lemma of_complex_minus [simp]: "of_complex (- x) = - of_complex x"
  by (simp add: of_complex_def)

lemma of_complex_diff [simp]: "of_complex (x - y) = of_complex x - of_complex y"
  by (simp add: of_complex_def scaleC_diff_left)

lemma of_complex_mult [simp]: "of_complex (x * y) = of_complex x * of_complex y"
  by (simp add: of_complex_def mult.commute)

lemma of_complex_sum[simp]: "of_complex (sum f s) = (\<Sum>x\<in>s. of_complex (f x))"
  by (induct s rule: infinite_finite_induct) auto

lemma of_complex_prod[simp]: "of_complex (prod f s) = (\<Prod>x\<in>s. of_complex (f x))"
  by (induct s rule: infinite_finite_induct) auto

lemma nonzero_of_complex_inverse:
  "x \<noteq> 0 \<Longrightarrow> of_complex (inverse x) = inverse (of_complex x :: 'a::complex_div_algebra)"
  by (simp add: of_complex_def nonzero_inverse_scaleC_distrib)

lemma of_complex_inverse [simp]:
  "of_complex (inverse x) = inverse (of_complex x :: 'a::{complex_div_algebra,division_ring})"
  by (simp add: of_complex_def inverse_scaleC_distrib)

lemma nonzero_of_complex_divide:
  "y \<noteq> 0 \<Longrightarrow> of_complex (x / y) = (of_complex x / of_complex y :: 'a::complex_field)"
  by (simp add: divide_inverse nonzero_of_complex_inverse)

lemma of_complex_divide [simp]:
  "of_complex (x / y) = (of_complex x / of_complex y :: 'a::complex_div_algebra)"
  by (simp add: divide_inverse)

lemma of_complex_power [simp]:
  "of_complex (x ^ n) = (of_complex x :: 'a::{complex_algebra_1}) ^ n"
  by (induct n) simp_all

lemma of_complex_power_int [simp]:
  "of_complex (power_int x n) = power_int (of_complex x :: 'a :: {complex_div_algebra,division_ring}) n"
  by (auto simp: power_int_def)

lemma of_complex_eq_iff [simp]: "of_complex x = of_complex y \<longleftrightarrow> x = y"
  by (simp add: of_complex_def)

lemma inj_of_complex: "inj of_complex"
  by (auto intro: injI)

lemmas of_complex_eq_0_iff [simp] = of_complex_eq_iff [of _ 0, simplified]
lemmas of_complex_eq_1_iff [simp] = of_complex_eq_iff [of _ 1, simplified]

lemma minus_of_complex_eq_of_complex_iff [simp]: "-of_complex x = of_complex y \<longleftrightarrow> -x = y"
  using of_complex_eq_iff[of "-x" y] by (simp only: of_complex_minus)

lemma of_complex_eq_minus_of_complex_iff [simp]: "of_complex x = -of_complex y \<longleftrightarrow> x = -y"
  using of_complex_eq_iff[of x "-y"] by (simp only: of_complex_minus)

lemma of_complex_eq_id [simp]: "of_complex = (id :: complex \<Rightarrow> complex)"
  by (rule ext) (simp add: of_complex_def)

text \<open>Collapse nested embeddings.\<close>
lemma of_complex_of_nat_eq [simp]: "of_complex (of_nat n) = of_nat n"
  by (induct n) auto

lemma of_complex_of_int_eq [simp]: "of_complex (of_int z) = of_int z"
  by (cases z rule: int_diff_cases) simp

lemma of_complex_numeral [simp]: "of_complex (numeral w) = numeral w"
  using of_complex_of_int_eq [of "numeral w"] by simp

lemma of_complex_neg_numeral [simp]: "of_complex (- numeral w) = - numeral w"
  using of_complex_of_int_eq [of "- numeral w"] by simp

lemma numeral_power_int_eq_of_complex_cancel_iff [simp]:
  "power_int (numeral x) n = (of_complex y :: 'a :: {complex_div_algebra, division_ring}) \<longleftrightarrow>
     power_int (numeral x) n = y"
proof -
  have "power_int (numeral x) n = (of_complex (power_int (numeral x) n) :: 'a)"
    by simp
  also have "\<dots> = of_complex y \<longleftrightarrow> power_int (numeral x) n = y"
    by (subst of_complex_eq_iff) auto
  finally show ?thesis .
qed

lemma of_complex_eq_numeral_power_int_cancel_iff [simp]:
  "(of_complex y :: 'a :: {complex_div_algebra, division_ring}) = power_int (numeral x) n \<longleftrightarrow>
     y = power_int (numeral x) n"
  by (subst (1 2) eq_commute) simp

lemma of_complex_eq_of_complex_power_int_cancel_iff [simp]:
  "power_int (of_complex b :: 'a :: {complex_div_algebra, division_ring}) w = of_complex x \<longleftrightarrow>
     power_int b w = x"
  by (metis of_complex_power_int of_complex_eq_iff)

lemma of_complex_in_Ints_iff [simp]: "of_complex x \<in> \<int> \<longleftrightarrow> x \<in> \<int>"
proof safe
  fix x assume "(of_complex x :: 'a) \<in> \<int>"
  then obtain n where "(of_complex x :: 'a) = of_int n"
    by (auto simp: Ints_def)
  also have "of_int n = of_complex (of_int n)"
    by simp
  finally have "x = of_int n"
    by (subst (asm) of_complex_eq_iff)
  thus "x \<in> \<int>"
    by auto
qed (auto simp: Ints_def)

lemma Ints_of_complex [intro]: "x \<in> \<int> \<Longrightarrow> of_complex x \<in> \<int>"
  by simp


text \<open>Every complex algebra has characteristic zero.\<close>

(* Inherited from real_algebra_1 *)
(* instance complex_algebra_1 < ring_char_0 .. *)

lemma fraction_scaleC_times [simp]:
  fixes a :: "'a::complex_algebra_1"
  shows "(numeral u / numeral v) *\<^sub>C (numeral w * a) = (numeral u * numeral w / numeral v) *\<^sub>C a"
  by (metis (no_types, lifting) of_complex_numeral scaleC_conv_of_complex scaleC_scaleC times_divide_eq_left)

lemma inverse_scaleC_times [simp]:
  fixes a :: "'a::complex_algebra_1"
  shows "(1 / numeral v) *\<^sub>C (numeral w * a) = (numeral w / numeral v) *\<^sub>C a"
  by (metis divide_inverse_commute inverse_eq_divide of_complex_numeral scaleC_conv_of_complex scaleC_scaleC)

lemma scaleC_times [simp]:
  fixes a :: "'a::complex_algebra_1"
  shows "(numeral u) *\<^sub>C (numeral w * a) = (numeral u * numeral w) *\<^sub>C a"
  by (simp add: scaleC_conv_of_complex)

(* Inherited from real_field *)
(* instance complex_field < field_char_0 .. *)


subsection \<open>The Set of Real Numbers\<close>

definition Complexs :: "'a::complex_algebra_1 set"  ("\<complex>")
  where "\<complex> = range of_complex"

lemma Complexs_of_complex [simp]: "of_complex r \<in> \<complex>"
  by (simp add: Complexs_def)

lemma Complexs_of_int [simp]: "of_int z \<in> \<complex>"
  by (subst of_complex_of_int_eq [symmetric], rule Complexs_of_complex)

lemma Complexs_of_nat [simp]: "of_nat n \<in> \<complex>"
  by (subst of_complex_of_nat_eq [symmetric], rule Complexs_of_complex)

lemma Complexs_numeral [simp]: "numeral w \<in> \<complex>"
  by (subst of_complex_numeral [symmetric], rule Complexs_of_complex)

lemma Complexs_0 [simp]: "0 \<in> \<complex>" and Complexs_1 [simp]: "1 \<in> \<complex>"
  by (simp_all add: Complexs_def)

lemma Complexs_add [simp]: "a \<in> \<complex> \<Longrightarrow> b \<in> \<complex> \<Longrightarrow> a + b \<in> \<complex>"
  apply (auto simp add: Complexs_def)
  by (metis of_complex_add range_eqI) 

lemma Complexs_minus [simp]: "a \<in> \<complex> \<Longrightarrow> - a \<in> \<complex>"
  by (auto simp: Complexs_def)

lemma Complexs_minus_iff [simp]: "- a \<in> \<complex> \<longleftrightarrow> a \<in> \<complex>"
  using Complexs_minus by fastforce

lemma Complexs_diff [simp]: "a \<in> \<complex> \<Longrightarrow> b \<in> \<complex> \<Longrightarrow> a - b \<in> \<complex>"
  by (metis Complexs_add Complexs_minus_iff add_uminus_conv_diff)

lemma Complexs_mult [simp]: "a \<in> \<complex> \<Longrightarrow> b \<in> \<complex> \<Longrightarrow> a * b \<in> \<complex>"
  apply (auto simp add: Complexs_def)
  by (metis of_complex_mult rangeI)

lemma nonzero_Complexs_inverse: "a \<in> \<complex> \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> inverse a \<in> \<complex>"
  for a :: "'a::complex_div_algebra"
  apply (auto simp add: Complexs_def)
  by (metis of_complex_inverse range_eqI) 

lemma Complexs_inverse: "a \<in> \<complex> \<Longrightarrow> inverse a \<in> \<complex>"
  for a :: "'a::{complex_div_algebra,division_ring}"
  using nonzero_Complexs_inverse by fastforce

lemma Complexs_inverse_iff [simp]: "inverse x \<in> \<complex> \<longleftrightarrow> x \<in> \<complex>"
  for x :: "'a::{complex_div_algebra,division_ring}"
  by (metis Complexs_inverse inverse_inverse_eq)

lemma nonzero_Complexs_divide: "a \<in> \<complex> \<Longrightarrow> b \<in> \<complex> \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> a / b \<in> \<complex>"
  for a b :: "'a::complex_field"
  by (simp add: divide_inverse)

lemma Complexs_divide [simp]: "a \<in> \<complex> \<Longrightarrow> b \<in> \<complex> \<Longrightarrow> a / b \<in> \<complex>"
  for a b :: "'a::{complex_field,field}"
  using nonzero_Complexs_divide by fastforce

lemma Complexs_power [simp]: "a \<in> \<complex> \<Longrightarrow> a ^ n \<in> \<complex>"
  for a :: "'a::complex_algebra_1"
  apply (auto simp add: Complexs_def)
  by (metis range_eqI of_complex_power[symmetric])

lemma Complexs_cases [cases set: Complexs]:
  assumes "q \<in> \<complex>"
  obtains (of_complex) c where "q = of_complex c"
  unfolding Complexs_def
proof -
  from \<open>q \<in> \<complex>\<close> have "q \<in> range of_complex" unfolding Complexs_def .
  then obtain c where "q = of_complex c" ..
  then show thesis ..
qed

lemma sum_in_Complexs [intro,simp]: "(\<And>i. i \<in> s \<Longrightarrow> f i \<in> \<complex>) \<Longrightarrow> sum f s \<in> \<complex>"
proof (induct s rule: infinite_finite_induct)
  case infinite
  then show ?case by (metis Complexs_0 sum.infinite)
qed simp_all

lemma prod_in_Complexs [intro,simp]: "(\<And>i. i \<in> s \<Longrightarrow> f i \<in> \<complex>) \<Longrightarrow> prod f s \<in> \<complex>"
proof (induct s rule: infinite_finite_induct)
  case infinite
  then show ?case by (metis Complexs_1 prod.infinite)
qed simp_all

lemma Complexs_induct [case_names of_complex, induct set: Complexs]:
  "q \<in> \<complex> \<Longrightarrow> (\<And>r. P (of_complex r)) \<Longrightarrow> P q"
  by (rule Complexs_cases) auto



subsection \<open>Ordered complex vector spaces\<close>

class ordered_complex_vector = complex_vector + ordered_ab_group_add +
  assumes scaleC_left_mono: "x \<le> y \<Longrightarrow> 0 \<le> a \<Longrightarrow> a *\<^sub>C x \<le> a *\<^sub>C y"
    and scaleC_right_mono: "a \<le> b \<Longrightarrow> 0 \<le> x \<Longrightarrow> a *\<^sub>C x \<le> b *\<^sub>C x"
begin

subclass (in ordered_complex_vector) ordered_real_vector
  apply standard
  by (auto simp add: less_eq_complex_def scaleC_left_mono scaleC_right_mono scaleR_scaleC)

lemma scaleC_mono:
  "a \<le> b \<Longrightarrow> x \<le> y \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> x \<Longrightarrow> a *\<^sub>C x \<le> b *\<^sub>C y"
  by (meson order_trans scaleC_left_mono scaleC_right_mono)

lemma scaleC_mono':
  "a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> 0 \<le> a \<Longrightarrow> 0 \<le> c \<Longrightarrow> a *\<^sub>C c \<le> b *\<^sub>C d"
  by (rule scaleC_mono) (auto intro: order.trans)

lemma pos_le_divideC_eq [field_simps]:
  "a \<le> b /\<^sub>C c \<longleftrightarrow> c *\<^sub>C a \<le> b" (is "?P \<longleftrightarrow> ?Q") if "0 < c"
proof
  assume ?P
  with scaleC_left_mono that have "c *\<^sub>C a \<le> c *\<^sub>C (b /\<^sub>C c)"
    using preorder_class.less_imp_le by blast
  with that show ?Q
    by auto
next
  assume ?Q
  with scaleC_left_mono that have "c *\<^sub>C a /\<^sub>C c \<le> b /\<^sub>C c"
    using less_complex_def less_eq_complex_def by fastforce
  with that show ?P
    by auto
qed

lemma pos_less_divideC_eq [field_simps]:
  "a < b /\<^sub>C c \<longleftrightarrow> c *\<^sub>C a < b" if "c > 0"
  using that pos_le_divideC_eq [of c a b]
  by (auto simp add: le_less)

lemma pos_divideC_le_eq [field_simps]:
  "b /\<^sub>C c \<le> a \<longleftrightarrow> b \<le> c *\<^sub>C a" if "c > 0"
  using that pos_le_divideC_eq [of "inverse c" b a]
    less_complex_def by auto

lemma pos_divideC_less_eq [field_simps]:
  "b /\<^sub>C c < a \<longleftrightarrow> b < c *\<^sub>C a" if "c > 0"
  using that pos_less_divideC_eq [of "inverse c" b a]
  by (simp add: local.less_le_not_le local.pos_divideC_le_eq local.pos_le_divideC_eq)

lemma pos_le_minus_divideC_eq [field_simps]:
  "a \<le> - (b /\<^sub>C c) \<longleftrightarrow> c *\<^sub>C a \<le> - b" if "c > 0"
  using that
  by (metis local.ab_left_minus local.add.inverse_unique local.add.right_inverse local.add_minus_cancel local.le_minus_iff local.pos_divideC_le_eq local.scaleC_add_right local.scaleC_one local.scaleC_scaleC)

lemma pos_less_minus_divideC_eq [field_simps]:
  "a < - (b /\<^sub>C c) \<longleftrightarrow> c *\<^sub>C a < - b" if "c > 0"
  using that
  by (metis le_less less_le_not_le pos_divideC_le_eq pos_divideC_less_eq pos_le_minus_divideC_eq)

lemma pos_minus_divideC_le_eq [field_simps]:
  "- (b /\<^sub>C c) \<le> a \<longleftrightarrow> - b \<le> c *\<^sub>C a" if "c > 0"
  using that
  by (metis local.add_minus_cancel local.left_minus local.pos_divideC_le_eq local.scaleC_add_right)

lemma pos_minus_divideC_less_eq [field_simps]:
  "- (b /\<^sub>C c) < a \<longleftrightarrow> - b < c *\<^sub>C a" if "c > 0"
  using that by (simp add: less_le_not_le pos_le_minus_divideC_eq pos_minus_divideC_le_eq) 

lemma scaleC_image_atLeastAtMost: "c > 0 \<Longrightarrow> scaleC c ` {x..y} = {c *\<^sub>C x..c *\<^sub>C y}"
  apply (auto intro!: scaleC_left_mono simp: image_iff Bex_def)
  by (meson local.eq_iff pos_divideC_le_eq pos_le_divideC_eq)

end (* class ordered_complex_vector *)

lemma neg_le_divideC_eq [field_simps]:
  "a \<le> b /\<^sub>C c \<longleftrightarrow> b \<le> c *\<^sub>C a" (is "?P \<longleftrightarrow> ?Q") if "c < 0"
    for a b :: "'a :: ordered_complex_vector"
  using that pos_le_divideC_eq [of "- c" a "- b"]
  by (simp add: less_complex_def)

lemma neg_less_divideC_eq [field_simps]:
  "a < b /\<^sub>C c \<longleftrightarrow> b < c *\<^sub>C a" if "c < 0"
    for a b :: "'a :: ordered_complex_vector"
  using that neg_le_divideC_eq [of c a b]
  by (smt (verit, ccfv_SIG) neg_le_divideC_eq antisym_conv2 complex_vector.scale_minus_right dual_order.strict_implies_order le_less_trans neg_le_iff_le scaleC_scaleC)

lemma neg_divideC_le_eq [field_simps]:
  "b /\<^sub>C c \<le> a \<longleftrightarrow> c *\<^sub>C a \<le> b" if "c < 0"
    for a b :: "'a :: ordered_complex_vector"
  using that pos_divideC_le_eq [of "- c" "- b" a]
  by (simp add: less_complex_def)

lemma neg_divideC_less_eq [field_simps]:
  "b /\<^sub>C c < a \<longleftrightarrow> c *\<^sub>C a < b" if "c < 0"
    for a b :: "'a :: ordered_complex_vector"
  using that neg_divideC_le_eq [of c b a]
  by (meson neg_le_divideC_eq less_le_not_le)

lemma neg_le_minus_divideC_eq [field_simps]:
  "a \<le> - (b /\<^sub>C c) \<longleftrightarrow> - b \<le> c *\<^sub>C a" if "c < 0"
    for a b :: "'a :: ordered_complex_vector"
  using that pos_le_minus_divideC_eq [of "- c" a "- b"]
  by (metis neg_le_divideC_eq complex_vector.scale_minus_right)

lemma neg_less_minus_divideC_eq [field_simps]:
  "a < - (b /\<^sub>C c) \<longleftrightarrow> - b < c *\<^sub>C a" if "c < 0"
    for a b :: "'a :: ordered_complex_vector"
proof -
  have *: "- b = c *\<^sub>C a \<longleftrightarrow> b = - (c *\<^sub>C a)"
    by (metis add.inverse_inverse)
  from that neg_le_minus_divideC_eq [of c a b]
  show ?thesis by (auto simp add: le_less *)
qed

lemma neg_minus_divideC_le_eq [field_simps]:
  "- (b /\<^sub>C c) \<le> a \<longleftrightarrow> c *\<^sub>C a \<le> - b" if "c < 0"
for a b :: "'a :: ordered_complex_vector"
  using that pos_minus_divideC_le_eq [of "- c" "- b" a]
  by (metis Complex_Vector_Spaces0.neg_divideC_le_eq complex_vector.scale_minus_right)

lemma neg_minus_divideC_less_eq [field_simps]:
  "- (b /\<^sub>C c) < a \<longleftrightarrow> c *\<^sub>C a < - b" if "c < 0"
for a b :: "'a :: ordered_complex_vector"
  using that by (simp add: less_le_not_le neg_le_minus_divideC_eq neg_minus_divideC_le_eq)

lemma divideC_field_splits_simps_1 [field_split_simps]: (* In Real_Vector_Spaces, these lemmas are unnamed *)
  "a = b /\<^sub>C c \<longleftrightarrow> (if c = 0 then a = 0 else c *\<^sub>C a = b)"
  "b /\<^sub>C c = a \<longleftrightarrow> (if c = 0 then a = 0 else b = c *\<^sub>C a)"
  "a + b /\<^sub>C c = (if c = 0 then a else (c *\<^sub>C a + b) /\<^sub>C c)"
  "a /\<^sub>C c + b = (if c = 0 then b else (a + c *\<^sub>C b) /\<^sub>C c)"
  "a - b /\<^sub>C c = (if c = 0 then a else (c *\<^sub>C a - b) /\<^sub>C c)"
  "a /\<^sub>C c - b = (if c = 0 then - b else (a - c *\<^sub>C b) /\<^sub>C c)"
  "- (a /\<^sub>C c) + b = (if c = 0 then b else (- a + c *\<^sub>C b) /\<^sub>C c)"
  "- (a /\<^sub>C c) - b = (if c = 0 then - b else (- a - c *\<^sub>C b) /\<^sub>C c)"
  for a b :: "'a :: complex_vector"
  by (auto simp add: field_simps)

lemma divideC_field_splits_simps_2 [field_split_simps]: (* In Real_Vector_Spaces, these lemmas are unnamed *)
  "0 < c \<Longrightarrow> a \<le> b /\<^sub>C c \<longleftrightarrow> (if c > 0 then c *\<^sub>C a \<le> b else if c < 0 then b \<le> c *\<^sub>C a else a \<le> 0)"
  "0 < c \<Longrightarrow> a < b /\<^sub>C c \<longleftrightarrow> (if c > 0 then c *\<^sub>C a < b else if c < 0 then b < c *\<^sub>C a else a < 0)"
  "0 < c \<Longrightarrow> b /\<^sub>C c \<le> a \<longleftrightarrow> (if c > 0 then b \<le> c *\<^sub>C a else if c < 0 then c *\<^sub>C a \<le> b else a \<ge> 0)"
  "0 < c \<Longrightarrow> b /\<^sub>C c < a \<longleftrightarrow> (if c > 0 then b < c *\<^sub>C a else if c < 0 then c *\<^sub>C a < b else a > 0)"
  "0 < c \<Longrightarrow> a \<le> - (b /\<^sub>C c) \<longleftrightarrow> (if c > 0 then c *\<^sub>C a \<le> - b else if c < 0 then - b \<le> c *\<^sub>C a else a \<le> 0)"
  "0 < c \<Longrightarrow> a < - (b /\<^sub>C c) \<longleftrightarrow> (if c > 0 then c *\<^sub>C a < - b else if c < 0 then - b < c *\<^sub>C a else a < 0)"
  "0 < c \<Longrightarrow> - (b /\<^sub>C c) \<le> a \<longleftrightarrow> (if c > 0 then - b \<le> c *\<^sub>C a else if c < 0 then c *\<^sub>C a \<le> - b else a \<ge> 0)"
  "0 < c \<Longrightarrow> - (b /\<^sub>C c) < a \<longleftrightarrow> (if c > 0 then - b < c *\<^sub>C a else if c < 0 then c *\<^sub>C a < - b else a > 0)"
  for a b :: "'a :: ordered_complex_vector"
  by (clarsimp intro!: field_simps)+

lemma scaleC_nonneg_nonneg: "0 \<le> a \<Longrightarrow> 0 \<le> x \<Longrightarrow> 0 \<le> a *\<^sub>C x"
  for x :: "'a::ordered_complex_vector"
  using scaleC_left_mono [of 0 x a] by simp

lemma scaleC_nonneg_nonpos: "0 \<le> a \<Longrightarrow> x \<le> 0 \<Longrightarrow> a *\<^sub>C x \<le> 0"
  for x :: "'a::ordered_complex_vector"
  using scaleC_left_mono [of x 0 a] by simp

lemma scaleC_nonpos_nonneg: "a \<le> 0 \<Longrightarrow> 0 \<le> x \<Longrightarrow> a *\<^sub>C x \<le> 0"
  for x :: "'a::ordered_complex_vector"
  using scaleC_right_mono [of a 0 x] by simp

lemma split_scaleC_neg_le: "(0 \<le> a \<and> x \<le> 0) \<or> (a \<le> 0 \<and> 0 \<le> x) \<Longrightarrow> a *\<^sub>C x \<le> 0"
  for x :: "'a::ordered_complex_vector"
  by (auto simp: scaleC_nonneg_nonpos scaleC_nonpos_nonneg)

lemma cle_add_iff1: "a *\<^sub>C e + c \<le> b *\<^sub>C e + d \<longleftrightarrow> (a - b) *\<^sub>C e + c \<le> d"
  for c d e :: "'a::ordered_complex_vector"
  by (simp add: algebra_simps)

lemma cle_add_iff2: "a *\<^sub>C e + c \<le> b *\<^sub>C e + d \<longleftrightarrow> c \<le> (b - a) *\<^sub>C e + d"
  for c d e :: "'a::ordered_complex_vector"
  by (simp add: algebra_simps)

lemma scaleC_left_mono_neg: "b \<le> a \<Longrightarrow> c \<le> 0 \<Longrightarrow> c *\<^sub>C a \<le> c *\<^sub>C b"
  for a b :: "'a::ordered_complex_vector"
  by (drule scaleC_left_mono [of _ _ "- c"], simp_all add: less_eq_complex_def)

lemma scaleC_right_mono_neg: "b \<le> a \<Longrightarrow> c \<le> 0 \<Longrightarrow> a *\<^sub>C c \<le> b *\<^sub>C c"
  for c :: "'a::ordered_complex_vector"
  by (drule scaleC_right_mono [of _ _ "- c"], simp_all)

lemma scaleC_nonpos_nonpos: "a \<le> 0 \<Longrightarrow> b \<le> 0 \<Longrightarrow> 0 \<le> a *\<^sub>C b"
  for b :: "'a::ordered_complex_vector"
  using scaleC_right_mono_neg [of a 0 b] by simp

lemma split_scaleC_pos_le: "(0 \<le> a \<and> 0 \<le> b) \<or> (a \<le> 0 \<and> b \<le> 0) \<Longrightarrow> 0 \<le> a *\<^sub>C b"
  for b :: "'a::ordered_complex_vector"
  by (auto simp: scaleC_nonneg_nonneg scaleC_nonpos_nonpos)

lemma zero_le_scaleC_iff:
  fixes b :: "'a::ordered_complex_vector"
  assumes "a \<in> \<real>" (* Not present in Real_Vector_Spaces.thy *)
  shows "0 \<le> a *\<^sub>C b \<longleftrightarrow> 0 < a \<and> 0 \<le> b \<or> a < 0 \<and> b \<le> 0 \<or> a = 0"
    (is "?lhs = ?rhs")
proof (cases "a = 0")
  case True
  then show ?thesis by simp
next
  case False
  show ?thesis
  proof
    assume ?lhs
    from \<open>a \<noteq> 0\<close> consider "a > 0" | "a < 0"
      by (metis assms complex_is_Real_iff less_complex_def less_eq_complex_def not_le order.not_eq_order_implies_strict that(1) zero_complex.sel(2))
    then show ?rhs
    proof cases
      case 1
      with \<open>?lhs\<close> have "inverse a *\<^sub>C 0 \<le> inverse a *\<^sub>C (a *\<^sub>C b)"
        by (metis complex_vector.scale_zero_right ordered_complex_vector_class.pos_le_divideC_eq)
      with 1 show ?thesis
        by simp
    next
      case 2
      with \<open>?lhs\<close> have "- inverse a *\<^sub>C 0 \<le> - inverse a *\<^sub>C (a *\<^sub>C b)"
        by (metis Complex_Vector_Spaces0.neg_le_minus_divideC_eq complex_vector.scale_zero_right neg_le_0_iff_le scaleC_left.minus)
      with 2 show ?thesis
        by simp
    qed
  next
    assume ?rhs
    then show ?lhs
      using less_imp_le split_scaleC_pos_le by auto
  qed
qed

lemma scaleC_le_0_iff:
  "a *\<^sub>C b \<le> 0 \<longleftrightarrow> 0 < a \<and> b \<le> 0 \<or> a < 0 \<and> 0 \<le> b \<or> a = 0"
  if "a \<in> \<real>" (* Not present in Real_Vector_Spaces *)
  for b::"'a::ordered_complex_vector"
  apply (insert zero_le_scaleC_iff [of "-a" b])
  using less_complex_def that by force


lemma scaleC_le_cancel_left: "c *\<^sub>C a \<le> c *\<^sub>C b \<longleftrightarrow> (0 < c \<longrightarrow> a \<le> b) \<and> (c < 0 \<longrightarrow> b \<le> a)"
  if "c \<in> \<real>" (* Not present in Real_Vector_Spaces *)
  for b :: "'a::ordered_complex_vector"
  by (smt (verit, ccfv_threshold) Complex_Vector_Spaces0.neg_divideC_le_eq complex_vector.scale_cancel_left complex_vector.scale_zero_right dual_order.eq_iff dual_order.trans ordered_complex_vector_class.pos_le_divideC_eq that zero_le_scaleC_iff)

lemma scaleC_le_cancel_left_pos: "0 < c \<Longrightarrow> c *\<^sub>C a \<le> c *\<^sub>C b \<longleftrightarrow> a \<le> b"
  for b :: "'a::ordered_complex_vector"
  by (simp add: complex_is_Real_iff less_complex_def scaleC_le_cancel_left)

lemma scaleC_le_cancel_left_neg: "c < 0 \<Longrightarrow> c *\<^sub>C a \<le> c *\<^sub>C b \<longleftrightarrow> b \<le> a"
  for b :: "'a::ordered_complex_vector"
  by (simp add: complex_is_Real_iff less_complex_def scaleC_le_cancel_left)

lemma scaleC_left_le_one_le: "0 \<le> x \<Longrightarrow> a \<le> 1 \<Longrightarrow> a *\<^sub>C x \<le> x"
  for x :: "'a::ordered_complex_vector" and a :: complex
  using scaleC_right_mono[of a 1 x] by simp

subsection \<open>Complex normed vector spaces\<close>

(* Classes dist, norm, sgn_div_norm, dist_norm, uniformity_dist
   defined in Real_Vector_Spaces are unchanged in the complex setting.
   No need to define them here. *)

class complex_normed_vector = complex_vector + sgn_div_norm + dist_norm + uniformity_dist + open_uniformity +
  real_normed_vector + (* Not present in Real_Normed_Vector *)
  assumes norm_scaleC [simp]: "norm (scaleC a x) = cmod a * norm x"
begin
(* lemma norm_ge_zero [simp]: "0 \<le> norm x" *) (* Not needed, included from real_normed_vector *)
end

class complex_normed_algebra = complex_algebra + complex_normed_vector +
  real_normed_algebra (* Not present in Real_Normed_Vector *)
  (* assumes norm_mult_ineq: "norm (x * y) \<le> norm x * norm y" *) (* Not needed, included from real_normed_algebra *)

class complex_normed_algebra_1 = complex_algebra_1 + complex_normed_algebra +
  real_normed_algebra_1 (* Not present in Real_Normed_Vector *)
  (* assumes norm_one [simp]: "norm 1 = 1" *) (* Not needed, included from real_normed_algebra_1 *)

lemma (in complex_normed_algebra_1) scaleC_power [simp]: "(scaleC x y) ^ n = scaleC (x^n) (y^n)"
  by (induct n) (simp_all add: mult_ac)

class complex_normed_div_algebra = complex_div_algebra + complex_normed_vector +
  real_normed_div_algebra (* Not present in Real_Normed_Vector *)
  (* assumes norm_mult: "norm (x * y) = norm x * norm y" *) (* Not needed, included from real_normed_div_algebra *)

class complex_normed_field = complex_field + complex_normed_div_algebra

subclass (in complex_normed_field) real_normed_field ..

instance complex_normed_div_algebra < complex_normed_algebra_1 ..

context complex_normed_vector begin
(* Inherited from real_normed_vector:
lemma norm_zero [simp]: "norm (0::'a) = 0"
lemma zero_less_norm_iff [simp]: "norm x > 0 \<longleftrightarrow> x \<noteq> 0"
lemma norm_not_less_zero [simp]: "\<not> norm x < 0"
lemma norm_le_zero_iff [simp]: "norm x \<le> 0 \<longleftrightarrow> x = 0"
lemma norm_minus_cancel [simp]: "norm (- x) = norm x"
lemma norm_minus_commute: "norm (a - b) = norm (b - a)"
lemma dist_add_cancel [simp]: "dist (a + b) (a + c) = dist b c"
lemma dist_add_cancel2 [simp]: "dist (b + a) (c + a) = dist b c"
lemma norm_uminus_minus: "norm (- x - y) = norm (x + y)"
lemma norm_triangle_ineq2: "norm a - norm b \<le> norm (a - b)"
lemma norm_triangle_ineq3: "\<bar>norm a - norm b\<bar> \<le> norm (a - b)"
lemma norm_triangle_ineq4: "norm (a - b) \<le> norm a + norm b"
lemma norm_triangle_le_diff: "norm x + norm y \<le> e \<Longrightarrow> norm (x - y) \<le> e"
lemma norm_diff_ineq: "norm a - norm b \<le> norm (a + b)"
lemma norm_triangle_sub: "norm x \<le> norm y + norm (x - y)"
lemma norm_triangle_le: "norm x + norm y \<le> e \<Longrightarrow> norm (x + y) \<le> e"
lemma norm_triangle_lt: "norm x + norm y < e \<Longrightarrow> norm (x + y) < e"
lemma norm_add_leD: "norm (a + b) \<le> c \<Longrightarrow> norm b \<le> norm a + c"
lemma norm_diff_triangle_ineq: "norm ((a + b) - (c + d)) \<le> norm (a - c) + norm (b - d)"
lemma norm_diff_triangle_le: "norm (x - z) \<le> e1 + e2"
  if "norm (x - y) \<le> e1"  "norm (y - z) \<le> e2"
lemma norm_diff_triangle_less: "norm (x - z) < e1 + e2"
  if "norm (x - y) < e1"  "norm (y - z) < e2"
lemma norm_triangle_mono:
  "norm a \<le> r \<Longrightarrow> norm b \<le> s \<Longrightarrow> norm (a + b) \<le> r + s"
lemma norm_sum: "norm (sum f A) \<le> (\<Sum>i\<in>A. norm (f i))"
  for f::"'b \<Rightarrow> 'a"
lemma sum_norm_le: "norm (sum f S) \<le> sum g S"
  if "\<And>x. x \<in> S \<Longrightarrow> norm (f x) \<le> g x"
  for f::"'b \<Rightarrow> 'a"
lemma abs_norm_cancel [simp]: "\<bar>norm a\<bar> = norm a"
lemma sum_norm_bound:
  "norm (sum f S) \<le> of_nat (card S)*K"
  if "\<And>x. x \<in> S \<Longrightarrow> norm (f x) \<le> K"
  for f :: "'b \<Rightarrow> 'a"
lemma norm_add_less: "norm x < r \<Longrightarrow> norm y < s \<Longrightarrow> norm (x + y) < r + s"
*)
end

lemma dist_scaleC [simp]: "dist (x *\<^sub>C a) (y *\<^sub>C a) = \<bar>x - y\<bar> * norm a"
  for a :: "'a::complex_normed_vector"
  by (metis dist_scaleR scaleR_scaleC)

(* Inherited from real_normed_vector *)
(* lemma norm_mult_less: "norm x < r \<Longrightarrow> norm y < s \<Longrightarrow> norm (x * y) < r * s"
  for x y :: "'a::complex_normed_algebra" *)

lemma norm_of_complex [simp]: "norm (of_complex c :: 'a::complex_normed_algebra_1) = cmod c"
  by (simp add: of_complex_def)

(* Inherited from real_normed_vector:
lemma norm_numeral [simp]: "norm (numeral w::'a::complex_normed_algebra_1) = numeral w"
lemma norm_neg_numeral [simp]: "norm (- numeral w::'a::complex_normed_algebra_1) = numeral w"
lemma norm_of_complex_add1 [simp]: "norm (of_real x + 1 :: 'a :: complex_normed_div_algebra) = \<bar>x + 1\<bar>"
lemma norm_of_complex_addn [simp]:
  "norm (of_real x + numeral b :: 'a :: complex_normed_div_algebra) = \<bar>x + numeral b\<bar>"
lemma norm_of_int [simp]: "norm (of_int z::'a::complex_normed_algebra_1) = \<bar>of_int z\<bar>"
lemma norm_of_nat [simp]: "norm (of_nat n::'a::complex_normed_algebra_1) = of_nat n"
lemma nonzero_norm_inverse: "a \<noteq> 0 \<Longrightarrow> norm (inverse a) = inverse (norm a)"
  for a :: "'a::complex_normed_div_algebra"
lemma norm_inverse: "norm (inverse a) = inverse (norm a)"
  for a :: "'a::{complex_normed_div_algebra,division_ring}"
lemma nonzero_norm_divide: "b \<noteq> 0 \<Longrightarrow> norm (a / b) = norm a / norm b"
  for a b :: "'a::complex_normed_field"
lemma norm_divide: "norm (a / b) = norm a / norm b"
  for a b :: "'a::{complex_normed_field,field}"
lemma norm_inverse_le_norm:
  fixes x :: "'a::complex_normed_div_algebra"
  shows "r \<le> norm x \<Longrightarrow> 0 < r \<Longrightarrow> norm (inverse x) \<le> inverse r"
lemma norm_power_ineq: "norm (x ^ n) \<le> norm x ^ n"
  for x :: "'a::complex_normed_algebra_1"
lemma norm_power: "norm (x ^ n) = norm x ^ n"
  for x :: "'a::complex_normed_div_algebra"
lemma norm_power_int: "norm (power_int x n) = power_int (norm x) n"
  for x :: "'a::complex_normed_div_algebra"
lemma power_eq_imp_eq_norm:
  fixes w :: "'a::complex_normed_div_algebra"
  assumes eq: "w ^ n = z ^ n" and "n > 0"
    shows "norm w = norm z"
lemma power_eq_1_iff:
  fixes w :: "'a::complex_normed_div_algebra"
  shows "w ^ n = 1 \<Longrightarrow> norm w = 1 \<or> n = 0"
lemma norm_mult_numeral1 [simp]: "norm (numeral w * a) = numeral w * norm a"
  for a b :: "'a::{complex_normed_field,field}"
lemma norm_mult_numeral2 [simp]: "norm (a * numeral w) = norm a * numeral w"
  for a b :: "'a::{complex_normed_field,field}"
lemma norm_divide_numeral [simp]: "norm (a / numeral w) = norm a / numeral w"
  for a b :: "'a::{complex_normed_field,field}"
lemma square_norm_one:
  fixes x :: "'a::complex_normed_div_algebra"
  assumes "x\<^sup>2 = 1"
  shows "norm x = 1"
lemma norm_less_p1: "norm x < norm (of_real (norm x) + 1 :: 'a)"
  for x :: "'a::complex_normed_algebra_1"
lemma prod_norm: "prod (\<lambda>x. norm (f x)) A = norm (prod f A)"
  for f :: "'a \<Rightarrow> 'b::{comm_semiring_1,complex_normed_div_algebra}"
lemma norm_prod_le:
  "norm (prod f A) \<le> (\<Prod>a\<in>A. norm (f a :: 'a :: {complex_normed_algebra_1,comm_monoid_mult}))"
lemma norm_prod_diff:
  fixes z w :: "'i \<Rightarrow> 'a::{complex_normed_algebra_1, comm_monoid_mult}"
  shows "(\<And>i. i \<in> I \<Longrightarrow> norm (z i) \<le> 1) \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> norm (w i) \<le> 1) \<Longrightarrow>
    norm ((\<Prod>i\<in>I. z i) - (\<Prod>i\<in>I. w i)) \<le> (\<Sum>i\<in>I. norm (z i - w i))"
lemma norm_power_diff:
  fixes z w :: "'a::{complex_normed_algebra_1, comm_monoid_mult}"
  assumes "norm z \<le> 1" "norm w \<le> 1"
  shows "norm (z^m - w^m) \<le> m * norm (z - w)"
*)

lemma norm_of_complex_add1 [simp]: "norm (of_complex x + 1 :: 'a :: complex_normed_div_algebra) = cmod (x + 1)"
  by (metis norm_of_complex of_complex_1 of_complex_add)

lemma norm_of_complex_addn [simp]:
  "norm (of_complex x + numeral b :: 'a :: complex_normed_div_algebra) = cmod (x + numeral b)"
  by (metis norm_of_complex of_complex_add of_complex_numeral)

lemma norm_of_complex_diff [simp]:
  "norm (of_complex b - of_complex a :: 'a::complex_normed_algebra_1) \<le> cmod (b - a)"
  by (metis norm_of_complex of_complex_diff order_refl)

subsection \<open>Metric spaces\<close>

(* Class metric_space is already defined in Real_Vector_Spaces and does not need changing here *)

text \<open>Every normed vector space is a metric space.\<close>
(* Already follows from complex_normed_vector < real_normed_vector < metric_space *)
(* instance complex_normed_vector < metric_space *)

subsection \<open>Class instances for complex numbers\<close>

instantiation complex :: complex_normed_field
begin

instance
  apply intro_classes
  by (simp add: norm_mult)

end

declare uniformity_Abort[where 'a=complex, code]

lemma dist_of_complex [simp]: "dist (of_complex x :: 'a) (of_complex y) = dist x y"
  for a :: "'a::complex_normed_div_algebra"
  by (metis dist_norm norm_of_complex of_complex_diff)

declare [[code abort: "open :: complex set \<Rightarrow> bool"]]

(* As far as I can tell, there is no analogue to this for complex:
instance real :: order_topology
instance real :: linear_continuum_topology ..

lemmas open_complex_greaterThan = open_greaterThan[where 'a=complex]
lemmas open_complex_lessThan = open_lessThan[where 'a=complex]
lemmas open_complex_greaterThanLessThan = open_greaterThanLessThan[where 'a=complex]
*)

lemma closed_complex_atMost: \<open>closed {..a::complex}\<close>
proof -
  have \<open>{..a} = Im -` {Im a} \<inter> Re -` {..Re a}\<close>
    by (auto simp: less_eq_complex_def)
  also have \<open>closed \<dots>\<close>
    by (auto intro!: closed_Int closed_vimage continuous_on_Im continuous_on_Re)
  finally show ?thesis
    by -
qed

lemma closed_complex_atLeast: \<open>closed {a::complex..}\<close>
proof -
  have \<open>{a..} = Im -` {Im a} \<inter> Re -` {Re a..}\<close>
    by (auto simp: less_eq_complex_def)
  also have \<open>closed \<dots>\<close>
    by (auto intro!: closed_Int closed_vimage continuous_on_Im continuous_on_Re)
  finally show ?thesis
    by -
qed

lemma closed_complex_atLeastAtMost: \<open>closed {a::complex .. b}\<close>
proof (cases \<open>Im a = Im b\<close>)
  case True
  have \<open>{a..b} = Im -` {Im a} \<inter> Re -` {Re a..Re b}\<close>
    by (auto simp add: less_eq_complex_def intro!: True)
  also have \<open>closed \<dots>\<close>
    by (auto intro!: closed_Int closed_vimage continuous_on_Im continuous_on_Re)
  finally show ?thesis
    by -
next
  case False
  then have *: \<open>{a..b} = {}\<close>
    using less_eq_complex_def by auto
  show ?thesis
    by (simp add: *)  
qed

(* As far as I can tell, there is no analogue to this for complex:
instance real :: ordered_real_vector
  by standard (auto intro: mult_left_mono mult_right_mono)
*)

(* subsection \<open>Extra type constraints\<close> *)
(* Everything is commented out, so we comment out the heading, too. *)

(* These are already configured in Real_Vector_Spaces:

text \<open>Only allow \<^term>\<open>open\<close> in class \<open>topological_space\<close>.\<close>
setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>open\<close>, SOME \<^typ>\<open>'a::topological_space set \<Rightarrow> bool\<close>)\<close>

text \<open>Only allow \<^term>\<open>uniformity\<close> in class \<open>uniform_space\<close>.\<close>
setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>uniformity\<close>, SOME \<^typ>\<open>('a::uniformity \<times> 'a) filter\<close>)\<close>

text \<open>Only allow \<^term>\<open>dist\<close> in class \<open>metric_space\<close>.\<close>
setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>dist\<close>, SOME \<^typ>\<open>'a::metric_space \<Rightarrow> 'a \<Rightarrow> real\<close>)\<close>

text \<open>Only allow \<^term>\<open>norm\<close> in class \<open>complex_normed_vector\<close>.\<close>
setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>norm\<close>, SOME \<^typ>\<open>'a::complex_normed_vector \<Rightarrow> real\<close>)\<close>
*)

subsection \<open>Sign function\<close>

(* Inherited from real_normed_vector: 
lemma norm_sgn: "norm (sgn x) = (if x = 0 then 0 else 1)"
  for x :: "'a::complex_normed_vector"
lemma sgn_zero [simp]: "sgn (0::'a::complex_normed_vector) = 0"
lemma sgn_zero_iff: "sgn x = 0 \<longleftrightarrow> x = 0"
  for x :: "'a::complex_normed_vector"
lemma sgn_minus: "sgn (- x) = - sgn x"
  for x :: "'a::complex_normed_vector"
lemma sgn_one [simp]: "sgn (1::'a::complex_normed_algebra_1) = 1"
lemma sgn_mult: "sgn (x * y) = sgn x * sgn y"
  for x y :: "'a::complex_normed_div_algebra"
hide_fact (open) sgn_mult
lemma norm_conv_dist: "norm x = dist x 0"
declare norm_conv_dist [symmetric, simp]
lemma dist_0_norm [simp]: "dist 0 x = norm x"
  for x :: "'a::complex_normed_vector"
lemma dist_diff [simp]: "dist a (a - b) = norm b"  "dist (a - b) a = norm b"
lemma dist_of_int: "dist (of_int m) (of_int n :: 'a :: complex_normed_algebra_1) = of_int \<bar>m - n\<bar>"
lemma dist_of_nat:
  "dist (of_nat m) (of_nat n :: 'a :: complex_normed_algebra_1) = of_int \<bar>int m - int n\<bar>"
*)

lemma sgn_scaleC: "sgn (scaleC r x) = scaleC (sgn r) (sgn x)"
  for x :: "'a::complex_normed_vector"
  by (simp add: scaleR_scaleC sgn_div_norm ac_simps)

lemma sgn_of_complex: "sgn (of_complex r :: 'a::complex_normed_algebra_1) = of_complex (sgn r)"
  unfolding of_complex_def by (simp only: sgn_scaleC sgn_one)

lemma complex_sgn_eq: "sgn x = x / \<bar>x\<bar>"
  for x :: complex
  by (simp add: abs_complex_def scaleR_scaleC sgn_div_norm divide_inverse)

lemma czero_le_sgn_iff [simp]: "0 \<le> sgn x \<longleftrightarrow> 0 \<le> x"
  for x :: complex
  using cmod_eq_Re divide_eq_0_iff less_eq_complex_def by auto

lemma csgn_le_0_iff [simp]: "sgn x \<le> 0 \<longleftrightarrow> x \<le> 0"
  for x :: complex
  by (smt (verit, best) czero_le_sgn_iff Im_sgn Re_sgn divide_eq_0_iff dual_order.eq_iff less_eq_complex_def sgn_zero_iff zero_complex.sel(1) zero_complex.sel(2))


subsection \<open>Bounded Linear and Bilinear Operators\<close>

lemma clinearI: "clinear f"
  if "\<And>b1 b2. f (b1 + b2) = f b1 + f b2"
    "\<And>r b. f (r *\<^sub>C b) = r *\<^sub>C f b"
  using that
  by unfold_locales (auto simp: algebra_simps)

lemma clinear_iff:
  "clinear f \<longleftrightarrow> (\<forall>x y. f (x + y) = f x + f y) \<and> (\<forall>c x. f (c *\<^sub>C x) = c *\<^sub>C f x)"
  (is "clinear f \<longleftrightarrow> ?rhs")
proof
  assume "clinear f"
  then interpret f: clinear f .
  show "?rhs"
    by (simp add: f.add f.scale complex_vector.linear_scale f.clinear_axioms)
next
  assume "?rhs"
  then show "clinear f" by (intro clinearI) auto
qed

lemmas clinear_scaleC_left = complex_vector.linear_scale_left
lemmas clinear_imp_scaleC = complex_vector.linear_imp_scale

corollary complex_clinearD:
  fixes f :: "complex \<Rightarrow> complex"
  assumes "clinear f" obtains c where "f = (*) c"
  by (rule clinear_imp_scaleC [OF assms]) (force simp: scaleC_conv_of_complex)

lemma clinear_times_of_complex: "clinear (\<lambda>x. a * of_complex x)"
  by (auto intro!: clinearI simp: distrib_left)
    (metis mult_scaleC_right scaleC_conv_of_complex)

locale bounded_clinear = clinear f for f :: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector" +
  assumes bounded: "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K"
begin

(* Not present in Real_Vector_Spaces *)
lemma bounded_linear: "bounded_linear f"
  apply standard
  by (simp_all add: add scaleC scaleR_scaleC bounded)

lemma pos_bounded: "\<exists>K>0. \<forall>x. norm (f x) \<le> norm x * K"
proof -
  obtain K where K: "\<And>x. norm (f x) \<le> norm x * K"
    using bounded by blast
  show ?thesis
  proof (intro exI impI conjI allI)
    show "0 < max 1 K"
      by (rule order_less_le_trans [OF zero_less_one max.cobounded1])
  next
    fix x
    have "norm (f x) \<le> norm x * K" using K .
    also have "\<dots> \<le> norm x * max 1 K"
      by (rule mult_left_mono [OF max.cobounded2 norm_ge_zero])
    finally show "norm (f x) \<le> norm x * max 1 K" .
  qed
qed

(* Inherited from bounded_linear *)
lemma nonneg_bounded: "\<exists>K\<ge>0. \<forall>x. norm (f x) \<le> norm x * K"
  by (meson less_imp_le pos_bounded)

lemma clinear: "clinear f"
  by (fact local.clinear_axioms)

end

lemma bounded_clinear_intro:
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>r x. f (scaleC r x) = scaleC r (f x)"
    and "\<And>x. norm (f x) \<le> norm x * K"
  shows "bounded_clinear f"
  by standard (blast intro: assms)+

locale bounded_cbilinear =
  fixes prod :: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector \<Rightarrow> 'c::complex_normed_vector"
    (infixl "**" 70)
  assumes add_left: "prod (a + a') b = prod a b + prod a' b"
    and add_right: "prod a (b + b') = prod a b + prod a b'"
    and scaleC_left: "prod (scaleC r a) b = scaleC r (prod a b)"
    and scaleC_right: "prod a (scaleC r b) = scaleC r (prod a b)"
    and bounded: "\<exists>K. \<forall>a b. norm (prod a b) \<le> norm a * norm b * K"
begin

(* Not present in Real_Vector_Spaces *)
lemma bounded_bilinear[simp]: "bounded_bilinear prod"
  apply standard
  by (auto simp add: add_left add_right scaleR_scaleC scaleC_left scaleC_right bounded)

(* Not present in Real_Vector_Spaces. Has only temporary effect (until "end") *)
interpretation bounded_bilinear prod
  by simp

lemmas pos_bounded = pos_bounded (* "\<exists>K>0. \<forall>a b. norm (a ** b) \<le> norm a * norm b * K" *)
lemmas nonneg_bounded = nonneg_bounded (* "\<exists>K\<ge>0. \<forall>a b. norm (a ** b) \<le> norm a * norm b * K" *)
lemmas additive_right = additive_right (* "additive (\<lambda>b. prod a b)" *)
lemmas additive_left = additive_left (* "additive (\<lambda>a. prod a b)" *)
lemmas zero_left = zero_left (* "prod 0 b = 0" *)
lemmas zero_right = zero_right (* "prod a 0 = 0" *)
lemmas minus_left = minus_left (* "prod (- a) b = - prod a b" *)
lemmas minus_right = minus_right (* "prod a (- b) = - prod a b" *)
lemmas diff_left = diff_left (* "prod (a - a') b = prod a b - prod a' b" *)
lemmas diff_right = diff_right (* "prod a (b - b') = prod a b - prod a b'" *)
lemmas sum_left = sum_left (* "prod (sum g S) x = sum ((\<lambda>i. prod (g i) x)) S" *)
lemmas sum_right = sum_right (* "prod x (sum g S) = sum ((\<lambda>i. (prod x (g i)))) S" *)
lemmas prod_diff_prod = prod_diff_prod (* "(x ** y - a ** b) = (x - a) ** (y - b) + (x - a) ** b + a ** (y - b)" *)

lemma bounded_clinear_left: "bounded_clinear (\<lambda>a. a ** b)"
proof -
  obtain K where "\<And>a b. norm (a ** b) \<le> norm a * norm b * K"
    using pos_bounded by blast
  then show ?thesis
    by (rule_tac K="norm b * K" in bounded_clinear_intro) (auto simp: algebra_simps scaleC_left add_left)
qed

lemma bounded_clinear_right: "bounded_clinear (\<lambda>b. a ** b)"
proof -
  obtain K where "\<And>a b. norm (a ** b) \<le> norm a * norm b * K"
    using pos_bounded by blast
  then show ?thesis
    by (rule_tac K="norm a * K" in bounded_clinear_intro) (auto simp: algebra_simps scaleC_right add_right)
qed

lemma flip: "bounded_cbilinear (\<lambda>x y. y ** x)"
proof
  show "\<exists>K. \<forall>a b. norm (b ** a) \<le> norm a * norm b * K"
    by (metis bounded mult.commute)
qed (simp_all add: add_right add_left scaleC_right scaleC_left)

lemma comp1:
  assumes "bounded_clinear g"
  shows "bounded_cbilinear (\<lambda>x. (**) (g x))"
proof
  interpret g: bounded_clinear g by fact
  show "\<And>a a' b. g (a + a') ** b = g a ** b + g a' ** b"
    "\<And>a b b'. g a ** (b + b') = g a ** b + g a ** b'"
    "\<And>r a b. g (r *\<^sub>C a) ** b = r *\<^sub>C (g a ** b)"
    "\<And>a r b. g a ** (r *\<^sub>C b) = r *\<^sub>C (g a ** b)"
    by (auto simp: g.add add_left add_right g.scaleC scaleC_left scaleC_right)
  have "bounded_bilinear (\<lambda>a b. g a ** b)"
    using g.bounded_linear by (rule comp1)
  then show "\<exists>K. \<forall>a b. norm (g a ** b) \<le> norm a * norm b * K"
    by (rule bounded_bilinear.bounded)
qed

lemma comp: "bounded_clinear f \<Longrightarrow> bounded_clinear g \<Longrightarrow> bounded_cbilinear (\<lambda>x y. f x ** g y)"
  by (rule bounded_cbilinear.flip[OF bounded_cbilinear.comp1[OF bounded_cbilinear.flip[OF comp1]]])

end (* locale bounded_cbilinear *)

lemma bounded_clinear_ident[simp]: "bounded_clinear (\<lambda>x. x)"
  by standard (auto intro!: exI[of _ 1])

lemma bounded_clinear_zero[simp]: "bounded_clinear (\<lambda>x. 0)"
  by standard (auto intro!: exI[of _ 1])

lemma bounded_clinear_add:
  assumes "bounded_clinear f"
    and "bounded_clinear g"
  shows "bounded_clinear (\<lambda>x. f x + g x)"
proof -
  interpret f: bounded_clinear f by fact
  interpret g: bounded_clinear g by fact
  show ?thesis
  proof
    from f.bounded obtain Kf where Kf: "norm (f x) \<le> norm x * Kf" for x
      by blast
    from g.bounded obtain Kg where Kg: "norm (g x) \<le> norm x * Kg" for x
      by blast
    show "\<exists>K. \<forall>x. norm (f x + g x) \<le> norm x * K"
      using add_mono[OF Kf Kg]
      by (intro exI[of _ "Kf + Kg"]) (auto simp: field_simps intro: norm_triangle_ineq order_trans)
  qed (simp_all add: f.add g.add f.scaleC g.scaleC scaleC_add_right)
qed

lemma bounded_clinear_minus:
  assumes "bounded_clinear f"
  shows "bounded_clinear (\<lambda>x. - f x)"
proof -
  interpret f: bounded_clinear f by fact
  show ?thesis
    by unfold_locales (simp_all add: f.add f.scaleC f.bounded)
qed

lemma bounded_clinear_sub: "bounded_clinear f \<Longrightarrow> bounded_clinear g \<Longrightarrow> bounded_clinear (\<lambda>x. f x - g x)"
  using bounded_clinear_add[of f "\<lambda>x. - g x"] bounded_clinear_minus[of g]
  by (auto simp: algebra_simps)

lemma bounded_clinear_sum:
  fixes f :: "'i \<Rightarrow> 'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector"
  shows "(\<And>i. i \<in> I \<Longrightarrow> bounded_clinear (f i)) \<Longrightarrow> bounded_clinear (\<lambda>x. \<Sum>i\<in>I. f i x)"
  by (induct I rule: infinite_finite_induct) (auto intro!: bounded_clinear_add)

lemma bounded_clinear_compose:
  assumes "bounded_clinear f"
    and "bounded_clinear g"
  shows "bounded_clinear (\<lambda>x. f (g x))"
proof
  interpret f: bounded_clinear f by fact
  interpret g: bounded_clinear g by fact
  show "f (g (x + y)) = f (g x) + f (g y)" for x y
    by (simp only: f.add g.add)
  show "f (g (scaleC r x)) = scaleC r (f (g x))" for r x
    by (simp only: f.scaleC g.scaleC)
  from f.pos_bounded obtain Kf where f: "\<And>x. norm (f x) \<le> norm x * Kf" and Kf: "0 < Kf"
    by blast
  from g.pos_bounded obtain Kg where g: "\<And>x. norm (g x) \<le> norm x * Kg"
    by blast
  show "\<exists>K. \<forall>x. norm (f (g x)) \<le> norm x * K"
  proof (intro exI allI)
    fix x
    have "norm (f (g x)) \<le> norm (g x) * Kf"
      using f .
    also have "\<dots> \<le> (norm x * Kg) * Kf"
      using g Kf [THEN order_less_imp_le] by (rule mult_right_mono)
    also have "(norm x * Kg) * Kf = norm x * (Kg * Kf)"
      by (rule mult.assoc)
    finally show "norm (f (g x)) \<le> norm x * (Kg * Kf)" .
  qed
qed

lemma bounded_cbilinear_mult: "bounded_cbilinear ((*) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a::complex_normed_algebra)"
proof (rule bounded_cbilinear.intro)
  show "\<exists>K. \<forall>a b::'a. norm (a * b) \<le> norm a * norm b * K"
    by (rule_tac x=1 in exI) (simp add: norm_mult_ineq)
qed (auto simp: algebra_simps)

lemma bounded_clinear_mult_left: "bounded_clinear (\<lambda>x::'a::complex_normed_algebra. x * y)"
  using bounded_cbilinear_mult
  by (rule bounded_cbilinear.bounded_clinear_left)

lemma bounded_clinear_mult_right: "bounded_clinear (\<lambda>y::'a::complex_normed_algebra. x * y)"
  using bounded_cbilinear_mult
  by (rule bounded_cbilinear.bounded_clinear_right)

lemmas bounded_clinear_mult_const =
  bounded_clinear_mult_left [THEN bounded_clinear_compose]

lemmas bounded_clinear_const_mult =
  bounded_clinear_mult_right [THEN bounded_clinear_compose]

lemma bounded_clinear_divide: "bounded_clinear (\<lambda>x. x / y)"
  for y :: "'a::complex_normed_field"
  unfolding divide_inverse by (rule bounded_clinear_mult_left)

lemma bounded_cbilinear_scaleC: "bounded_cbilinear scaleC"
proof (rule bounded_cbilinear.intro)
  obtain K where K: \<open>\<forall>a (b::'a). norm b \<le> norm b * K\<close>
    using less_eq_real_def by auto
  show "\<exists>K. \<forall>a (b::'a). norm (a *\<^sub>C b) \<le> norm a * norm b * K"
    apply (rule exI[where x=K]) using K
    by (metis norm_scaleC)
qed (auto simp: algebra_simps)

lemma bounded_clinear_scaleC_left: "bounded_clinear (\<lambda>c. scaleC c x)"
  using bounded_cbilinear_scaleC
  by (rule bounded_cbilinear.bounded_clinear_left)

lemma bounded_clinear_scaleC_right: "bounded_clinear (\<lambda>x. scaleC c x)"
  using bounded_cbilinear_scaleC
  by (rule bounded_cbilinear.bounded_clinear_right)

lemmas bounded_clinear_scaleC_const =
  bounded_clinear_scaleC_left[THEN bounded_clinear_compose]

lemmas bounded_clinear_const_scaleC =
  bounded_clinear_scaleC_right[THEN bounded_clinear_compose]

lemma bounded_clinear_of_complex: "bounded_clinear (\<lambda>r. of_complex r)"
  unfolding of_complex_def by (rule bounded_clinear_scaleC_left)

lemma complex_bounded_clinear: "bounded_clinear f \<longleftrightarrow> (\<exists>c::complex. f = (\<lambda>x. x * c))"
  for f :: "complex \<Rightarrow> complex"
proof -
  {
    fix x
    assume "bounded_clinear f"
    then interpret bounded_clinear f .
    from scaleC[of x 1] have "f x = x * f 1"
      by simp
  }
  then show ?thesis
    by (auto intro: exI[of _ "f 1"] bounded_clinear_mult_left)
qed

(* Inherited from real_normed_algebra_1 *)
(* instance complex_normed_algebra_1 \<subseteq> perfect_space *)

(* subsection \<open>Filters and Limits on Metric Space\<close> *)
(* Everything is commented out, so we comment out the heading, too. *)

(* Not specific to real/complex *)
(* lemma (in metric_space) nhds_metric: "nhds x = (INF e\<in>{0 <..}. principal {y. dist y x < e})" *)
(* lemma (in metric_space) tendsto_iff: "(f \<longlongrightarrow> l) F \<longleftrightarrow> (\<forall>e>0. eventually (\<lambda>x. dist (f x) l < e) F)" *)
(* lemma tendsto_dist_iff: "((f \<longlongrightarrow> l) F) \<longleftrightarrow> (((\<lambda>x. dist (f x) l) \<longlongrightarrow> 0) F)" *)
(* lemma (in metric_space) tendstoI [intro?]:
  "(\<And>e. 0 < e \<Longrightarrow> eventually (\<lambda>x. dist (f x) l < e) F) \<Longrightarrow> (f \<longlongrightarrow> l) F" *)
(* lemma (in metric_space) tendstoD: "(f \<longlongrightarrow> l) F \<Longrightarrow> 0 < e \<Longrightarrow> eventually (\<lambda>x. dist (f x) l < e) F" *)
(* lemma (in metric_space) eventually_nhds_metric:
  "eventually P (nhds a) \<longleftrightarrow> (\<exists>d>0. \<forall>x. dist x a < d \<longrightarrow> P x)" *)
(* lemma eventually_at: "eventually P (at a within S) \<longleftrightarrow> (\<exists>d>0. \<forall>x\<in>S. x \<noteq> a \<and> dist x a < d \<longrightarrow> P x)"
  for a :: "'a :: metric_space" *)
(* lemma frequently_at: "frequently P (at a within S) \<longleftrightarrow> (\<forall>d>0. \<exists>x\<in>S. x \<noteq> a \<and> dist x a < d \<and> P x)"
  for a :: "'a :: metric_space" *)
(* lemma eventually_at_le: "eventually P (at a within S) \<longleftrightarrow> (\<exists>d>0. \<forall>x\<in>S. x \<noteq> a \<and> dist x a \<le> d \<longrightarrow> P x)"
  for a :: "'a::metric_space" *)

(* Does not work in complex case because it needs complex :: order_toplogy *)
(* lemma eventually_at_left_real: "a > (b :: real) \<Longrightarrow> eventually (\<lambda>x. x \<in> {b<..<a}) (at_left a)" *)
(* lemma eventually_at_right_real: "a < (b :: real) \<Longrightarrow> eventually (\<lambda>x. x \<in> {a<..<b}) (at_right a)" *)

(* Not specific to real/complex *)
(* lemma metric_tendsto_imp_tendsto:
  fixes a :: "'a :: metric_space"
    and b :: "'b :: metric_space"
  assumes f: "(f \<longlongrightarrow> a) F"
    and le: "eventually (\<lambda>x. dist (g x) b \<le> dist (f x) a) F"
  shows "(g \<longlongrightarrow> b) F" *)

(* Not sure if this makes sense in the complex case *)
(* lemma filterlim_complex_sequentially: "LIM x sequentially. (of_nat x :: complex) :> at_top" *)

(* Not specific to real/complex *)
(* lemma filterlim_nat_sequentially: "filterlim nat sequentially at_top" *)
(* lemma filterlim_floor_sequentially: "filterlim floor at_top at_top" *)

(* Not sure if this makes sense in the complex case *)
(* lemma filterlim_sequentially_iff_filterlim_real:
  "filterlim f sequentially F \<longleftrightarrow> filterlim (\<lambda>x. real (f x)) at_top F" (is "?lhs = ?rhs") *)


subsubsection \<open>Limits of Sequences\<close>

(* Not specific to real/complex *)
(* lemma lim_sequentially: "X \<longlonglongrightarrow> L \<longleftrightarrow> (\<forall>r>0. \<exists>no. \<forall>n\<ge>no. dist (X n) L < r)"
  for L :: "'a::metric_space" *)
(* lemmas LIMSEQ_def = lim_sequentially  (*legacy binding*) *)
(* lemma LIMSEQ_iff_nz: "X \<longlonglongrightarrow> L \<longleftrightarrow> (\<forall>r>0. \<exists>no>0. \<forall>n\<ge>no. dist (X n) L < r)"
  for L :: "'a::metric_space" *)
(* lemma metric_LIMSEQ_I: "(\<And>r. 0 < r \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. dist (X n) L < r) \<Longrightarrow> X \<longlonglongrightarrow> L"
  for L :: "'a::metric_space" *)
(* lemma metric_LIMSEQ_D: "X \<longlonglongrightarrow> L \<Longrightarrow> 0 < r \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. dist (X n) L < r"
  for L :: "'a::metric_space" *)
(* lemma LIMSEQ_norm_0:
  assumes  "\<And>n::nat. norm (f n) < 1 / real (Suc n)"
  shows "f \<longlonglongrightarrow> 0" *)

(* subsubsection \<open>Limits of Functions\<close> *)
(* Everything is commented out, so we comment out the heading, too. *)

(* Not specific to real/complex *)
(* lemma LIM_def: "f \<midarrow>a\<rightarrow> L \<longleftrightarrow> (\<forall>r > 0. \<exists>s > 0. \<forall>x. x \<noteq> a \<and> dist x a < s \<longrightarrow> dist (f x) L < r)"
  for a :: "'a::metric_space" and L :: "'b::metric_space" *)
(* lemma metric_LIM_I:
  "(\<And>r. 0 < r \<Longrightarrow> \<exists>s>0. \<forall>x. x \<noteq> a \<and> dist x a < s \<longrightarrow> dist (f x) L < r) \<Longrightarrow> f \<midarrow>a\<rightarrow> L"
  for a :: "'a::metric_space" and L :: "'b::metric_space" *)
(* lemma metric_LIM_D: "f \<midarrow>a\<rightarrow> L \<Longrightarrow> 0 < r \<Longrightarrow> \<exists>s>0. \<forall>x. x \<noteq> a \<and> dist x a < s \<longrightarrow> dist (f x) L < r"
  for a :: "'a::metric_space" and L :: "'b::metric_space" *)
(* lemma metric_LIM_imp_LIM:
  fixes l :: "'a::metric_space"
    and m :: "'b::metric_space"
  assumes f: "f \<midarrow>a\<rightarrow> l"
    and le: "\<And>x. x \<noteq> a \<Longrightarrow> dist (g x) m \<le> dist (f x) l"
  shows "g \<midarrow>a\<rightarrow> m" *)
(* lemma metric_LIM_equal2:
  fixes a :: "'a::metric_space"
  assumes "g \<midarrow>a\<rightarrow> l" "0 < R"
    and "\<And>x. x \<noteq> a \<Longrightarrow> dist x a < R \<Longrightarrow> f x = g x"
  shows "f \<midarrow>a\<rightarrow> l" *)
(* lemma metric_LIM_compose2:
  fixes a :: "'a::metric_space"
  assumes f: "f \<midarrow>a\<rightarrow> b"
    and g: "g \<midarrow>b\<rightarrow> c"
    and inj: "\<exists>d>0. \<forall>x. x \<noteq> a \<and> dist x a < d \<longrightarrow> f x \<noteq> b"
  shows "(\<lambda>x. g (f x)) \<midarrow>a\<rightarrow> c" *)
(* lemma metric_isCont_LIM_compose2:
  fixes f :: "'a :: metric_space \<Rightarrow> _"
  assumes f [unfolded isCont_def]: "isCont f a"
    and g: "g \<midarrow>f a\<rightarrow> l"
    and inj: "\<exists>d>0. \<forall>x. x \<noteq> a \<and> dist x a < d \<longrightarrow> f x \<noteq> f a"
  shows "(\<lambda>x. g (f x)) \<midarrow>a\<rightarrow> l" *)


(* subsection \<open>Complete metric spaces\<close> *)
(* Everything is commented out, so we comment out the heading, too. *)

subsection \<open>Cauchy sequences\<close>

(* Not specific to real/complex *)
(* lemma (in metric_space) Cauchy_def: "Cauchy X = (\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < e)" *)
(* lemma (in metric_space) Cauchy_altdef: "Cauchy f \<longleftrightarrow> (\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n>m. dist (f m) (f n) < e)" *)
(* lemma (in metric_space) Cauchy_altdef2: "Cauchy s \<longleftrightarrow> (\<forall>e>0. \<exists>N::nat. \<forall>n\<ge>N. dist(s n)(s N) < e)" (is "?lhs = ?rhs") *)
(* lemma (in metric_space) metric_CauchyI:
  "(\<And>e. 0 < e \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < e) \<Longrightarrow> Cauchy X" *)
(* lemma (in metric_space) CauchyI':
  "(\<And>e. 0 < e \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n>m. dist (X m) (X n) < e) \<Longrightarrow> Cauchy X" *)
(* lemma (in metric_space) metric_CauchyD:
  "Cauchy X \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < e" *)
(* lemma (in metric_space) metric_Cauchy_iff2:
  "Cauchy X = (\<forall>j. (\<exists>M. \<forall>m \<ge> M. \<forall>n \<ge> M. dist (X m) (X n) < inverse(real (Suc j))))" *)

lemma cCauchy_iff2: "Cauchy X \<longleftrightarrow> (\<forall>j. (\<exists>M. \<forall>m \<ge> M. \<forall>n \<ge> M. cmod (X m - X n) < inverse (real (Suc j))))"
  by (simp only: metric_Cauchy_iff2 dist_complex_def)

(* Not specific to real/complex *)
(* lemma lim_1_over_n [tendsto_intros]: "((\<lambda>n. 1 / of_nat n) \<longlongrightarrow> (0::'a::complex_normed_field)) sequentially" *)
(* lemma (in metric_space) complete_def:
  shows "complete S = (\<forall>f. (\<forall>n. f n \<in> S) \<and> Cauchy f \<longrightarrow> (\<exists>l\<in>S. f \<longlonglongrightarrow> l))" *)
(* lemma (in metric_space) totally_bounded_metric:
  "totally_bounded S \<longleftrightarrow> (\<forall>e>0. \<exists>k. finite k \<and> S \<subseteq> (\<Union>x\<in>k. {y. dist x y < e}))" *)

(* subsubsection \<open>Cauchy Sequences are Convergent\<close> *)
(* Everything is commented out, so we comment out the heading, too. *)

(* Not specific to real/complex *)
(* class complete_space *)
(* lemma Cauchy_convergent_iff: "Cauchy X \<longleftrightarrow> convergent X"
  for X :: "nat \<Rightarrow> 'a::complete_space" *)

(* text \<open>To prove that a Cauchy sequence converges, it suffices to show that a subsequence converges.\<close> *)

(* Not specific to real/complex *)
(* lemma Cauchy_converges_subseq:
  fixes u::"nat \<Rightarrow> 'a::metric_space"
  assumes "Cauchy u"
    "strict_mono r"
    "(u \<circ> r) \<longlonglongrightarrow> l"
  shows "u \<longlonglongrightarrow> l" *)

subsection \<open>The set of real numbers is a complete metric space\<close>

text \<open>
  Proof that Cauchy sequences converge based on the one from
  \<^url>\<open>http://pirate.shu.edu/~wachsmut/ira/numseq/proofs/cauconv.html\<close>
\<close>

text \<open>
  If sequence \<^term>\<open>X\<close> is Cauchy, then its limit is the lub of
  \<^term>\<open>{r::real. \<exists>N. \<forall>n\<ge>N. r < X n}\<close>
\<close>

lemma complex_increasing_LIMSEQ:
  fixes f :: "nat \<Rightarrow> complex"
  assumes inc: "\<And>n. f n \<le> f (Suc n)"
    and bdd: "\<And>n. f n \<le> l"
    and en: "\<And>e. 0 < e \<Longrightarrow> \<exists>n. l \<le> f n + e"
  shows "f \<longlonglongrightarrow> l"
proof -
  have \<open>(\<lambda>n. Re (f n)) \<longlonglongrightarrow> Re l\<close>
    apply (rule increasing_LIMSEQ)
    using assms apply (auto simp: less_eq_complex_def less_complex_def)
    by (metis Im_complex_of_real Re_complex_of_real)
  moreover have \<open>Im (f n) = Im l\<close> for n
    using bdd by (auto simp: less_eq_complex_def)
  then have \<open>(\<lambda>n. Im (f n)) \<longlonglongrightarrow> Im l\<close>
    by auto
  ultimately show \<open>f \<longlonglongrightarrow> l\<close>
    by (simp add: tendsto_complex_iff)
qed

lemma complex_Cauchy_convergent:
  fixes X :: "nat \<Rightarrow> complex"
  assumes X: "Cauchy X"
  shows "convergent X"
  using assms by (rule Cauchy_convergent)

instance complex :: complete_space
  by intro_classes (rule complex_Cauchy_convergent)

class cbanach = complex_normed_vector + complete_space

(* Not present in Real_Vector_Spaces *)
subclass (in cbanach) banach ..

instance complex :: banach ..

(* Don't know if this holds in the complex case *)
(* lemma tendsto_at_topI_sequentially:
  fixes f :: "complex \<Rightarrow> 'b::first_countable_topology"
  assumes *: "\<And>X. filterlim X at_top sequentially \<Longrightarrow> (\<lambda>n. f (X n)) \<longlonglongrightarrow> y"
  shows "(f \<longlongrightarrow> y) at_top" *)
(* lemma tendsto_at_topI_sequentially_real:
  fixes f :: "real \<Rightarrow> real"
  assumes mono: "mono f"
    and limseq: "(\<lambda>n. f (real n)) \<longlonglongrightarrow> y"
  shows "(f \<longlongrightarrow> y) at_top" *)

end
