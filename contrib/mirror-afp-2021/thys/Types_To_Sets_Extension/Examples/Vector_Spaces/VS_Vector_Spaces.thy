(* Title: Examples/Vector_Spaces/VS_Vector_Spaces.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Vector spaces\<close>
theory VS_Vector_Spaces
  imports VS_Modules
begin



subsection\<open>\<open>vector_space_with\<close>\<close>

locale vector_space_with = ab_group_add plus\<^sub>V\<^sub>S zero\<^sub>V\<^sub>S minus\<^sub>V\<^sub>S uminus\<^sub>V\<^sub>S
  for plus\<^sub>V\<^sub>S :: "['vs, 'vs] \<Rightarrow> 'vs" (infixl \<open>+\<^sub>V\<^sub>S\<close> 65)
    and zero\<^sub>V\<^sub>S (\<open>0\<^sub>V\<^sub>S\<close>)
    and minus\<^sub>V\<^sub>S (infixl \<open>-\<^sub>V\<^sub>S\<close> 65)
    and uminus\<^sub>V\<^sub>S (\<open>-\<^sub>V\<^sub>S _\<close> [81] 80) +
  fixes scale :: "['f::field, 'vs] \<Rightarrow> 'vs" (infixr "*s\<^sub>w\<^sub>i\<^sub>t\<^sub>h" 75)
  assumes scale_right_distrib[algebra_simps]: 
    "a *s\<^sub>w\<^sub>i\<^sub>t\<^sub>h (x +\<^sub>V\<^sub>S y) = a *s\<^sub>w\<^sub>i\<^sub>t\<^sub>h x +\<^sub>V\<^sub>S a *s\<^sub>w\<^sub>i\<^sub>t\<^sub>h y"
    and scale_left_distrib[algebra_simps]:
      "(a + b) *s\<^sub>w\<^sub>i\<^sub>t\<^sub>h x = a *s\<^sub>w\<^sub>i\<^sub>t\<^sub>h x +\<^sub>V\<^sub>S b *s\<^sub>w\<^sub>i\<^sub>t\<^sub>h x"
    and scale_scale[simp]: "a *s\<^sub>w\<^sub>i\<^sub>t\<^sub>h (b *s\<^sub>w\<^sub>i\<^sub>t\<^sub>h x) = (a * b) *s\<^sub>w\<^sub>i\<^sub>t\<^sub>h x"
    and scale_one[simp]: "1 *s\<^sub>w\<^sub>i\<^sub>t\<^sub>h x = x"
begin

notation plus\<^sub>V\<^sub>S (infixl \<open>+\<^sub>V\<^sub>S\<close> 65)
  and zero\<^sub>V\<^sub>S (\<open>0\<^sub>V\<^sub>S\<close>)
  and minus\<^sub>V\<^sub>S (infixl \<open>-\<^sub>V\<^sub>S\<close> 65)
  and uminus\<^sub>V\<^sub>S (\<open>-\<^sub>V\<^sub>S _\<close> [81] 80)
  and scale (infixr "*s\<^sub>w\<^sub>i\<^sub>t\<^sub>h" 75)
  
end

lemma vector_space_with_overloaded[ud_with]: 
  "vector_space = vector_space_with (+) 0 (-) uminus"
  unfolding vector_space_def vector_space_with_def vector_space_with_axioms_def
  by (simp add: field_axioms ab_group_add_axioms)

locale vector_space_pair_with =
  VS\<^sub>1: vector_space_with plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 scale\<^sub>1 +
  VS\<^sub>2: vector_space_with plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 scale\<^sub>2
  for plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 :: "['vs_1, 'vs_1] \<Rightarrow> 'vs_1" (infixl \<open>+\<^sub>V\<^sub>S\<^sub>'_\<^sub>1\<close> 65)
    and zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (\<open>0\<^sub>V\<^sub>S\<^sub>'_\<^sub>1\<close>)
    and minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (infixl \<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>1\<close> 65)
    and uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (\<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>1 _\<close> [81] 80)
    and scale\<^sub>1 :: "['f::field, 'vs_1] \<Rightarrow> 'vs_1"  (infixr \<open>*s\<^sub>w\<^sub>i\<^sub>t\<^sub>h\<^sub>'_\<^sub>1\<close> 75)
    and plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 :: "['vs_2, 'vs_2] \<Rightarrow> 'vs_2" (infixl \<open>+\<^sub>V\<^sub>S\<^sub>'_\<^sub>2\<close> 65)
    and zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (\<open>0\<^sub>V\<^sub>S\<^sub>'_\<^sub>2\<close>)
    and minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (infixl \<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>2\<close> 65)
    and uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (\<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>2 _\<close> [81] 80)
    and scale\<^sub>2 :: "['f::field, 'vs_2] \<Rightarrow> 'vs_2" (infixr \<open>*s\<^sub>w\<^sub>i\<^sub>t\<^sub>h\<^sub>'_\<^sub>2\<close> 75)

lemma vector_space_pair_with_overloaded[ud_with]: 
  "vector_space_pair = 
    (
      \<lambda>scale\<^sub>1 scale\<^sub>2. 
        vector_space_pair_with (+) 0 (-) uminus scale\<^sub>1 (+) 0 (-) uminus scale\<^sub>2
    )"
  unfolding vector_space_pair_def vector_space_pair_with_def 
  unfolding vector_space_with_overloaded
  ..

locale linear_with =
  VS\<^sub>1: vector_space_with plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 scale\<^sub>1 +
  VS\<^sub>2: vector_space_with plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 scale\<^sub>2 +
  module_hom_with 
    plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 scale\<^sub>1
    plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 scale\<^sub>2
    f 
  for plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 :: "['vs_1, 'vs_1] \<Rightarrow> 'vs_1" (infixl \<open>+\<^sub>V\<^sub>S\<^sub>'_\<^sub>1\<close> 65)
    and zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (\<open>0\<^sub>V\<^sub>S\<^sub>'_\<^sub>1\<close>)
    and minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (infixl \<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>1\<close> 65)
    and uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (\<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>1 _\<close> [81] 80)
    and scale\<^sub>1 :: "['f::field, 'vs_1] \<Rightarrow> 'vs_1"  (infixr \<open>*s\<^sub>w\<^sub>i\<^sub>t\<^sub>h\<^sub>'_\<^sub>1\<close> 75)
    and plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 :: "['vs_2, 'vs_2] \<Rightarrow> 'vs_2" (infixl \<open>+\<^sub>V\<^sub>S\<^sub>'_\<^sub>2\<close> 65)
    and zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (\<open>0\<^sub>V\<^sub>S\<^sub>'_\<^sub>2\<close>)
    and minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (infixl \<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>2\<close> 65)
    and uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (\<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>2 _\<close> [81] 80)
    and scale\<^sub>2 :: "['f::field, 'vs_2] \<Rightarrow> 'vs_2" (infixr \<open>*s\<^sub>w\<^sub>i\<^sub>t\<^sub>h\<^sub>'_\<^sub>2\<close> 75)
    and f :: "'vs_1 \<Rightarrow> 'vs_2"

lemma linear_with_overloaded[ud_with]: 
  "Vector_Spaces.linear = 
    (
      \<lambda>scale\<^sub>1 scale\<^sub>2. 
        linear_with (+) 0 (-) uminus scale\<^sub>1 (+) 0 (-) uminus scale\<^sub>2
    )"
  unfolding 
    Vector_Spaces.linear_def linear_with_def 
    vector_space_with_overloaded module_hom_with_overloaded
  ..

locale finite_dimensional_vector_space_with = 
  vector_space_with plus\<^sub>V\<^sub>S zero\<^sub>V\<^sub>S minus\<^sub>V\<^sub>S uminus\<^sub>V\<^sub>S scale
  for plus\<^sub>V\<^sub>S :: "['vs, 'vs] \<Rightarrow> 'vs"
    and zero\<^sub>V\<^sub>S 
    and minus\<^sub>V\<^sub>S 
    and uminus\<^sub>V\<^sub>S 
    and scale :: "['f::field, 'vs] \<Rightarrow> 'vs" +
  fixes basis :: "'vs set"
  assumes finite_basis: "finite basis"
    and independent_basis: "independent_with 0 0\<^sub>V\<^sub>S (+\<^sub>V\<^sub>S) (*s\<^sub>w\<^sub>i\<^sub>t\<^sub>h) basis"
    and span_basis: "span.with 0\<^sub>V\<^sub>S (+\<^sub>V\<^sub>S) (*s\<^sub>w\<^sub>i\<^sub>t\<^sub>h) basis = UNIV"

lemma finite_dimensional_vector_space_with_overloaded[ud_with]: 
  "finite_dimensional_vector_space = 
    finite_dimensional_vector_space_with (+) 0 (-) uminus"
  unfolding
    finite_dimensional_vector_space_def
    finite_dimensional_vector_space_axioms_def
    finite_dimensional_vector_space_with_def
    finite_dimensional_vector_space_with_axioms_def
  by (intro ext)
    (
      auto simp: 
        vector_space_with_overloaded 
        dependent.with 
        module_iff_vector_space
        span.with 
    )

locale finite_dimensional_vector_space_pair_1_with = 
  VS\<^sub>1: finite_dimensional_vector_space_with 
    plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 scale\<^sub>1 basis\<^sub>1 +
  VS\<^sub>2: vector_space_with 
    plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 scale\<^sub>2
  for plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 :: "['vs_1, 'vs_1] \<Rightarrow> 'vs_1" (infixl \<open>+\<^sub>V\<^sub>S\<^sub>'_\<^sub>1\<close> 65)
    and zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (\<open>0\<^sub>V\<^sub>S\<^sub>'_\<^sub>1\<close>)
    and minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (infixl \<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>1\<close> 65)
    and uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (\<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>1 _\<close> [81] 80)
    and scale\<^sub>1 :: "['f::field, 'vs_1] \<Rightarrow> 'vs_1" (infixr \<open>*s\<^sub>w\<^sub>i\<^sub>t\<^sub>h\<^sub>'_\<^sub>1\<close> 75)
    and basis\<^sub>1
    and plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 :: "['vs_2, 'vs_2] \<Rightarrow> 'vs_2" (infixl \<open>+\<^sub>V\<^sub>S\<^sub>'_\<^sub>2\<close> 65)
    and zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (\<open>0\<^sub>V\<^sub>S\<^sub>'_\<^sub>2\<close>)
    and minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (infixl \<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>2\<close> 65)
    and uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (\<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>2 _\<close> [81] 80)
    and scale\<^sub>2 :: "['f::field, 'vs_2] \<Rightarrow> 'vs_2" (infixr \<open>*s\<^sub>w\<^sub>i\<^sub>t\<^sub>h\<^sub>'_\<^sub>2\<close> 75)

lemma finite_dimensional_vector_space_pair_1_with_overloaded[ud_with]: 
  "finite_dimensional_vector_space_pair_1 = 
    (
      \<lambda>scale\<^sub>1 basis\<^sub>1 scale\<^sub>2. 
        finite_dimensional_vector_space_pair_1_with 
          (+) 0 (-) uminus scale\<^sub>1 basis\<^sub>1 (+) 0 (-) uminus scale\<^sub>2
    )"
  unfolding
    finite_dimensional_vector_space_pair_1_def
    finite_dimensional_vector_space_pair_1_with_def    
    vector_space_with_overloaded
  by (simp add: finite_dimensional_vector_space_with_overloaded)

locale finite_dimensional_vector_space_pair_with = 
  VS\<^sub>1: finite_dimensional_vector_space_with 
    plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 scale\<^sub>1 basis\<^sub>1 +
  VS\<^sub>2: finite_dimensional_vector_space_with 
    plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 scale\<^sub>2 basis\<^sub>2
  for plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 :: "['vs_1, 'vs_1] \<Rightarrow> 'vs_1" (infixl \<open>+\<^sub>V\<^sub>S\<^sub>'_\<^sub>1\<close> 65)
    and zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (\<open>0\<^sub>V\<^sub>S\<^sub>'_\<^sub>1\<close>)
    and minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (infixl \<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>1\<close> 65)
    and uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (\<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>1 _\<close> [81] 80)
    and scale\<^sub>1 :: "['f::field, 'vs_1] \<Rightarrow> 'vs_1" (infixr \<open>*s\<^sub>w\<^sub>i\<^sub>t\<^sub>h\<^sub>'_\<^sub>1\<close> 75)
    and basis\<^sub>1
    and plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 :: "['vs_2, 'vs_2] \<Rightarrow> 'vs_2" (infixl \<open>+\<^sub>V\<^sub>S\<^sub>'_\<^sub>2\<close> 65)
    and zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (\<open>0\<^sub>V\<^sub>S\<^sub>'_\<^sub>2\<close>)
    and minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (infixl \<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>2\<close> 65)
    and uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (\<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>2 _\<close> [81] 80)
    and scale\<^sub>2 :: "['f::field, 'vs_2] \<Rightarrow> 'vs_2" (infixr \<open>*s\<^sub>w\<^sub>i\<^sub>t\<^sub>h\<^sub>'_\<^sub>2\<close> 75)
    and basis\<^sub>2

lemma finite_dimensional_vector_space_pair_with_overloaded[ud_with]: 
  "finite_dimensional_vector_space_pair = 
    (
      \<lambda>scale\<^sub>1 basis\<^sub>1 scale\<^sub>2 basis\<^sub>2. 
        finite_dimensional_vector_space_pair_with 
          (+) 0 (-) uminus scale\<^sub>1 basis\<^sub>1 (+) 0 (-) uminus scale\<^sub>2 basis\<^sub>2
    )"
  unfolding
    finite_dimensional_vector_space_pair_def
    finite_dimensional_vector_space_pair_with_def
    finite_dimensional_vector_space_with_overloaded
  ..



subsection\<open>\<open>vector_space_ow\<close>\<close>


subsubsection\<open>Definitions and common properties\<close>


text\<open>Single vector space.\<close>

locale vector_space_ow = ab_group_add_ow U\<^sub>V\<^sub>S plus\<^sub>V\<^sub>S zero\<^sub>V\<^sub>S minus\<^sub>V\<^sub>S uminus\<^sub>V\<^sub>S
  for U\<^sub>V\<^sub>S :: "'vs set" 
    and plus\<^sub>V\<^sub>S (infixl \<open>+\<^sub>V\<^sub>S\<close> 65)
    and zero\<^sub>V\<^sub>S (\<open>0\<^sub>V\<^sub>S\<close>)
    and minus\<^sub>V\<^sub>S (infixl \<open>-\<^sub>V\<^sub>S\<close> 65)
    and uminus\<^sub>V\<^sub>S (\<open>-\<^sub>V\<^sub>S _\<close> [81] 80) +
  fixes scale :: "['f::field, 'vs] \<Rightarrow> 'vs" (infixr "*s\<^sub>o\<^sub>w" 75)
  assumes scale_closed[simp, intro]: "x \<in> U\<^sub>V\<^sub>S \<Longrightarrow> a *s\<^sub>o\<^sub>w x \<in> U\<^sub>V\<^sub>S"
    and scale_right_distrib[algebra_simps]: 
    "\<lbrakk> x \<in> U\<^sub>V\<^sub>S; y \<in> U\<^sub>V\<^sub>S \<rbrakk> \<Longrightarrow> a *s\<^sub>o\<^sub>w (x +\<^sub>V\<^sub>S y) = a *s\<^sub>o\<^sub>w x +\<^sub>V\<^sub>S a *s\<^sub>o\<^sub>w y"
    and scale_left_distrib[algebra_simps]: 
      "x \<in> U\<^sub>V\<^sub>S \<Longrightarrow> (a + b) *s\<^sub>o\<^sub>w x = a *s\<^sub>o\<^sub>w x +\<^sub>V\<^sub>S b *s\<^sub>o\<^sub>w x"
    and scale_scale[simp]: 
      "x \<in> U\<^sub>V\<^sub>S \<Longrightarrow> a *s\<^sub>o\<^sub>w (b *s\<^sub>o\<^sub>w x) = (a * b) *s\<^sub>o\<^sub>w x"
    and scale_one[simp]: "x \<in> U\<^sub>V\<^sub>S \<Longrightarrow> 1 *s\<^sub>o\<^sub>w x = x"
begin

lemma scale_closed'[simp]: "\<forall>a. \<forall>x\<in>U\<^sub>V\<^sub>S. a *s\<^sub>o\<^sub>w x \<in> U\<^sub>V\<^sub>S" by simp

lemma minus_closed'[simp]: "\<forall>x\<in>U\<^sub>V\<^sub>S. \<forall>y\<in>U\<^sub>V\<^sub>S. x -\<^sub>V\<^sub>S y \<in> U\<^sub>V\<^sub>S"
  by (simp add: ab_diff_conv_add_uminus add_closed' uminus_closed)

lemma uminus_closed'[simp]: "\<forall>x\<in>U\<^sub>V\<^sub>S. -\<^sub>V\<^sub>S x \<in> U\<^sub>V\<^sub>S" by (simp add: uminus_closed)

tts_register_sbts \<open>(*s\<^sub>o\<^sub>w)\<close> | U\<^sub>V\<^sub>S
  by (rule tts_AB_C_transfer[OF scale_closed]) 
    (auto simp: bi_unique_eq right_total_eq)

sublocale implicit\<^sub>V\<^sub>S: module_ow U\<^sub>V\<^sub>S plus\<^sub>V\<^sub>S zero\<^sub>V\<^sub>S minus\<^sub>V\<^sub>S uminus\<^sub>V\<^sub>S scale
  by unfold_locales (simp_all add: scale_right_distrib scale_left_distrib)

end

ud \<open>vector_space.dim\<close>
ud dim' \<open>dim\<close>


text\<open>Pair of vector spaces.\<close>

locale vector_space_pair_ow = 
  VS\<^sub>1: vector_space_ow U\<^sub>V\<^sub>S\<^sub>_\<^sub>1 plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 scale\<^sub>1 +
  VS\<^sub>2: vector_space_ow U\<^sub>V\<^sub>S\<^sub>_\<^sub>2 plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 scale\<^sub>2
  for U\<^sub>V\<^sub>S\<^sub>_\<^sub>1 :: "'vs_1 set"
    and plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (infixl \<open>+\<^sub>V\<^sub>S\<^sub>'_\<^sub>1\<close> 65)
    and zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (\<open>0\<^sub>V\<^sub>S\<^sub>'_\<^sub>1\<close>)
    and minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (infixl \<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>1\<close> 65)
    and uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (\<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>1 _\<close> [81] 80)
    and scale\<^sub>1 :: "['f::field, 'vs_1] \<Rightarrow> 'vs_1" (infixr \<open>*s\<^sub>o\<^sub>w\<^sub>'_\<^sub>1\<close> 75)
    and U\<^sub>V\<^sub>S\<^sub>_\<^sub>2 :: "'vs_2 set"
    and plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (infixl \<open>+\<^sub>V\<^sub>S\<^sub>'_\<^sub>2\<close> 65)
    and zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (\<open>0\<^sub>V\<^sub>S\<^sub>'_\<^sub>2\<close>)
    and minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (infixl \<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>2\<close> 65)
    and uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (\<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>2 _\<close> [81] 80)
    and scale\<^sub>2 :: "['f::field, 'vs_2] \<Rightarrow> 'vs_2" (infixr \<open>*s\<^sub>o\<^sub>w\<^sub>'_\<^sub>2\<close> 75)
begin

sublocale implicit\<^sub>V\<^sub>S: module_pair_ow 
  U\<^sub>V\<^sub>S\<^sub>_\<^sub>1 plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 scale\<^sub>1
  U\<^sub>V\<^sub>S\<^sub>_\<^sub>2 plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 scale\<^sub>2
  by unfold_locales

end


text\<open>Linear map.\<close>

locale linear_ow =
  VS\<^sub>1: vector_space_ow U\<^sub>V\<^sub>S\<^sub>_\<^sub>1 plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 scale\<^sub>1 +
  VS\<^sub>2: vector_space_ow U\<^sub>V\<^sub>S\<^sub>_\<^sub>2 plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 scale\<^sub>2 +
  module_hom_ow 
    U\<^sub>V\<^sub>S\<^sub>_\<^sub>1 plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 scale\<^sub>1
    U\<^sub>V\<^sub>S\<^sub>_\<^sub>2 plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 scale\<^sub>2
    f 
  for U\<^sub>V\<^sub>S\<^sub>_\<^sub>1 :: "'vs_1 set"
    and plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (infixl \<open>+\<^sub>V\<^sub>S\<^sub>'_\<^sub>1\<close> 65)
    and zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (\<open>0\<^sub>V\<^sub>S\<^sub>'_\<^sub>1\<close>)
    and minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (infixl \<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>1\<close> 65)
    and uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (\<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>1 _\<close> [81] 80)
    and scale\<^sub>1 :: "['f::field, 'vs_1] \<Rightarrow> 'vs_1" (infixr \<open>*s\<^sub>o\<^sub>w\<^sub>'_\<^sub>1\<close> 75)
    and U\<^sub>V\<^sub>S\<^sub>_\<^sub>2 :: "'vs_2 set"
    and plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (infixl \<open>+\<^sub>V\<^sub>S\<^sub>'_\<^sub>2\<close> 65)
    and zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (\<open>0\<^sub>V\<^sub>S\<^sub>'_\<^sub>2\<close>)
    and minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (infixl \<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>2\<close> 65)
    and uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (\<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>2 _\<close> [81] 80)
    and scale\<^sub>2 :: "['f::field, 'vs_2] \<Rightarrow> 'vs_2" (infixr \<open>*s\<^sub>o\<^sub>w\<^sub>'_\<^sub>2\<close> 75)
    and f :: "'vs_1 \<Rightarrow> 'vs_2"
begin

sublocale implicit\<^sub>V\<^sub>S: vector_space_pair_ow
  U\<^sub>V\<^sub>S\<^sub>_\<^sub>1 plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 scale\<^sub>1
  U\<^sub>V\<^sub>S\<^sub>_\<^sub>2 plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 scale\<^sub>2
  by unfold_locales

end


text\<open>Single finite dimensional vector space.\<close>

locale finite_dimensional_vector_space_ow = 
  vector_space_ow U\<^sub>V\<^sub>S plus\<^sub>V\<^sub>S zero\<^sub>V\<^sub>S minus\<^sub>V\<^sub>S uminus\<^sub>V\<^sub>S scale
  for U\<^sub>V\<^sub>S :: "'vs set"
    and plus\<^sub>V\<^sub>S (infixl \<open>+\<^sub>V\<^sub>S\<close> 65)
    and zero\<^sub>V\<^sub>S (\<open>0\<^sub>V\<^sub>S\<close>)
    and minus\<^sub>V\<^sub>S (infixl \<open>-\<^sub>V\<^sub>S\<close> 65)
    and uminus\<^sub>V\<^sub>S (\<open>-\<^sub>V\<^sub>S _\<close> [81] 80) 
    and scale :: "['f::field, 'vs] \<Rightarrow> 'vs" (infixr "*s\<^sub>o\<^sub>w" 75) +
  fixes basis :: "'vs set"
  assumes basis_closed: "basis \<subseteq> U\<^sub>V\<^sub>S"
    and finite_basis: "finite basis"
    and independent_basis: "independent_with 0 zero\<^sub>V\<^sub>S plus\<^sub>V\<^sub>S scale basis"
    and span_basis: "span.with zero\<^sub>V\<^sub>S plus\<^sub>V\<^sub>S scale basis = U\<^sub>V\<^sub>S"


text\<open>Pair of finite dimensional vector spaces.\<close>

locale finite_dimensional_vector_space_pair_1_ow =
  VS\<^sub>1: finite_dimensional_vector_space_ow
    U\<^sub>V\<^sub>S\<^sub>_\<^sub>1 plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 scale\<^sub>1 basis\<^sub>1 +
  VS\<^sub>2: vector_space_ow 
    U\<^sub>V\<^sub>S\<^sub>_\<^sub>2 plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 scale\<^sub>2
  for U\<^sub>V\<^sub>S\<^sub>_\<^sub>1 :: "'vs_1 set"
    and plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (infixl \<open>+\<^sub>V\<^sub>S\<^sub>'_\<^sub>1\<close> 65)
    and zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (\<open>0\<^sub>V\<^sub>S\<^sub>'_\<^sub>1\<close>)
    and minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (infixl \<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>1\<close> 65)
    and uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (\<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>1 _\<close> [81] 80)
    and scale\<^sub>1 :: "['f::field, 'vs_1] \<Rightarrow> 'vs_1" (infixr \<open>*s\<^sub>o\<^sub>w\<^sub>'_\<^sub>1\<close> 75)
    and basis\<^sub>1
    and U\<^sub>V\<^sub>S\<^sub>_\<^sub>2 :: "'vs_2 set"
    and plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (infixl \<open>+\<^sub>V\<^sub>S\<^sub>'_\<^sub>2\<close> 65)
    and zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (\<open>0\<^sub>V\<^sub>S\<^sub>'_\<^sub>2\<close>)
    and minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (infixl \<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>2\<close> 65)
    and uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (\<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>2 _\<close> [81] 80)
    and scale\<^sub>2 :: "['f::field, 'vs_2] \<Rightarrow> 'vs_2" (infixr \<open>*s\<^sub>o\<^sub>w\<^sub>'_\<^sub>2\<close> 75)

locale finite_dimensional_vector_space_pair_ow = 
  VS\<^sub>1: finite_dimensional_vector_space_ow 
    U\<^sub>V\<^sub>S\<^sub>_\<^sub>1 plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 scale\<^sub>1 basis\<^sub>1 + 
  VS\<^sub>2: finite_dimensional_vector_space_ow 
    U\<^sub>V\<^sub>S\<^sub>_\<^sub>2 plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 scale\<^sub>2 basis\<^sub>2
  for U\<^sub>V\<^sub>S\<^sub>_\<^sub>1 :: "'vs_1 set"
    and plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (infixl \<open>+\<^sub>V\<^sub>S\<^sub>'_\<^sub>1\<close> 65)
    and zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (\<open>0\<^sub>V\<^sub>S\<^sub>'_\<^sub>1\<close>)
    and minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (infixl \<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>1\<close> 65)
    and uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 (\<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>1 _\<close> [81] 80)
    and scale\<^sub>1 :: "['f::field, 'vs_1] \<Rightarrow> 'vs_1" (infixr \<open>*s\<^sub>o\<^sub>w\<^sub>'_\<^sub>1\<close> 75)
    and basis\<^sub>1
    and U\<^sub>V\<^sub>S\<^sub>_\<^sub>2 :: "'vs_2 set"
    and plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (infixl \<open>+\<^sub>V\<^sub>S\<^sub>'_\<^sub>2\<close> 65)
    and zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (\<open>0\<^sub>V\<^sub>S\<^sub>'_\<^sub>2\<close>)
    and minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (infixl \<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>2\<close> 65)
    and uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 (\<open>-\<^sub>V\<^sub>S\<^sub>'_\<^sub>2 _\<close> [81] 80)
    and scale\<^sub>2 :: "['f::field, 'vs_2] \<Rightarrow> 'vs_2" (infixr \<open>*s\<^sub>o\<^sub>w\<^sub>'_\<^sub>2\<close> 75)
    and basis\<^sub>2


subsubsection\<open>Transfer.\<close>

lemma vector_space_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique B" "right_total B"     
  fixes PP lhs
  defines
    "PP \<equiv> 
      (
        (B ===> B ===> B) ===>
        B ===>
        (B ===> B ===> B) ===>
        (B ===> B) ===>
        ((=) ===> B ===> B) ===>
        (=)
      )"
    and
      "lhs \<equiv> 
        (
          \<lambda>plus\<^sub>V\<^sub>S zero\<^sub>V\<^sub>S minus\<^sub>V\<^sub>S uminus\<^sub>V\<^sub>S scale.
            vector_space_ow 
              (Collect (Domainp B)) plus\<^sub>V\<^sub>S zero\<^sub>V\<^sub>S minus\<^sub>V\<^sub>S uminus\<^sub>V\<^sub>S scale
        )"
  shows "PP lhs vector_space_with"
proof-
  let ?rhs = 
    "(
      \<lambda>plus\<^sub>V\<^sub>S zero\<^sub>V\<^sub>S minus\<^sub>V\<^sub>S uminus\<^sub>V\<^sub>S scale.
        (\<forall>a \<in> UNIV. \<forall>x \<in> UNIV. scale a x \<in> UNIV) \<and>
         vector_space_with plus\<^sub>V\<^sub>S zero\<^sub>V\<^sub>S minus\<^sub>V\<^sub>S uminus\<^sub>V\<^sub>S scale
    )"
  have "PP lhs ?rhs"
    unfolding 
      PP_def lhs_def
      vector_space_ow_def vector_space_with_def
      vector_space_ow_axioms_def vector_space_with_axioms_def
    apply transfer_prover_start
    apply transfer_step+
    by (intro ext) blast
  then show ?thesis by simp
qed

lemma vector_space_pair_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: 
    "bi_unique B\<^sub>1" "right_total B\<^sub>1" "bi_unique B\<^sub>2" "right_total B\<^sub>2"     
  fixes PP lhs
  defines
    "PP \<equiv> 
      (
        (B\<^sub>1 ===> B\<^sub>1 ===> B\<^sub>1) ===>
        B\<^sub>1 ===>
        (B\<^sub>1 ===> B\<^sub>1 ===> B\<^sub>1) ===>
        (B\<^sub>1 ===> B\<^sub>1) ===>
        ((=) ===> B\<^sub>1 ===> B\<^sub>1) ===>
        (B\<^sub>2 ===> B\<^sub>2 ===> B\<^sub>2) ===>
        B\<^sub>2 ===>
        (B\<^sub>2 ===> B\<^sub>2 ===> B\<^sub>2) ===>
        (B\<^sub>2 ===> B\<^sub>2) ===>
        ((=) ===> B\<^sub>2 ===> B\<^sub>2) ===>
        (=)
    )"
    and
      "lhs \<equiv> 
        (
          \<lambda>
            plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 scale\<^sub>1
            plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 scale\<^sub>2.
          vector_space_pair_ow 
            (Collect (Domainp B\<^sub>1)) plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 scale\<^sub>1
            (Collect (Domainp B\<^sub>2)) plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 scale\<^sub>2
        )"
    shows "PP lhs vector_space_pair_with"
  unfolding PP_def lhs_def
  unfolding vector_space_pair_ow_def vector_space_pair_with_def
  by transfer_prover

lemma linear_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: 
    "bi_unique B\<^sub>1" "right_total B\<^sub>1" "bi_unique B\<^sub>2" "right_total B\<^sub>2"     
  fixes PP lhs
  defines
    "PP \<equiv> 
      (
        (B\<^sub>1 ===> B\<^sub>1 ===> B\<^sub>1) ===>
        B\<^sub>1 ===>
        (B\<^sub>1 ===> B\<^sub>1 ===> B\<^sub>1) ===>
        (B\<^sub>1 ===> B\<^sub>1) ===>
        ((=) ===> B\<^sub>1 ===> B\<^sub>1) ===>
        (B\<^sub>2 ===> B\<^sub>2 ===> B\<^sub>2) ===>
        B\<^sub>2 ===>
        (B\<^sub>2 ===> B\<^sub>2 ===> B\<^sub>2) ===>
        (B\<^sub>2 ===> B\<^sub>2) ===>
        ((=) ===> B\<^sub>2 ===> B\<^sub>2) ===>
        (B\<^sub>1 ===> B\<^sub>2) ===>
        (=)
    )"
    and
      "lhs \<equiv> 
        (
          \<lambda>
            plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 scale\<^sub>1
            plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 scale\<^sub>2
            f.
          linear_ow 
            (Collect (Domainp B\<^sub>1)) plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 scale\<^sub>1
            (Collect (Domainp B\<^sub>2)) plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 scale\<^sub>2
            f
        )
      "
    shows "PP lhs linear_with"
  unfolding PP_def lhs_def
  unfolding linear_ow_def linear_with_def
  by transfer_prover

lemma linear_with_transfer'[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique B" "right_total B"
  fixes PP lhs
  defines
    "PP \<equiv> 
      (
        (B ===> B ===> B) ===>
        B ===>
        (B ===> B ===> B) ===>
        (B ===> B) ===>
        ((=) ===> B ===> B) ===>
        (B ===> B ===> B) ===>
        B ===>
        (B ===> B ===> B) ===>
        (B ===> B) ===>
        ((=) ===> B ===> B) ===>
        (B ===> B) ===>
        (=)
    )"
    and
      "lhs \<equiv> 
        (
          \<lambda>
            plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 scale\<^sub>1
            plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 scale\<^sub>2
            f.
          linear_ow 
            (Collect (Domainp B)) plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 scale\<^sub>1
            (Collect (Domainp B)) plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 scale\<^sub>2
            f
        )
      "
    shows "PP lhs linear_with"
  unfolding PP_def lhs_def
  using assms(1,2) by (rule linear_with_transfer[OF assms(1,2)])

lemma finite_dimensional_vector_space_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique B" "right_total B"     
  fixes PP lhs
  defines
    "PP \<equiv> 
      (
        (B ===> B ===> B) ===>
        B ===>
        (B ===> B ===> B) ===>
        (B ===> B) ===>
        ((=) ===> B ===> B) ===>
        rel_set B ===>
        (=)
      )"
    and
      "lhs \<equiv> 
        (
          \<lambda>plus\<^sub>V\<^sub>S zero\<^sub>V\<^sub>S minus\<^sub>V\<^sub>S uminus\<^sub>V\<^sub>S scale basis.
            finite_dimensional_vector_space_ow 
              (Collect (Domainp B)) plus\<^sub>V\<^sub>S zero\<^sub>V\<^sub>S minus\<^sub>V\<^sub>S uminus\<^sub>V\<^sub>S scale basis
        )"
    shows "PP lhs finite_dimensional_vector_space_with"
proof-
  let ?rhs = 
    "(
      \<lambda>plus\<^sub>V\<^sub>S zero\<^sub>V\<^sub>S minus\<^sub>V\<^sub>S uminus\<^sub>V\<^sub>S scale basis.
        basis \<subseteq> UNIV \<and>
        finite_dimensional_vector_space_with 
          plus\<^sub>V\<^sub>S zero\<^sub>V\<^sub>S minus\<^sub>V\<^sub>S uminus\<^sub>V\<^sub>S scale basis
    )"
  have "PP lhs ?rhs"
    unfolding 
      PP_def lhs_def
      finite_dimensional_vector_space_ow_def 
      finite_dimensional_vector_space_with_def
      finite_dimensional_vector_space_ow_axioms_def
      finite_dimensional_vector_space_with_axioms_def
    apply transfer_prover_start
    apply transfer_step+
    by blast
  then show ?thesis by simp
qed

lemma finite_dimensional_vector_space_pair_1_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: 
    "bi_unique B\<^sub>1" "right_total B\<^sub>1" "bi_unique B\<^sub>2" "right_total B\<^sub>2"     
  fixes PP lhs
  defines
    "PP \<equiv> 
      (
        (B\<^sub>1 ===> B\<^sub>1 ===> B\<^sub>1) ===>
        B\<^sub>1 ===>
        (B\<^sub>1 ===> B\<^sub>1 ===> B\<^sub>1) ===>
        (B\<^sub>1 ===> B\<^sub>1) ===>
        ((=) ===> B\<^sub>1 ===> B\<^sub>1) ===>
        rel_set B\<^sub>1 ===>
        (B\<^sub>2 ===> B\<^sub>2 ===> B\<^sub>2) ===>
        B\<^sub>2 ===>
        (B\<^sub>2 ===> B\<^sub>2 ===> B\<^sub>2) ===>
        (B\<^sub>2 ===> B\<^sub>2) ===>
        ((=) ===> B\<^sub>2 ===> B\<^sub>2) ===>
        (=)
    )"
    and
      "lhs \<equiv> 
        (
          \<lambda>
            plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 scale\<^sub>1 basis\<^sub>1
            plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 scale\<^sub>2.
          finite_dimensional_vector_space_pair_1_ow 
            (Collect (Domainp B\<^sub>1)) 
              plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 scale\<^sub>1 basis\<^sub>1
            (Collect (Domainp B\<^sub>2)) 
              plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 scale\<^sub>2
        )"
    shows "PP lhs finite_dimensional_vector_space_pair_1_with"
  unfolding PP_def lhs_def
  unfolding 
    finite_dimensional_vector_space_pair_1_ow_def
    finite_dimensional_vector_space_pair_1_with_def
  by transfer_prover

lemma finite_dimensional_vector_space_pair_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: 
    "bi_unique B\<^sub>1" "right_total B\<^sub>1" "bi_unique B\<^sub>2" "right_total B\<^sub>2"     
  fixes PP lhs
  defines
    "PP \<equiv> 
      (
        (B\<^sub>1 ===> B\<^sub>1 ===> B\<^sub>1) ===>
        B\<^sub>1 ===>
        (B\<^sub>1 ===> B\<^sub>1 ===> B\<^sub>1) ===>
        (B\<^sub>1 ===> B\<^sub>1) ===>
        ((=) ===> B\<^sub>1 ===> B\<^sub>1) ===>
        rel_set B\<^sub>1 ===>
        (B\<^sub>2 ===> B\<^sub>2 ===> B\<^sub>2) ===>
        B\<^sub>2 ===>
        (B\<^sub>2 ===> B\<^sub>2 ===> B\<^sub>2) ===>
        (B\<^sub>2 ===> B\<^sub>2) ===>
        ((=) ===> B\<^sub>2 ===> B\<^sub>2) ===>
        rel_set B\<^sub>2 ===>
        (=)
      )"
    and
      "lhs \<equiv> 
        (
          \<lambda>
            plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 scale\<^sub>1 basis\<^sub>1
            plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 scale\<^sub>2 basis\<^sub>2.
          finite_dimensional_vector_space_pair_ow 
            (Collect (Domainp B\<^sub>1)) 
              plus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>1 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>1 scale\<^sub>1 basis\<^sub>1
            (Collect (Domainp B\<^sub>2)) 
              plus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 zero\<^sub>V\<^sub>S\<^sub>_\<^sub>2 minus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 uminus\<^sub>V\<^sub>S\<^sub>_\<^sub>2 scale\<^sub>2 basis\<^sub>2
        )"
    shows "PP lhs finite_dimensional_vector_space_pair_with"
  unfolding PP_def lhs_def
  unfolding 
    finite_dimensional_vector_space_pair_ow_def
    finite_dimensional_vector_space_pair_with_def
  by transfer_prover



subsection\<open>\<open>vector_space_on\<close>\<close>

locale vector_space_on = module_on U\<^sub>V\<^sub>S scale
  for U\<^sub>V\<^sub>S and scale :: "'a::field \<Rightarrow> 'b::ab_group_add \<Rightarrow> 'b" (infixr "*s" 75)
begin

notation scale (infixr "*s" 75)

sublocale implicit\<^sub>V\<^sub>S: vector_space_ow U\<^sub>V\<^sub>S \<open>(+)\<close> 0 \<open>(-)\<close> uminus scale
  by unfold_locales 
    (simp_all add: scale_right_distrib_on scale_left_distrib_on)

lemmas ab_group_add_ow_axioms = implicit\<^sub>M.ab_group_add_ow_axioms
lemmas vector_space_ow_axioms = implicit\<^sub>V\<^sub>S.vector_space_ow_axioms

definition dim :: "'b set \<Rightarrow> nat"
  where "dim V = (if \<exists>b\<subseteq>U\<^sub>V\<^sub>S. \<not> dependent b \<and> span b = span V
    then card (SOME b. b \<subseteq> U\<^sub>V\<^sub>S \<and> \<not> dependent b \<and> span b = span V)
    else 0)"

end

lemma vector_space_on_alt_def: "vector_space_on U\<^sub>V\<^sub>S = module_on U\<^sub>V\<^sub>S"
  unfolding vector_space_on_def module_on_def
  by auto

lemma implicit_vector_space_ow[tts_implicit]:
  "vector_space_ow U\<^sub>V\<^sub>S (+) 0 (-) uminus = vector_space_on U\<^sub>V\<^sub>S"
proof(intro ext, rule iffI)
  fix s :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" 
  assume "vector_space_ow U\<^sub>V\<^sub>S (+) 0 (-) uminus s"
  then interpret vector_space_ow U\<^sub>V\<^sub>S \<open>(+)\<close> 0 \<open>(-)\<close> uminus s .
  show "vector_space_on U\<^sub>V\<^sub>S s"
    by 
      (
        simp add: 
          scale_left_distrib 
          scale_right_distrib
          module_on_def 
          vector_space_on_def
      )
qed (rule vector_space_on.vector_space_ow_axioms)

locale linear_on = 
  VS\<^sub>1: vector_space_on U\<^sub>M\<^sub>_\<^sub>1 scale\<^sub>1 +
  VS\<^sub>2: vector_space_on U\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>2 +
  module_hom_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>1 scale\<^sub>2 f
  for U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 and scale\<^sub>1::"'a::field \<Rightarrow> 'b \<Rightarrow> 'b::ab_group_add"
    and scale\<^sub>2::"'a::field \<Rightarrow> 'c \<Rightarrow> 'c::ab_group_add"
    and f

lemma implicit_linear_on[tts_implicit]:
  "linear_ow U\<^sub>M\<^sub>_\<^sub>1 (+) 0 minus uminus scale\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (+) 0 (-) uminus scale\<^sub>2 = 
    linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>1 scale\<^sub>2"
  unfolding linear_ow_def linear_on_def tts_implicit ..

locale finite_dimensional_vector_space_on =
  vector_space_on U\<^sub>V\<^sub>S scale 
  for U\<^sub>V\<^sub>S :: "'b::ab_group_add set" 
    and scale :: "'a::field \<Rightarrow> 'b \<Rightarrow> 'b" +
  fixes basis :: "'b set"
  assumes finite_basis: "finite basis"
    and independent_basis: "\<not> dependent basis"
    and span_basis: "span basis = U\<^sub>V\<^sub>S" 
    and basis_subset: "basis \<subseteq> U\<^sub>V\<^sub>S"
begin

sublocale implicit\<^sub>V\<^sub>S: 
  finite_dimensional_vector_space_ow U\<^sub>V\<^sub>S \<open>(+)\<close> 0 \<open>(-)\<close> uminus scale basis
  by unfold_locales 
    (
      simp_all add: 
        finite_basis 
        implicit_dependent_with 
        independent_basis  
        implicit_span_with
        span_basis
        basis_subset
    )

end

lemma implicit_finite_dimensional_vector_space_on[tts_implicit]:
  "finite_dimensional_vector_space_ow U\<^sub>V\<^sub>S (+) 0 minus uminus scale basis = 
    finite_dimensional_vector_space_on U\<^sub>V\<^sub>S scale basis"
  unfolding 
    finite_dimensional_vector_space_ow_def 
    finite_dimensional_vector_space_on_def  
    finite_dimensional_vector_space_ow_axioms_def
    finite_dimensional_vector_space_on_axioms_def  
    vector_space_on_alt_def
    tts_implicit
  by (metis module_on.implicit_dependent_with module_on.implicit_span_with)  

locale vector_space_pair_on = 
  VS\<^sub>1: vector_space_on U\<^sub>M\<^sub>_\<^sub>1 scale\<^sub>1 +
  VS\<^sub>2: vector_space_on U\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>2
  for U\<^sub>M\<^sub>_\<^sub>1:: "'b::ab_group_add set" and U\<^sub>M\<^sub>_\<^sub>2::"'c::ab_group_add set"
    and scale\<^sub>1::"'a::field \<Rightarrow> _ \<Rightarrow> _" (infixr \<open>*s\<^sub>1\<close> 75) 
    and scale\<^sub>2::"'a \<Rightarrow> _ \<Rightarrow> _" (infixr \<open>*s\<^sub>2\<close> 75)
begin

notation scale\<^sub>1 (infixr \<open>*s\<^sub>1\<close> 75)
notation scale\<^sub>2 (infixr \<open>*s\<^sub>2\<close> 75)

sublocale module_pair_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>1 scale\<^sub>2 by unfold_locales

sublocale implicit\<^sub>V\<^sub>S: 
  vector_space_pair_ow 
    U\<^sub>M\<^sub>_\<^sub>1 \<open>(+)\<close> 0 \<open>(-)\<close> uminus scale\<^sub>1 
    U\<^sub>M\<^sub>_\<^sub>2 \<open>(+)\<close> 0 \<open>(-)\<close> uminus scale\<^sub>2
  by unfold_locales

end

lemma implicit_vector_space_pair_on[tts_implicit]:
  "vector_space_pair_ow 
    U\<^sub>M\<^sub>_\<^sub>1 (+) 0 (-) uminus scale\<^sub>1 
    U\<^sub>M\<^sub>_\<^sub>2 (+) 0 (-) uminus scale\<^sub>2 = 
    vector_space_pair_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>1 scale\<^sub>2"
  unfolding vector_space_pair_ow_def vector_space_pair_on_def tts_implicit ..

locale finite_dimensional_vector_space_pair_1_on =
  VS\<^sub>1: finite_dimensional_vector_space_on U\<^sub>M\<^sub>_\<^sub>1 scale\<^sub>1 basis1 +
  VS\<^sub>2: vector_space_on U\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>2
  for U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2
    and scale\<^sub>1::"'a::field \<Rightarrow> 'b::ab_group_add \<Rightarrow> 'b"
    and scale\<^sub>2::"'a::field \<Rightarrow> 'c::ab_group_add \<Rightarrow> 'c"
    and basis1
begin

sublocale vector_space_pair_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>1 scale\<^sub>2 by unfold_locales

sublocale implicit\<^sub>V\<^sub>S:
  finite_dimensional_vector_space_pair_1_ow 
    U\<^sub>M\<^sub>_\<^sub>1 \<open>(+)\<close> 0 \<open>(-)\<close> uminus scale\<^sub>1 basis1 U\<^sub>M\<^sub>_\<^sub>2 \<open>(+)\<close> 0 \<open>(-)\<close> uminus scale\<^sub>2
  by unfold_locales

end

lemma implicit_finite_dimensional_vector_space_pair_1_on[tts_implicit]:
  "finite_dimensional_vector_space_pair_1_ow 
    U\<^sub>M\<^sub>_\<^sub>1 (+) 0 minus uminus scale\<^sub>1 basis1 U\<^sub>M\<^sub>_\<^sub>2 (+) 0 (-) uminus scale\<^sub>2 = 
    finite_dimensional_vector_space_pair_1_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>1 scale\<^sub>2 basis1"
  unfolding 
    finite_dimensional_vector_space_pair_1_ow_def 
    finite_dimensional_vector_space_pair_1_on_def 
    tts_implicit 
    ..

locale finite_dimensional_vector_space_pair_on =
  VS\<^sub>1: finite_dimensional_vector_space_on U\<^sub>M\<^sub>_\<^sub>1 scale\<^sub>1 basis1 +
  VS\<^sub>2: finite_dimensional_vector_space_on U\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>2 basis2
  for U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2
    and scale\<^sub>1::"'a::field \<Rightarrow> 'b::ab_group_add \<Rightarrow> 'b"
    and scale\<^sub>2::"'a::field \<Rightarrow> 'c::ab_group_add \<Rightarrow> 'c"
    and basis1 basis2
begin

sublocale finite_dimensional_vector_space_pair_1_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>1 scale\<^sub>2 
  by unfold_locales

sublocale implicit\<^sub>V\<^sub>S: 
  finite_dimensional_vector_space_pair_ow 
    U\<^sub>M\<^sub>_\<^sub>1 \<open>(+)\<close> 0 \<open>(-)\<close> uminus scale\<^sub>1 basis1 
    U\<^sub>M\<^sub>_\<^sub>2 \<open>(+)\<close> 0 \<open>(-)\<close> uminus scale\<^sub>2 basis2
  by unfold_locales

end

lemma implicit_finite_dimensional_vector_space_pair_on[tts_implicit]:
  "finite_dimensional_vector_space_pair_ow 
      U\<^sub>M\<^sub>_\<^sub>1 (+) 0 minus uminus scale\<^sub>1 basis1 
      U\<^sub>M\<^sub>_\<^sub>2 (+) 0 (-) uminus scale\<^sub>2 basis2 = 
    finite_dimensional_vector_space_pair_on 
      U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>1 scale\<^sub>2 basis1 basis2"
  unfolding 
    finite_dimensional_vector_space_pair_ow_def 
    finite_dimensional_vector_space_pair_on_def 
    tts_implicit 
    ..



subsection\<open>Relativization : part I\<close>

context vector_space_on
begin

tts_context
  tts: (?'b to \<open>U\<^sub>V\<^sub>S::'b set\<close>)
  rewriting ctr_simps
  substituting ab_group_add_ow_axioms
    and vector_space_ow_axioms
    and implicit\<^sub>M.module_ow_axioms
  applying 
    [
      OF 
        implicit\<^sub>M.carrier_ne 
        implicit\<^sub>M.add_closed' 
        implicit\<^sub>M.zero_closed 
        implicit\<^sub>V\<^sub>S.minus_closed' 
        implicit\<^sub>V\<^sub>S.uminus_closed' 
        implicit\<^sub>V\<^sub>S.scale_closed',
      unfolded tts_implicit
    ]
begin

tts_lemma linear_id: "linear_on U\<^sub>V\<^sub>S U\<^sub>V\<^sub>S (*s) (*s) id"
  is vector_space.linear_id.

tts_lemma linear_ident: "linear_on U\<^sub>V\<^sub>S U\<^sub>V\<^sub>S (*s) (*s) (\<lambda>x. x)"
  is vector_space.linear_ident.
    
tts_lemma linear_scale_self: "linear_on U\<^sub>V\<^sub>S U\<^sub>V\<^sub>S (*s) (*s) ((*s) c)"
  is vector_space.linear_scale_self.
    
tts_lemma linear_scale_left:
  assumes "x \<in> U\<^sub>V\<^sub>S"
  shows "linear_on UNIV U\<^sub>V\<^sub>S (*) (*s) (\<lambda>r. r *s x)"
    is vector_space.linear_scale_left.
    
tts_lemma linear_uminus: "linear_on U\<^sub>V\<^sub>S U\<^sub>V\<^sub>S (*s) (*s) uminus"
    is vector_space.linear_uminus.
    
tts_lemma linear_imp_scale["consumes" - 1, "case_names" "1"]:
  assumes "range D \<subseteq> U\<^sub>V\<^sub>S"
    and "linear_on UNIV U\<^sub>V\<^sub>S (*) (*s) D"
    and "\<And>d. \<lbrakk>d \<in> U\<^sub>V\<^sub>S; D = (\<lambda>x. x *s d)\<rbrakk> \<Longrightarrow> thesis"
  shows thesis
    is vector_space.linear_imp_scale.

tts_lemma scale_eq_0_iff:
  assumes "x \<in> U\<^sub>V\<^sub>S"
  shows "(a *s x = 0) = (a = 0 \<or> x = 0)"
    is vector_space.scale_eq_0_iff.

tts_lemma scale_left_imp_eq:
  assumes "x \<in> U\<^sub>V\<^sub>S" and "y \<in> U\<^sub>V\<^sub>S" and "a \<noteq> 0" and "a *s x = a *s y"
  shows "x = y"
    is vector_space.scale_left_imp_eq.

tts_lemma scale_right_imp_eq:
  assumes "x \<in> U\<^sub>V\<^sub>S" and "x \<noteq> 0" and "a *s x = b *s x"
  shows "a = b"
    is vector_space.scale_right_imp_eq.

tts_lemma scale_cancel_left:
  assumes "x \<in> U\<^sub>V\<^sub>S" and "y \<in> U\<^sub>V\<^sub>S"
  shows "(a *s x = a *s y) = (x = y \<or> a = 0)"
    is vector_space.scale_cancel_left.

tts_lemma scale_cancel_right:
  assumes "x \<in> U\<^sub>V\<^sub>S"
  shows "(a *s x = b *s x) = (a = b \<or> x = 0)"
    is vector_space.scale_cancel_right.

tts_lemma injective_scale:
  assumes "c \<noteq> 0"
  shows "inj_on ((*s) c) U\<^sub>V\<^sub>S"
    is vector_space.injective_scale.

tts_lemma dependent_def:
  assumes "P \<subseteq> U\<^sub>V\<^sub>S"
  shows "dependent P = (\<exists>x\<in>P. x \<in> span (P - {x}))"
    is vector_space.dependent_def.

tts_lemma dependent_single:
  assumes "x \<in> U\<^sub>V\<^sub>S"
  shows "dependent {x} = (x = 0)"
    is vector_space.dependent_single.

tts_lemma in_span_insert:
  assumes "a \<in> U\<^sub>V\<^sub>S"
    and "b \<in> U\<^sub>V\<^sub>S"
    and "S \<subseteq> U\<^sub>V\<^sub>S"
    and "a \<in> span (insert b S)"
    and "a \<notin> span S"
  shows "b \<in> span (insert a S)"
    is vector_space.in_span_insert.

tts_lemma dependent_insertD:
  assumes "a \<in> U\<^sub>V\<^sub>S" and "S \<subseteq> U\<^sub>V\<^sub>S" and "a \<notin> span S" and "dependent (insert a S)"
  shows "dependent S"
    is vector_space.dependent_insertD.

tts_lemma independent_insertI:
  assumes "a \<in> U\<^sub>V\<^sub>S" and "S \<subseteq> U\<^sub>V\<^sub>S" and "a \<notin> span S" and "\<not> dependent S"
  shows "\<not> dependent (insert a S)"
    is vector_space.independent_insertI.

tts_lemma independent_insert:
  assumes "a \<in> U\<^sub>V\<^sub>S" and "S \<subseteq> U\<^sub>V\<^sub>S"
  shows "(\<not> dependent (insert a S)) = 
    (if a \<in> S then \<not> dependent S else \<not> dependent S \<and> a \<notin> span S)"
    is vector_space.independent_insert.

tts_lemma maximal_independent_subset_extend["consumes" - 1, "case_names" "1"]:
  assumes "S \<subseteq> U\<^sub>V\<^sub>S"
    and "V \<subseteq> U\<^sub>V\<^sub>S"
    and "S \<subseteq> V"
    and "\<not> dependent S"
    and "\<And>B. \<lbrakk>B \<subseteq> U\<^sub>V\<^sub>S; S \<subseteq> B; B \<subseteq> V; \<not> dependent B; V \<subseteq> span B\<rbrakk> \<Longrightarrow> thesis"
  shows thesis
    is vector_space.maximal_independent_subset_extend.

tts_lemma maximal_independent_subset["consumes" - 1, "case_names" "1"]:
  assumes "V \<subseteq> U\<^sub>V\<^sub>S"
    and "\<And>B. \<lbrakk>B \<subseteq> U\<^sub>V\<^sub>S; B \<subseteq> V; \<not> dependent B; V \<subseteq> span B\<rbrakk> \<Longrightarrow> thesis"
  shows thesis
    is vector_space.maximal_independent_subset.

tts_lemma in_span_delete:
  assumes "a \<in> U\<^sub>V\<^sub>S"
    and "S \<subseteq> U\<^sub>V\<^sub>S"
    and "b \<in> U\<^sub>V\<^sub>S"
    and "a \<in> span S"
    and "a \<notin> span (S - {b})"
  shows "b \<in> span (insert a (S - {b}))"
    is vector_space.in_span_delete.

tts_lemma span_redundant:
  assumes "x \<in> U\<^sub>V\<^sub>S" and "S \<subseteq> U\<^sub>V\<^sub>S" and "x \<in> span S"
  shows "span (insert x S) = span S"
    is vector_space.span_redundant.

tts_lemma span_trans:
  assumes "x \<in> U\<^sub>V\<^sub>S"
    and "S \<subseteq> U\<^sub>V\<^sub>S"
    and "y \<in> U\<^sub>V\<^sub>S"
    and "x \<in> span S"
    and "y \<in> span (insert x S)"
  shows "y \<in> span S"
    is vector_space.span_trans.

tts_lemma span_insert_0:
  assumes "S \<subseteq> U\<^sub>V\<^sub>S"
  shows "span (insert 0 S) = span S"
    is vector_space.span_insert_0.

tts_lemma span_delete_0:
  assumes "S \<subseteq> U\<^sub>V\<^sub>S"
  shows "span (S - {0}) = span S"
    is vector_space.span_delete_0.

tts_lemma span_image_scale:
  assumes "S \<subseteq> U\<^sub>V\<^sub>S" and "finite S" and "\<And>x. \<lbrakk>x \<in> U\<^sub>V\<^sub>S; x \<in> S\<rbrakk> \<Longrightarrow> c x \<noteq> 0"
  shows "span ((\<lambda>x. c x *s x) ` S) = span S"
    is vector_space.span_image_scale.

tts_lemma exchange_lemma:
  assumes "T \<subseteq> U\<^sub>V\<^sub>S"
    and "S \<subseteq> U\<^sub>V\<^sub>S"
    and "finite T"
    and "\<not>dependent S"
    and "S \<subseteq> span T"
  shows "\<exists>t'\<in>Pow U\<^sub>V\<^sub>S. 
    card t' = card T \<and> finite t' \<and> S \<subseteq> t' \<and> t' \<subseteq> S \<union> T \<and> S \<subseteq> span t'"
    is vector_space.exchange_lemma.

tts_lemma independent_span_bound:
  assumes "T \<subseteq> U\<^sub>V\<^sub>S"
    and "S \<subseteq> U\<^sub>V\<^sub>S"
    and "finite T"
    and "\<not> dependent S"
    and "S \<subseteq> span T"
  shows "finite S \<and> card S \<le> card T"
    is vector_space.independent_span_bound.

tts_lemma independent_explicit_finite_subsets:
  assumes "A \<subseteq> U\<^sub>V\<^sub>S"
  shows "(\<not> dependent A) = 
    (
      \<forall>x\<subseteq>U\<^sub>V\<^sub>S. 
        x \<subseteq> A \<longrightarrow> 
        finite x \<longrightarrow> 
        (\<forall>f. (\<Sum>v\<in>x. f v *s v) = 0 \<longrightarrow> (\<forall>x\<in>x. f x = 0))
    )"
    given vector_space.independent_explicit_finite_subsets by auto

tts_lemma independent_if_scalars_zero:
  assumes "A \<subseteq> U\<^sub>V\<^sub>S"
    and "finite A"
    and "\<And>f x. \<lbrakk>x \<in> U\<^sub>V\<^sub>S; (\<Sum>x\<in>A. f x *s x) = 0; x \<in> A\<rbrakk> \<Longrightarrow> f x = 0"
  shows "\<not> dependent A"
    is vector_space.independent_if_scalars_zero.

tts_lemma subspace_sums:
  assumes "S \<subseteq> U\<^sub>V\<^sub>S" and "T \<subseteq> U\<^sub>V\<^sub>S" and "subspace S" and "subspace T"
  shows "subspace {x \<in> U\<^sub>V\<^sub>S. \<exists>a\<in>U\<^sub>V\<^sub>S. \<exists>b\<in>U\<^sub>V\<^sub>S. x = a + b \<and> a \<in> S \<and> b \<in> T}"
    is vector_space.subspace_sums.

tts_lemma bij_if_span_eq_span_bases:
  assumes "B \<subseteq> U\<^sub>V\<^sub>S"
    and "C \<subseteq> U\<^sub>V\<^sub>S"
    and "\<not>dependent B"
    and "\<not>dependent C"
    and "span B = span C"
  shows "\<exists>x. bij_betw x B C \<and> (\<forall>a\<in>U\<^sub>V\<^sub>S. x a \<in> U\<^sub>V\<^sub>S)"
    given vector_space.bij_if_span_eq_span_bases by blast

end

end



subsection\<open>Transfer: \<open>dim\<close>\<close>

context vector_space_on
begin

lemma dim_eq_card:
  assumes "B \<subseteq> U\<^sub>V\<^sub>S"
    and "V \<subseteq> U\<^sub>V\<^sub>S"
    and BV: "span B = span V" 
    and B: "\<not>dependent B"
  shows "dim V = card B"
proof-
  define p where "p b \<equiv> b \<subseteq> U\<^sub>V\<^sub>S \<and> \<not>dependent b \<and> span b = span V" for b
  from assms have "p (SOME B. p B)"
    by (intro someI[of p B], unfold p_def) simp
  then have "\<exists>f. bij_betw f B (SOME B. p B) \<and> (\<forall>x\<in>U\<^sub>V\<^sub>S. f x \<in> U\<^sub>V\<^sub>S)"
    by (subst (asm) p_def, intro bij_if_span_eq_span_bases) (simp_all add: assms)
  then have "card B = card (SOME B. p B)" by (auto intro: bij_betw_same_card)
  then show ?thesis using assms(1,3,4) unfolding dim_def p_def by auto
qed

lemma dim_transfer[transfer_rule]: 
  includes lifting_syntax                               
  assumes [transfer_domain_rule]: "Domainp A = (\<lambda>x. x \<in> U\<^sub>V\<^sub>S)"
    and [transfer_rule]: "right_total A" "bi_unique A"
    and [transfer_rule]: "(A ===> A ===> A) plus plus'"
    and [transfer_rule]: "((=) ===> A ===> A) scale scale'"
    and [transfer_rule]: "A 0 zero'"
  shows "(rel_set A ===> (=)) dim (dim.with plus' zero' 0 scale')"
proof(rule rel_funI)
  
  (* preliminaries *)
  have rt_rlA: "right_total (rel_set A)"
    using assms using right_total_rel_set by auto
  have Dom_rsA: "Domainp (rel_set A) x = (x \<subseteq> U\<^sub>V\<^sub>S)" for x
    by (meson Domainp_set assms(1) in_mono subsetI)

  (* hypothesis and preliminary derived results *)
  fix V V' assume [transfer_rule]: "rel_set A V V'"
  with assms have subset: "V \<subseteq> U\<^sub>V\<^sub>S" 
    by (metis Domainp.DomainI rel_setD1 subsetI)
  then have "span V \<subseteq> U\<^sub>V\<^sub>S" by (simp add: span_minimal subspace_UNIV)

  (* convenience definitions *)
  define P' where "P' =
    (
      \<exists>b. 
        (with 0 zero' plus' scale' : \<guillemotleft>independent\<guillemotright> b) \<and> 
        (with zero' plus' scale' : \<guillemotleft>span\<guillemotright> b) = 
          (with zero' plus' scale' : \<guillemotleft>span\<guillemotright> V')
    )"
  define P where "P = 
    (\<exists>b\<subseteq>U\<^sub>V\<^sub>S. \<not> dependent b \<and> span b = span V)"
  have "P = P'" 
    unfolding P_def P'_def by (transfer, unfold tts_implicit) blast
  define f where "f b = (b \<subseteq> U\<^sub>V\<^sub>S \<and> \<not> dependent b \<and> span b = span V)" for b
  define f' where "f' b = (b \<subseteq> U\<^sub>V\<^sub>S \<and> f b)" for b
  have "f = f'" unfolding f'_def f_def by simp
  define g where "g b = 
    (
      (with 0 zero' plus' scale' : \<guillemotleft>independent\<guillemotright> b) \<and> 
      (with zero' plus' scale': \<guillemotleft>span\<guillemotright> b) = 
      (with zero' plus' scale' : \<guillemotleft>span\<guillemotright> V')
    )"
    for b
  define g' where "g' b = (b \<subseteq> UNIV \<and> g b)" for b
  have "g = g'" unfolding g_def g'_def by simp

  (* towards Eps_unique_transfer_lemma *)
  have fg[transfer_rule]: "(rel_set A ===> (=)) f g"
    unfolding \<open>g = g'\<close> 
    unfolding f_def g'_def g_def tts_implicit[symmetric]
    apply transfer_prover_start
    apply transfer_step+
    by simp
  have ex_Dom_rsA: "\<exists>x. Domainp (rel_set A) x \<and> f x"
    unfolding Dom_rsA f_def 
    by 
      (
        meson   
          \<open>span V \<subseteq> U\<^sub>V\<^sub>S\<close> 
          maximal_independent_subset 
          span_subspace 
          subspace_span 
          subset
      )
  have card_xy: "\<And>x y. \<lbrakk>g x; g y\<rbrakk> \<Longrightarrow> card x = card y"
    by (transfer, unfold f_def) (metis dim_eq_card)

  (* main *)
  show "dim V = dim.with plus' zero' 0 scale' V'"
  proof(cases \<open>P'\<close>)
    case True
    then have P unfolding \<open>P = P'\<close> .
    then have dim: "dim V = card (SOME b. f b)"
      unfolding dim_def P_def f_def by simp
    from True have dw: "dim.with plus' zero' 0 scale' V' = card (SOME b. g b)"
      unfolding dim.with_def P'_def g_def by simp
    from Eps_unique_transfer_lemma[
        OF rt_rlA fg card_transfer[OF \<open>bi_unique A\<close>] ex_Dom_rsA card_xy, 
        simplified,
        unfolded Dom_rsA,
        folded f'_def \<open>f = f'\<close>
        ]
    show "dim V = dim.with plus' zero' 0 scale' V'" 
      unfolding dim dw by simp
  next
    case False
    then have "\<not>P" unfolding \<open>P = P'\<close> .
    then have dim: "dim V = 0" unfolding dim_def P_def by auto 
    moreover from False have dw: "dim.with plus' zero'  0 scale' V' = 0"
      unfolding dim.with_def P'_def g_def by auto
    ultimately show ?thesis by simp
  qed

qed

end



subsection\<open>Relativization: part II\<close>

context vector_space_on
begin

tts_context
  tts: (?'b to \<open>U\<^sub>V\<^sub>S::'b set\<close>)
  sbterms: (\<open>(+)::?'b::ab_group_add\<Rightarrow>?'b\<Rightarrow>?'b\<close> to \<open>(+)::'b\<Rightarrow>'b\<Rightarrow>'b\<close>)
    and 
      (
        \<open>?scale::?'a::field \<Rightarrow>?'b::ab_group_add\<Rightarrow>?'b::ab_group_add\<close> to 
        \<open>(*s)::'a\<Rightarrow>'b\<Rightarrow>'b\<close>
      )
    and (\<open>0::?'b::ab_group_add\<close> to \<open>0::'b\<close>)
  rewriting ctr_simps
  substituting ab_group_add_ow_axioms 
    and vector_space_ow_axioms
    and implicit\<^sub>M.module_ow_axioms
  eliminating \<open>?a \<in> ?A\<close> and \<open>?B \<subseteq> ?C\<close> through auto
  applying 
    [
      OF 
        implicit\<^sub>M.carrier_ne 
        implicit\<^sub>V\<^sub>S.minus_closed' 
        implicit\<^sub>V\<^sub>S.uminus_closed', 
      unfolded tts_implicit
     ]
begin

tts_lemma dim_unique:
  assumes "V \<subseteq> U\<^sub>V\<^sub>S"
    and "B \<subseteq> V"
    and "V \<subseteq> span B"
    and "\<not> dependent B"
    and "card B = n"
  shows "dim V = n"
    is vector_space.dim_unique.
    
tts_lemma basis_card_eq_dim:
  assumes "V \<subseteq> U\<^sub>V\<^sub>S" and "B \<subseteq> V" and "V \<subseteq> span B" and "\<not> dependent B"
  shows "card B = dim V"
    is vector_space.basis_card_eq_dim.
    
tts_lemma dim_eq_card_independent:
  assumes "B \<subseteq> U\<^sub>V\<^sub>S" and "\<not> dependent B"
  shows "dim B = card B"
    is vector_space.dim_eq_card_independent.

tts_lemma dim_span:
  assumes "S \<subseteq> U\<^sub>V\<^sub>S"
  shows "dim (span S) = dim S"
    is vector_space.dim_span.

tts_lemma dim_span_eq_card_independent:
  assumes "B \<subseteq> U\<^sub>V\<^sub>S" and "\<not> dependent B"
  shows "dim (span B) = card B"
    is vector_space.dim_span_eq_card_independent.

tts_lemma dim_le_card:
  assumes "V \<subseteq> U\<^sub>V\<^sub>S" and "W \<subseteq> U\<^sub>V\<^sub>S" and "V \<subseteq> span W" and "finite W"
  shows "dim V \<le> card W"
    is vector_space.dim_le_card.

tts_lemma span_eq_dim:
  assumes "S \<subseteq> U\<^sub>V\<^sub>S" and "T \<subseteq> U\<^sub>V\<^sub>S" and "span S = span T"
  shows "dim S = dim T"
    is vector_space.span_eq_dim.

tts_lemma dim_le_card':
  assumes "s \<subseteq> U\<^sub>V\<^sub>S" and "finite s"
  shows "dim s \<le> card s"
    is vector_space.dim_le_card'.

tts_lemma span_card_ge_dim:
  assumes "V \<subseteq> U\<^sub>V\<^sub>S" and "B \<subseteq> V" and "V \<subseteq> span B" and "finite B"
  shows "dim V \<le> card B"
    is vector_space.span_card_ge_dim.

end

tts_context
  tts: (?'b to \<open>U\<^sub>V\<^sub>S::'b set\<close>) 
  sbterms: (\<open>(+)::?'b::ab_group_add\<Rightarrow>?'b\<Rightarrow>?'b\<close> to \<open>(+)::'b\<Rightarrow>'b\<Rightarrow>'b\<close>)
    and (\<open>?scale::?'a::field \<Rightarrow>?'b::ab_group_add\<Rightarrow>?'b\<close> to \<open>(*s)::'a\<Rightarrow>'b\<Rightarrow>'b\<close>)
    and (\<open>0::?'b::ab_group_add\<close> to \<open>0::'b\<close>)
  rewriting ctr_simps
  substituting ab_group_add_ow_axioms 
    and vector_space_ow_axioms
    and implicit\<^sub>M.module_ow_axioms
  applying 
    [
      OF 
        implicit\<^sub>M.carrier_ne 
        implicit\<^sub>V\<^sub>S.minus_closed' 
        implicit\<^sub>V\<^sub>S.uminus_closed', 
        unfolded tts_implicit
     ]
begin
  
tts_lemma basis_exists:
  assumes "V \<subseteq> U\<^sub>V\<^sub>S"
    and "\<And>B. 
      \<lbrakk>
        B \<subseteq> U\<^sub>V\<^sub>S; 
        B \<subseteq> V; 
        \<not> dependent B; 
        V \<subseteq> span B; 
        card B = dim V
      \<rbrakk> \<Longrightarrow> thesis"
  shows thesis
    is vector_space.basis_exists.

end

end

context finite_dimensional_vector_space_on 
begin

tts_context
  tts: (?'b to \<open>U\<^sub>V\<^sub>S::'b set\<close>)
  sbterms: (\<open>(+)::?'b::ab_group_add\<Rightarrow>?'b\<Rightarrow>?'b\<close> to \<open>(+)::'b\<Rightarrow>'b\<Rightarrow>'b\<close>)
    and (\<open>?scale::?'a::field \<Rightarrow>?'b::ab_group_add\<Rightarrow>?'b\<close> to \<open>(*s)::'a\<Rightarrow>'b\<Rightarrow>'b\<close>)
    and (\<open>0::?'b::ab_group_add\<close> to \<open>0::'b\<close>)
  rewriting ctr_simps
  substituting ab_group_add_ow_axioms
    and vector_space_ow_axioms
    and implicit\<^sub>V\<^sub>S.finite_dimensional_vector_space_ow_axioms
    and implicit\<^sub>M.module_ow_axioms
  eliminating \<open>?a \<in> ?A\<close> and \<open>?B \<subseteq> ?C\<close> through auto
  applying 
    [
      OF 
        implicit\<^sub>M.carrier_ne 
        implicit\<^sub>V\<^sub>S.minus_closed' 
        implicit\<^sub>V\<^sub>S.uminus_closed' 
        basis_subset, 
      unfolded tts_implicit
    ]
begin

tts_lemma finiteI_independent:
  assumes "B \<subseteq> U\<^sub>V\<^sub>S" and "\<not> dependent B"
  shows "finite B"
  is finite_dimensional_vector_space.finiteI_independent.

tts_lemma dim_empty: "dim {} = 0"
  is finite_dimensional_vector_space.dim_empty.
    
tts_lemma dim_insert:
  assumes "x \<in> U\<^sub>V\<^sub>S" and "S \<subseteq> U\<^sub>V\<^sub>S"
  shows "dim (insert x S) = (if x \<in> span S then dim S else dim S + 1)"
    is finite_dimensional_vector_space.dim_insert.
    
tts_lemma dim_singleton:
  assumes "x \<in> U\<^sub>V\<^sub>S"
  shows "dim {x} = (if x = 0 then 0 else 1)"
    is finite_dimensional_vector_space.dim_singleton.

tts_lemma choose_subspace_of_subspace["consumes" - 1, "case_names" "1"]:
  assumes "S \<subseteq> U\<^sub>V\<^sub>S"
    and "n \<le> dim S"
    and "\<And>T. \<lbrakk>T \<subseteq> U\<^sub>V\<^sub>S; subspace T; T \<subseteq> span S; dim T = n\<rbrakk> \<Longrightarrow> thesis"
  shows thesis
    is finite_dimensional_vector_space.choose_subspace_of_subspace.

tts_lemma basis_subspace_exists["consumes" - 1, "case_names" "1"]:
  assumes "S \<subseteq> U\<^sub>V\<^sub>S"
    and "subspace S"
    and "\<And>B. 
      \<lbrakk>
        B \<subseteq> U\<^sub>V\<^sub>S; 
        finite B; 
        B \<subseteq> S; 
        \<not> dependent B; 
        span B = S; 
        card B = dim S
      \<rbrakk> \<Longrightarrow> thesis"
  shows thesis
    is finite_dimensional_vector_space.basis_subspace_exists.

tts_lemma dim_mono:
  assumes "V \<subseteq> U\<^sub>V\<^sub>S" and "W \<subseteq> U\<^sub>V\<^sub>S" and "V \<subseteq> span W"
  shows "dim V \<le> dim W"
    is finite_dimensional_vector_space.dim_mono.

tts_lemma dim_subset:
  assumes "T \<subseteq> U\<^sub>V\<^sub>S" and "S \<subseteq> T"
  shows "dim S \<le> dim T"
    is finite_dimensional_vector_space.dim_subset.

tts_lemma dim_eq_0:
  assumes "S \<subseteq> U\<^sub>V\<^sub>S"
  shows "(dim S = 0) = (S \<subseteq> {0})"
    is finite_dimensional_vector_space.dim_eq_0.

tts_lemma dim_UNIV: "dim U\<^sub>V\<^sub>S = card basis"
    is finite_dimensional_vector_space.dim_UNIV.

tts_lemma independent_card_le_dim:
  assumes "V \<subseteq> U\<^sub>V\<^sub>S" and "B \<subseteq> V" and "\<not> dependent B"
  shows "card B \<le> dim V"
    is finite_dimensional_vector_space.independent_card_le_dim.

tts_lemma card_ge_dim_independent:
  assumes "V \<subseteq> U\<^sub>V\<^sub>S" and "B \<subseteq> V" and "\<not> dependent B" and "dim V \<le> card B"
  shows "V \<subseteq> span B"
    is finite_dimensional_vector_space.card_ge_dim_independent.

tts_lemma card_le_dim_spanning:
  assumes "V \<subseteq> U\<^sub>V\<^sub>S"
    and "B \<subseteq> V"
    and "V \<subseteq> span B"
    and "finite B"
    and "card B \<le> dim V"
  shows "\<not> dependent B"
    is finite_dimensional_vector_space.card_le_dim_spanning.

tts_lemma card_eq_dim:
  assumes "V \<subseteq> U\<^sub>V\<^sub>S" and "B \<subseteq> V" and "card B = dim V" and "finite B"
  shows "(\<not> dependent B) = (V \<subseteq> span B)"
    is finite_dimensional_vector_space.card_eq_dim.

tts_lemma subspace_dim_equal:
  assumes "T \<subseteq> U\<^sub>V\<^sub>S"
    and "subspace S"
    and "subspace T"
    and "S \<subseteq> T"
    and "dim T \<le> dim S"
  shows "S = T"
    is finite_dimensional_vector_space.subspace_dim_equal.

tts_lemma dim_eq_span:
  assumes "T \<subseteq> U\<^sub>V\<^sub>S" and "S \<subseteq> T" and "dim T \<le> dim S"
  shows "span S = span T"
    is finite_dimensional_vector_space.dim_eq_span.

tts_lemma dim_psubset:
  assumes "S \<subseteq> U\<^sub>V\<^sub>S" and "T \<subseteq> U\<^sub>V\<^sub>S" and "span S \<subset> span T"
  shows "dim S < dim T"
    is finite_dimensional_vector_space.dim_psubset.

tts_lemma indep_card_eq_dim_span:
  assumes "B \<subseteq> U\<^sub>V\<^sub>S" and "\<not> dependent B"
  shows "finite B \<and> card B = dim (span B)"
    is finite_dimensional_vector_space.indep_card_eq_dim_span.

tts_lemma independent_bound_general:
  assumes "S \<subseteq> U\<^sub>V\<^sub>S" and "\<not> dependent S"
  shows "finite S \<and> card S \<le> dim S"
    is finite_dimensional_vector_space.independent_bound_general.

tts_lemma independent_explicit:
  assumes "B \<subseteq> U\<^sub>V\<^sub>S"
  shows "(\<not> dependent B) = 
    (finite B \<and> (\<forall>x. (\<Sum>v\<in>B. x v *s v) = 0 \<longrightarrow> (\<forall>a\<in>B. x a = 0)))"
    is finite_dimensional_vector_space.independent_explicit.

tts_lemma dim_sums_Int:
  assumes "S \<subseteq> U\<^sub>V\<^sub>S" and "T \<subseteq> U\<^sub>V\<^sub>S" and "subspace S" and "subspace T"
  shows 
    "dim {x \<in> U\<^sub>V\<^sub>S. \<exists>y\<in>U\<^sub>V\<^sub>S. \<exists>z\<in>U\<^sub>V\<^sub>S. x = y + z \<and> y \<in> S \<and> z \<in> T} + dim (S \<inter> T) = 
      dim S + dim T"
    is finite_dimensional_vector_space.dim_sums_Int.

tts_lemma dependent_biggerset_general:
  assumes "S \<subseteq> U\<^sub>V\<^sub>S" and "finite S \<Longrightarrow> dim S < card S"
  shows "dependent S"
    is finite_dimensional_vector_space.dependent_biggerset_general.

tts_lemma subset_le_dim:
  assumes "S \<subseteq> U\<^sub>V\<^sub>S" and "T \<subseteq> U\<^sub>V\<^sub>S" and "S \<subseteq> span T"
  shows "dim S \<le> dim T"
    is finite_dimensional_vector_space.subset_le_dim.

tts_lemma linear_inj_imp_surj:
  assumes "\<forall>x\<in>U\<^sub>V\<^sub>S. f x \<in> U\<^sub>V\<^sub>S"
    and "linear_on U\<^sub>V\<^sub>S U\<^sub>V\<^sub>S (*s) (*s) f"
    and "inj_on f U\<^sub>V\<^sub>S"
  shows "f ` U\<^sub>V\<^sub>S = U\<^sub>V\<^sub>S"
    is finite_dimensional_vector_space.linear_inj_imp_surj.

tts_lemma linear_surj_imp_inj:
  assumes "\<forall>x\<in>U\<^sub>V\<^sub>S. f x \<in> U\<^sub>V\<^sub>S"
    and "linear_on U\<^sub>V\<^sub>S U\<^sub>V\<^sub>S (*s) (*s) f"
    and "f ` U\<^sub>V\<^sub>S = U\<^sub>V\<^sub>S"
  shows "inj_on f U\<^sub>V\<^sub>S"
    is finite_dimensional_vector_space.linear_surj_imp_inj.

tts_lemma linear_inverse_left:
  assumes "\<forall>x\<in>U\<^sub>V\<^sub>S. f x \<in> U\<^sub>V\<^sub>S"
    and "\<forall>x\<in>U\<^sub>V\<^sub>S. f' x \<in> U\<^sub>V\<^sub>S"
    and "linear_on U\<^sub>V\<^sub>S U\<^sub>V\<^sub>S (*s) (*s) f"
    and "linear_on U\<^sub>V\<^sub>S U\<^sub>V\<^sub>S (*s) (*s) f'"
  shows "(\<forall>x\<in>U\<^sub>V\<^sub>S. (f \<circ> f') x = id x) = (\<forall>x\<in>U\<^sub>V\<^sub>S. (f' \<circ> f) x = id x)"
    is finite_dimensional_vector_space.linear_inverse_left[unfolded fun_eq_iff].

tts_lemma left_inverse_linear:
  assumes "\<forall>x\<in>U\<^sub>V\<^sub>S. f x \<in> U\<^sub>V\<^sub>S"
    and "\<forall>x\<in>U\<^sub>V\<^sub>S. g x \<in> U\<^sub>V\<^sub>S"
    and "linear_on U\<^sub>V\<^sub>S U\<^sub>V\<^sub>S (*s) (*s) f"
    and "\<forall>x\<in>U\<^sub>V\<^sub>S. (g \<circ> f) x = id x"
  shows "linear_on U\<^sub>V\<^sub>S U\<^sub>V\<^sub>S (*s) (*s) g"
    is finite_dimensional_vector_space.left_inverse_linear[unfolded fun_eq_iff].

tts_lemma right_inverse_linear:
  assumes "\<forall>x\<in>U\<^sub>V\<^sub>S. f x \<in> U\<^sub>V\<^sub>S"
    and "\<forall>x\<in>U\<^sub>V\<^sub>S. g x \<in> U\<^sub>V\<^sub>S"
    and "linear_on U\<^sub>V\<^sub>S U\<^sub>V\<^sub>S (*s) (*s) f"
    and "\<forall>x\<in>U\<^sub>V\<^sub>S. (f \<circ> g) x = id x"
  shows "linear_on U\<^sub>V\<^sub>S U\<^sub>V\<^sub>S (*s) (*s) g"
    is finite_dimensional_vector_space.right_inverse_linear[unfolded fun_eq_iff].

end

end

context vector_space_pair_on 
begin

tts_context
  tts: (?'b to \<open>U\<^sub>M\<^sub>_\<^sub>1::'b set\<close>) and (?'c to \<open>U\<^sub>M\<^sub>_\<^sub>2::'c set\<close>) 
  sbterms: (\<open>(+)::?'b::ab_group_add\<Rightarrow>?'b\<Rightarrow>?'b\<close> to \<open>(+)::'b\<Rightarrow>'b\<Rightarrow>'b\<close>)
    and (\<open>?s1.0::?'a::field \<Rightarrow>?'b::ab_group_add\<Rightarrow>?'b\<close> to \<open>(*s\<^sub>1)::'a\<Rightarrow>'b\<Rightarrow>'b\<close>)
    and (\<open>0::?'b::ab_group_add\<close> to \<open>0::'b\<close>) 
    and (\<open>(+)::?'c::ab_group_add\<Rightarrow>?'c\<Rightarrow>?'c\<close> to \<open>(+)::'c\<Rightarrow>'c\<Rightarrow>'c\<close>)
    and (\<open>?s2.0::?'a::field \<Rightarrow>?'c::ab_group_add\<Rightarrow>?'c\<close> to \<open>(*s\<^sub>2)::'a\<Rightarrow>'c\<Rightarrow>'c\<close>)
    and (\<open>0::?'c::ab_group_add\<close> to \<open>0::'c\<close>)
  rewriting ctr_simps
  substituting VS\<^sub>1.ab_group_add_ow_axioms
    and VS\<^sub>1.vector_space_ow_axioms
    and VS\<^sub>2.ab_group_add_ow_axioms
    and VS\<^sub>2.vector_space_ow_axioms
    and implicit\<^sub>V\<^sub>S.vector_space_pair_ow_axioms
    and VS\<^sub>1.implicit\<^sub>M.module_ow_axioms
    and VS\<^sub>2.implicit\<^sub>M.module_ow_axioms
  eliminating \<open>?a \<in> U\<^sub>M\<^sub>_\<^sub>1\<close> and \<open>?B \<subseteq> U\<^sub>M\<^sub>_\<^sub>1\<close> and \<open>?a \<in> U\<^sub>M\<^sub>_\<^sub>2\<close> and \<open>?B \<subseteq> U\<^sub>M\<^sub>_\<^sub>2\<close> 
    through auto
  applying  
    [
      OF 
        VS\<^sub>1.implicit\<^sub>M.carrier_ne VS\<^sub>2.implicit\<^sub>M.carrier_ne 
        VS\<^sub>1.implicit\<^sub>M.minus_closed' VS\<^sub>1.implicit\<^sub>M.uminus_closed' 
        VS\<^sub>2.implicit\<^sub>V\<^sub>S.minus_closed' VS\<^sub>2.implicit\<^sub>V\<^sub>S.uminus_closed',
      unfolded tts_implicit
    ]
begin

tts_lemma linear_add:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "b1 \<in> U\<^sub>M\<^sub>_\<^sub>1"
    and "b2 \<in> U\<^sub>M\<^sub>_\<^sub>1"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
  shows "f (b1 + b2) = f b1 + f b2"
    is vector_space_pair.linear_add.

tts_lemma linear_scale:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "b \<in> U\<^sub>M\<^sub>_\<^sub>1"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
  shows "f (r *s\<^sub>1 b) = r *s\<^sub>2 f b"
    is vector_space_pair.linear_scale.
    
tts_lemma linear_neg:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "x \<in> U\<^sub>M\<^sub>_\<^sub>1"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
  shows "f (- x) = - f x"
    is vector_space_pair.linear_neg.
    
tts_lemma linear_diff:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "x \<in> U\<^sub>M\<^sub>_\<^sub>1"
    and "y \<in> U\<^sub>M\<^sub>_\<^sub>1"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
  shows "f (x - y) = f x - f y"
    is vector_space_pair.linear_diff.
    
tts_lemma linear_sum:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "range g \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
  shows "f (sum g S) = (\<Sum>a\<in>S. f (g a))"
is vector_space_pair.linear_sum.

tts_lemma linear_inj_on_iff_eq_0:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "s \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "VS\<^sub>1.subspace s"
  shows "inj_on f s = (\<forall>x\<in>s. f x = 0 \<longrightarrow> x = 0)"
    is vector_space_pair.linear_inj_on_iff_eq_0.

tts_lemma linear_inj_iff_eq_0:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
  shows "inj_on f U\<^sub>M\<^sub>_\<^sub>1 = (\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x = 0 \<longrightarrow> x = 0)"
    is vector_space_pair.linear_inj_iff_eq_0.

tts_lemma linear_subspace_image:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "S \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "VS\<^sub>1.subspace S"
  shows "VS\<^sub>2.subspace (f ` S)"
    is vector_space_pair.linear_subspace_image.

tts_lemma linear_subspace_kernel:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
  shows "VS\<^sub>1.subspace {x \<in> U\<^sub>M\<^sub>_\<^sub>1. f x = 0}"
    is vector_space_pair.linear_subspace_kernel.

tts_lemma linear_span_image:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "S \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
  shows "VS\<^sub>2.span (f ` S) = f ` VS\<^sub>1.span S"
    is vector_space_pair.linear_span_image.

tts_lemma linear_dependent_inj_imageD:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "s \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "VS\<^sub>2.dependent (f ` s)"
    and "inj_on f (VS\<^sub>1.span s)"
  shows "VS\<^sub>1.dependent s"
    is vector_space_pair.linear_dependent_inj_imageD.

tts_lemma linear_eq_0_on_span:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "b \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "x \<in> U\<^sub>M\<^sub>_\<^sub>1"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "\<And>x. \<lbrakk>x \<in> U\<^sub>M\<^sub>_\<^sub>1; x \<in> b\<rbrakk> \<Longrightarrow> f x = 0"
    and "x \<in> VS\<^sub>1.span b"
  shows "f x = 0"
    is vector_space_pair.linear_eq_0_on_span.

tts_lemma linear_independent_injective_image:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "s \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "\<not> VS\<^sub>1.dependent s"
    and "inj_on f (VS\<^sub>1.span s)"
  shows "\<not> VS\<^sub>2.dependent (f ` s)"
    is vector_space_pair.linear_independent_injective_image.

tts_lemma linear_inj_on_span_independent_image:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "B \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "\<not> VS\<^sub>2.dependent (f ` B)"
    and "inj_on f B"
  shows "inj_on f (VS\<^sub>1.span B)"
    is vector_space_pair.linear_inj_on_span_independent_image.

tts_lemma linear_inj_on_span_iff_independent_image:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "B \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "\<not> VS\<^sub>2.dependent (f ` B)"
  shows "inj_on f (VS\<^sub>1.span B) = inj_on f B"
    is vector_space_pair.linear_inj_on_span_iff_independent_image.

tts_lemma linear_subspace_linear_preimage:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "S \<subseteq> U\<^sub>M\<^sub>_\<^sub>2"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "VS\<^sub>2.subspace S"
  shows "VS\<^sub>1.subspace {x \<in> U\<^sub>M\<^sub>_\<^sub>1. f x \<in> S}"
    is vector_space_pair.linear_subspace_linear_preimage.

tts_lemma linear_spans_image:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "V \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "B \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "V \<subseteq> VS\<^sub>1.span B"
  shows "f ` V \<subseteq> VS\<^sub>2.span (f ` B)"
    is vector_space_pair.linear_spans_image.

tts_lemma linear_spanning_surjective_image:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "S \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "U\<^sub>M\<^sub>_\<^sub>1 \<subseteq> VS\<^sub>1.span S"
    and "f ` U\<^sub>M\<^sub>_\<^sub>1 = U\<^sub>M\<^sub>_\<^sub>2"
  shows "U\<^sub>M\<^sub>_\<^sub>2 \<subseteq> VS\<^sub>2.span (f ` S)"
    is vector_space_pair.linear_spanning_surjective_image.

tts_lemma linear_eq_on_span:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. g x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "B \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "x \<in> U\<^sub>M\<^sub>_\<^sub>1"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) g"
    and "\<And>x. \<lbrakk>x \<in> U\<^sub>M\<^sub>_\<^sub>1; x \<in> B\<rbrakk> \<Longrightarrow> f x = g x"
    and "x \<in> VS\<^sub>1.span B"
  shows "f x = g x"
    is vector_space_pair.linear_eq_on_span.

tts_lemma linear_compose_scale_right:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
  shows "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) (\<lambda>x. c *s\<^sub>2 f x)"
    is vector_space_pair.linear_compose_scale_right.

tts_lemma linear_compose_add:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. g x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) g"
  shows "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) (\<lambda>x. f x + g x)"
    is vector_space_pair.linear_compose_add.

tts_lemma linear_zero:
  shows "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) (\<lambda>x. 0)"
    is vector_space_pair.linear_zero.

tts_lemma linear_compose_sub:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. g x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) g"
  shows "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) (\<lambda>x. f x - g x)"
    is vector_space_pair.linear_compose_sub.

tts_lemma linear_compose_neg:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
  shows "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) (\<lambda>x. - f x)"
    is vector_space_pair.linear_compose_neg.

tts_lemma linear_compose_scale:
  assumes "c \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 UNIV (*s\<^sub>1) (*) f"
  shows "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) (\<lambda>x. f x *s\<^sub>2 c)"
    is vector_space_pair.linear_compose_scale.

tts_lemma linear_indep_image_lemma:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "B \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "x \<in> U\<^sub>M\<^sub>_\<^sub>1"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "finite B"
    and "\<not> VS\<^sub>2.dependent (f ` B)"
    and "inj_on f B"
    and "x \<in> VS\<^sub>1.span B"
    and "f x = 0"
  shows "x = 0"
    is vector_space_pair.linear_indep_image_lemma.

tts_lemma linear_eq_on:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. g x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "x \<in> U\<^sub>M\<^sub>_\<^sub>1"
    and "B \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) g"
    and "x \<in> VS\<^sub>1.span B"
    and "\<And>b. \<lbrakk>b \<in> U\<^sub>M\<^sub>_\<^sub>1; b \<in> B\<rbrakk> \<Longrightarrow> f b = g b"
  shows "f x = g x"
    is vector_space_pair.linear_eq_on.

tts_lemma linear_compose_sum:
  assumes "\<forall>x. \<forall>y\<in>U\<^sub>M\<^sub>_\<^sub>1. f x y \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "\<forall>x\<in>S. linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) (f x)"
  shows "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) (\<lambda>x. \<Sum>a\<in>S. f a x)"
    is vector_space_pair.linear_compose_sum.

tts_lemma linear_independent_extend_subspace:
  assumes "B \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "\<not> VS\<^sub>1.dependent B"
  shows 
    "\<exists>x.
      (\<forall>a\<in>U\<^sub>M\<^sub>_\<^sub>1. x a \<in> U\<^sub>M\<^sub>_\<^sub>2) \<and> 
      linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) x \<and> 
      (\<forall>a\<in>B. x a = f a) \<and> 
      x ` U\<^sub>M\<^sub>_\<^sub>1 = VS\<^sub>2.span (f ` B)"
    given vector_space_pair.linear_independent_extend_subspace by auto

tts_lemma linear_independent_extend:
  assumes "B \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "\<not> VS\<^sub>1.dependent B"
  shows 
    "\<exists>x. 
      (\<forall>a\<in>U\<^sub>M\<^sub>_\<^sub>1. x a \<in> U\<^sub>M\<^sub>_\<^sub>2) \<and> 
      (\<forall>a\<in>B. x a = f a) \<and> 
      linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) x"
    given vector_space_pair.linear_independent_extend by auto

tts_lemma linear_exists_left_inverse_on:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "V \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "VS\<^sub>1.subspace V"
    and "inj_on f V"
  shows 
    "\<exists>x. 
      (\<forall>a\<in>U\<^sub>M\<^sub>_\<^sub>2. x a \<in> U\<^sub>M\<^sub>_\<^sub>1) \<and> 
      x ` U\<^sub>M\<^sub>_\<^sub>2 \<subseteq> V \<and> 
      (\<forall>a\<in>V. x (f a) = a) \<and> 
      linear_on U\<^sub>M\<^sub>_\<^sub>2 U\<^sub>M\<^sub>_\<^sub>1 (*s\<^sub>2) (*s\<^sub>1) x"
    given vector_space_pair.linear_exists_left_inverse_on by auto

tts_lemma linear_exists_right_inverse_on:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "V \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "VS\<^sub>1.subspace V"
  shows 
    "\<exists>x. 
      (\<forall>a\<in>U\<^sub>M\<^sub>_\<^sub>2. x a \<in> U\<^sub>M\<^sub>_\<^sub>1) \<and> 
      x ` U\<^sub>M\<^sub>_\<^sub>2 \<subseteq> V \<and> 
      (\<forall>a\<in>f ` V. f (x a) = a) \<and> 
      linear_on U\<^sub>M\<^sub>_\<^sub>2 U\<^sub>M\<^sub>_\<^sub>1 (*s\<^sub>2) (*s\<^sub>1) x"
    given vector_space_pair.linear_exists_right_inverse_on by auto

tts_lemma linear_inj_on_left_inverse:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "S \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "inj_on f (VS\<^sub>1.span S)"
  shows 
    "\<exists>x. 
      (\<forall>a\<in>U\<^sub>M\<^sub>_\<^sub>2. x a \<in> U\<^sub>M\<^sub>_\<^sub>1) \<and> 
      x ` U\<^sub>M\<^sub>_\<^sub>2 \<subseteq> VS\<^sub>1.span S \<and> 
      (\<forall>a\<in>VS\<^sub>1.span S. x (f a) = a) \<and> 
      linear_on U\<^sub>M\<^sub>_\<^sub>2 U\<^sub>M\<^sub>_\<^sub>1 (*s\<^sub>2) (*s\<^sub>1) x"
    given vector_space_pair.linear_inj_on_left_inverse by auto

tts_lemma linear_surj_right_inverse:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "T \<subseteq> U\<^sub>M\<^sub>_\<^sub>2"
    and "S \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "VS\<^sub>2.span T \<subseteq> f ` VS\<^sub>1.span S"
  shows 
    "\<exists>x. 
      (\<forall>a\<in>U\<^sub>M\<^sub>_\<^sub>2. x a \<in> U\<^sub>M\<^sub>_\<^sub>1) \<and> 
      x ` U\<^sub>M\<^sub>_\<^sub>2 \<subseteq> VS\<^sub>1.span S \<and> 
      (\<forall>a\<in>VS\<^sub>2.span T. f (x a) = a) \<and> 
      linear_on U\<^sub>M\<^sub>_\<^sub>2 U\<^sub>M\<^sub>_\<^sub>1 (*s\<^sub>2) (*s\<^sub>1) x"
    given vector_space_pair.linear_surj_right_inverse by auto

tts_lemma finite_basis_to_basis_subspace_isomorphism:
  assumes "S \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "T \<subseteq> U\<^sub>M\<^sub>_\<^sub>2"
    and "VS\<^sub>1.subspace S"
    and "VS\<^sub>2.subspace T"
    and "VS\<^sub>1.dim S = VS\<^sub>2.dim T"
    and "finite B"
    and "B \<subseteq> S"
    and "\<not> VS\<^sub>1.dependent B"
    and "S \<subseteq> VS\<^sub>1.span B"
    and "card B = VS\<^sub>1.dim S"
    and "finite C"
    and "C \<subseteq> T"
    and "\<not> VS\<^sub>2.dependent C"
    and "T \<subseteq> VS\<^sub>2.span C"
    and "card C = VS\<^sub>2.dim T"
  shows 
    "\<exists>x. 
      (\<forall>a\<in>U\<^sub>M\<^sub>_\<^sub>1. x a \<in> U\<^sub>M\<^sub>_\<^sub>2) \<and> 
      linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) x \<and> 
      x ` B = C \<and> 
      inj_on x S \<and> x ` S = T"
    given vector_space_pair.finite_basis_to_basis_subspace_isomorphism by auto

tts_lemma linear_subspace_vimage:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "S \<subseteq> U\<^sub>M\<^sub>_\<^sub>2"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "VS\<^sub>2.subspace S"
  shows "VS\<^sub>1.subspace (f -` S \<inter> U\<^sub>M\<^sub>_\<^sub>1)"
    is vector_space_pair.linear_subspace_vimage.

tts_lemma linear_injective_left_inverse:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "inj_on f U\<^sub>M\<^sub>_\<^sub>1"
  shows 
    "\<exists>x. 
      (\<forall>a\<in>U\<^sub>M\<^sub>_\<^sub>2. x a \<in> U\<^sub>M\<^sub>_\<^sub>1) \<and> 
      (\<forall>a\<in>U\<^sub>M\<^sub>_\<^sub>1. (x \<circ> f) a = id a) \<and> 
      linear_on U\<^sub>M\<^sub>_\<^sub>2 U\<^sub>M\<^sub>_\<^sub>1 (*s\<^sub>2) (*s\<^sub>1) x"
    given vector_space_pair.linear_injective_left_inverse[unfolded fun_eq_iff]
  by auto

tts_lemma linear_surjective_right_inverse:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "f ` U\<^sub>M\<^sub>_\<^sub>1 = U\<^sub>M\<^sub>_\<^sub>2"
  shows 
    "\<exists>x. 
      (\<forall>a\<in>U\<^sub>M\<^sub>_\<^sub>2. x a \<in> U\<^sub>M\<^sub>_\<^sub>1) \<and> 
      (\<forall>a\<in>U\<^sub>M\<^sub>_\<^sub>2. (f \<circ> x) a = id a) \<and> 
      linear_on U\<^sub>M\<^sub>_\<^sub>2 U\<^sub>M\<^sub>_\<^sub>1 (*s\<^sub>2) (*s\<^sub>1) x"
    given vector_space_pair.linear_surjective_right_inverse[unfolded fun_eq_iff]
  by auto

end

end

context finite_dimensional_vector_space_pair_1_on 
begin

tts_context
  tts: (?'b to \<open>U\<^sub>M\<^sub>_\<^sub>1::'b set\<close>) and (?'c to \<open>U\<^sub>M\<^sub>_\<^sub>2::'c set\<close>) 
  sbterms: (\<open>(+)::?'b::ab_group_add\<Rightarrow>?'b\<Rightarrow>?'b\<close> to \<open>(+)::'b\<Rightarrow>'b\<Rightarrow>'b\<close>)
    and (\<open>?s1.0::?'a::field \<Rightarrow>?'b::ab_group_add\<Rightarrow>?'b\<close> to \<open>(*s\<^sub>1)::'a\<Rightarrow>'b\<Rightarrow>'b\<close>)
    and (\<open>0::?'b::ab_group_add\<close> to \<open>0::'b\<close>) 
    and (\<open>(+)::?'c::ab_group_add\<Rightarrow>?'c\<Rightarrow>?'c\<close> to \<open>(+)::'c\<Rightarrow>'c\<Rightarrow>'c\<close>)
    and (\<open>?s2.0::?'a::field \<Rightarrow>?'c::ab_group_add\<Rightarrow>?'c\<close> to \<open>(*s\<^sub>2)::'a\<Rightarrow>'c\<Rightarrow>'c\<close>)
    and (\<open>0::?'c::ab_group_add\<close> to \<open>0::'c\<close>)
  rewriting ctr_simps
  substituting VS\<^sub>1.ab_group_add_ow_axioms
    and VS\<^sub>1.vector_space_ow_axioms
    and VS\<^sub>2.ab_group_add_ow_axioms
    and VS\<^sub>2.vector_space_ow_axioms
    and implicit\<^sub>V\<^sub>S.vector_space_pair_ow_axioms
    and VS\<^sub>1.implicit\<^sub>M.module_ow_axioms
    and VS\<^sub>2.implicit\<^sub>M.module_ow_axioms 
    and implicit\<^sub>V\<^sub>S.finite_dimensional_vector_space_pair_1_ow_axioms
  applying  
    [
      OF 
        VS\<^sub>1.implicit\<^sub>M.carrier_ne VS\<^sub>2.implicit\<^sub>M.carrier_ne 
        VS\<^sub>1.implicit\<^sub>V\<^sub>S.minus_closed' VS\<^sub>1.implicit\<^sub>V\<^sub>S.uminus_closed' 
        VS\<^sub>2.implicit\<^sub>V\<^sub>S.minus_closed' VS\<^sub>2.implicit\<^sub>V\<^sub>S.uminus_closed'
        VS\<^sub>1.basis_subset,
      unfolded tts_implicit
    ]
begin

tts_lemma lt_dim_image_eq:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "S \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "inj_on f (VS\<^sub>1.span S)"
  shows "VS\<^sub>2.dim (f ` S) = VS\<^sub>1.dim S"
    is finite_dimensional_vector_space_pair_1.dim_image_eq.

tts_lemma lt_dim_image_le:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "S \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
  shows "VS\<^sub>2.dim (f ` S) \<le> VS\<^sub>1.dim S"
    is finite_dimensional_vector_space_pair_1.dim_image_le.

end

end

context finite_dimensional_vector_space_pair_on 
begin

tts_context
  tts: (?'b to \<open>U\<^sub>M\<^sub>_\<^sub>1::'b set\<close>) and (?'c to \<open>U\<^sub>M\<^sub>_\<^sub>2::'c set\<close>) 
  sbterms: (\<open>(+)::?'b::ab_group_add\<Rightarrow>?'b\<Rightarrow>?'b\<close> to \<open>(+)::'b\<Rightarrow>'b\<Rightarrow>'b\<close>)
    and (\<open>?s1.0::?'a::field \<Rightarrow>?'b::ab_group_add\<Rightarrow>?'b\<close> to \<open>(*s\<^sub>1)::'a\<Rightarrow>'b\<Rightarrow>'b\<close>)
    and (\<open>0::?'b::ab_group_add\<close> to \<open>0::'b\<close>) 
    and (\<open>(+)::?'c::ab_group_add\<Rightarrow>?'c\<Rightarrow>?'c\<close> to \<open>(+)::'c\<Rightarrow>'c\<Rightarrow>'c\<close>)
    and (\<open>?s2.0::?'a::field \<Rightarrow>?'c::ab_group_add\<Rightarrow>?'c\<close> to \<open>(*s\<^sub>2)::'a\<Rightarrow>'c\<Rightarrow>'c\<close>)
    and (\<open>0::?'c::ab_group_add\<close> to \<open>0::'c\<close>)
  rewriting ctr_simps
  substituting VS\<^sub>1.ab_group_add_ow_axioms
    and VS\<^sub>1.vector_space_ow_axioms
    and VS\<^sub>2.ab_group_add_ow_axioms
    and VS\<^sub>2.vector_space_ow_axioms
    and implicit\<^sub>V\<^sub>S.vector_space_pair_ow_axioms
    and VS\<^sub>1.implicit\<^sub>M.module_ow_axioms
    and VS\<^sub>2.implicit\<^sub>M.module_ow_axioms 
    and implicit\<^sub>V\<^sub>S.finite_dimensional_vector_space_pair_ow_axioms
  applying  
    [
      OF 
        VS\<^sub>1.implicit\<^sub>M.carrier_ne VS\<^sub>2.implicit\<^sub>M.carrier_ne 
        VS\<^sub>1.implicit\<^sub>V\<^sub>S.minus_closed' VS\<^sub>1.implicit\<^sub>V\<^sub>S.uminus_closed' 
        VS\<^sub>2.implicit\<^sub>V\<^sub>S.minus_closed' VS\<^sub>2.implicit\<^sub>V\<^sub>S.uminus_closed'
        VS\<^sub>1.basis_subset VS\<^sub>2.basis_subset,
      unfolded tts_implicit
    ]
begin

tts_lemma linear_surjective_imp_injective:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "f ` U\<^sub>M\<^sub>_\<^sub>1 = U\<^sub>M\<^sub>_\<^sub>2"
    and "VS\<^sub>2.dim U\<^sub>M\<^sub>_\<^sub>2 = VS\<^sub>1.dim U\<^sub>M\<^sub>_\<^sub>1"
  shows "inj_on f U\<^sub>M\<^sub>_\<^sub>1"
    is finite_dimensional_vector_space_pair.linear_surjective_imp_injective.

tts_lemma linear_injective_imp_surjective:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "inj_on f U\<^sub>M\<^sub>_\<^sub>1"
    and "VS\<^sub>2.dim U\<^sub>M\<^sub>_\<^sub>2 = VS\<^sub>1.dim U\<^sub>M\<^sub>_\<^sub>1"
  shows "f ` U\<^sub>M\<^sub>_\<^sub>1 = U\<^sub>M\<^sub>_\<^sub>2"
    is finite_dimensional_vector_space_pair.linear_injective_imp_surjective.

tts_lemma linear_injective_isomorphism:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "inj_on f U\<^sub>M\<^sub>_\<^sub>1"
    and "VS\<^sub>2.dim U\<^sub>M\<^sub>_\<^sub>2 = VS\<^sub>1.dim U\<^sub>M\<^sub>_\<^sub>1"
  shows 
    "\<exists>x. 
      (\<forall>a\<in>U\<^sub>M\<^sub>_\<^sub>2. x a \<in> U\<^sub>M\<^sub>_\<^sub>1) \<and> 
      linear_on U\<^sub>M\<^sub>_\<^sub>2 U\<^sub>M\<^sub>_\<^sub>1 (*s\<^sub>2) (*s\<^sub>1) x \<and> 
      (\<forall>a\<in>U\<^sub>M\<^sub>_\<^sub>1. x (f a) = a) \<and> 
      (\<forall>a\<in>U\<^sub>M\<^sub>_\<^sub>2. f (x a) = a)"
    given finite_dimensional_vector_space_pair.linear_injective_isomorphism
  by auto

tts_lemma linear_surjective_isomorphism:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "f ` U\<^sub>M\<^sub>_\<^sub>1 = U\<^sub>M\<^sub>_\<^sub>2"
    and "VS\<^sub>2.dim U\<^sub>M\<^sub>_\<^sub>2 = VS\<^sub>1.dim U\<^sub>M\<^sub>_\<^sub>1"
  shows 
    "\<exists>x.
      (\<forall>a\<in>U\<^sub>M\<^sub>_\<^sub>2. x a \<in> U\<^sub>M\<^sub>_\<^sub>1) \<and> 
      linear_on U\<^sub>M\<^sub>_\<^sub>2 U\<^sub>M\<^sub>_\<^sub>1 (*s\<^sub>2) (*s\<^sub>1) x \<and> 
      (\<forall>a\<in>U\<^sub>M\<^sub>_\<^sub>1. x (f a) = a) \<and> 
      (\<forall>a\<in>U\<^sub>M\<^sub>_\<^sub>2. f (x a) = a)"
    given finite_dimensional_vector_space_pair.linear_surjective_isomorphism
  by auto

tts_lemma basis_to_basis_subspace_isomorphism:
  assumes "S \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "T \<subseteq> U\<^sub>M\<^sub>_\<^sub>2"
    and "B \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "C \<subseteq> U\<^sub>M\<^sub>_\<^sub>2"
    and "VS\<^sub>1.subspace S"
    and "VS\<^sub>2.subspace T"
    and "VS\<^sub>1.dim S = VS\<^sub>2.dim T"
    and "B \<subseteq> S"
    and "\<not> VS\<^sub>1.dependent B"
    and "S \<subseteq> VS\<^sub>1.span B"
    and "card B = VS\<^sub>1.dim S"
    and "C \<subseteq> T"
    and "\<not> VS\<^sub>2.dependent C"
    and "T \<subseteq> VS\<^sub>2.span C"
    and "card C = VS\<^sub>2.dim T"
  shows
    "\<exists>x.
      (\<forall>a\<in>U\<^sub>M\<^sub>_\<^sub>1. x a \<in> U\<^sub>M\<^sub>_\<^sub>2) \<and>
      linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) x \<and>
      x ` B = C \<and>
      inj_on x S \<and>
      x ` S = T"
  given finite_dimensional_vector_space_pair.basis_to_basis_subspace_isomorphism
  by auto

tts_lemma subspace_isomorphism:
  assumes "S \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "T \<subseteq> U\<^sub>M\<^sub>_\<^sub>2"
    and "VS\<^sub>1.subspace S"
    and "VS\<^sub>2.subspace T"
    and "VS\<^sub>1.dim S = VS\<^sub>2.dim T"
  shows "\<exists>x.
    (\<forall>a\<in>U\<^sub>M\<^sub>_\<^sub>1. x a \<in> U\<^sub>M\<^sub>_\<^sub>2) \<and>
    (inj_on x S \<and> x ` S = T) \<and>
    linear_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) x"
    given finite_dimensional_vector_space_pair.subspace_isomorphism by auto

end

end

text\<open>\newpage\<close>

end