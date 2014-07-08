header {* Example for locale-code *}
theory Locale_Code_Ex
imports Locale_Code "~~/src/HOL/Library/Code_Target_Nat"
begin

definition [simp, code del]: "NOCODE \<equiv> id"

locale test = 
  fixes a b :: nat
  assumes "a=b"
begin
  text {* Mutually recursive functions *}
  fun g and f where
    "g 0 = NOCODE a"
  | "g (Suc n) = a + n + f n"
  | "f 0 = a+b"
  | "f (Suc n) = a + f n + b * f n + g n"

  text {* Various definitions, depending on more or less parameters *}
  definition "k x \<equiv> b + x :: nat"
  definition "j x y \<equiv> NOCODE x + y + f x :: nat"
  definition "i x y \<equiv> x + y :: nat"
  definition "h x y \<equiv> a+x+k y+i x y+j x y"

  lemmas "defs" = k_def j_def i_def h_def g.simps f.simps 

  lemma j_alt: "j x y \<equiv> f x + y + x" unfolding j_def by (simp add: add_ac)

  lemma g_alt:
    "g 0 = a"
    "g (Suc n) = f n + n + a"
    by (auto simp: add_ac)


  definition "c \<equiv> a + b"

  local_setup {* Locale_Code.lc_decl_eq @{thms j_alt} *}
  local_setup {* Locale_Code.lc_decl_eq @{thms g_alt} *}

end

text {* Conflicting constant name *}
definition "h_zero_zero \<equiv> True"

setup Locale_Code.open_block
  text {* Various interpretations, with and without constructor patterns 
    and free variables *}
  interpretation i0: test 0 0 apply unfold_locales by auto
  interpretation i1: test "Suc n" "Suc n" apply unfold_locales by auto
  interpretation i2: test 1 1 apply unfold_locales by auto
  interpretation i3: test 5 5 apply unfold_locales by auto
  interpretation i4: test "snd (x,3)" "1+2" apply unfold_locales by auto

  interpretation i5: test "i3.c" "i3.c" by unfold_locales simp

  text {* Setup some alternative equations *}
  lemma i0_f_pat: 
    "i0.f 0 = 0"
    "i0.f (Suc n) = i0.f n + i0.g n"
    by simp_all

  lemma i0_h_pat: "i0.h x y = x+i0.k y+i0.i x y+i0.j x y" 
    unfolding i0.h_def by auto

  declare [[ lc_add "i0.f" i0_f_pat and "i0.h" i0_h_pat]]
setup Locale_Code.close_block

definition "foo x y \<equiv> i0.h x y + i1.h x x y + i2.h x y + i3.h x y 
  + i4.h TYPE(bool) h_zero_zero x y + i5.h x y"

definition "bar x y \<equiv> i0.f x + i1.f x y + i2.f x + i3.f y 
  + i4.f TYPE(bool) False x + i5.f y"

code_thms foo
code_thms bar

text {* value *}
value "foo 3 4"
value "bar 3 4"

text {* eval-tactic *}
lemma "foo 3 4 = 34578" by eval
lemma "bar 3 4 = 354189" by eval

text {* Exported code *}
export_code foo bar in SML file -
export_code foo bar in OCaml file -
export_code foo bar in Haskell file -
export_code foo bar in Scala file -

text {* Inlined code *}
ML_val {*
  @{code foo} (@{code nat_of_integer} 3) (@{code nat_of_integer} 4);
  @{code bar} (@{code nat_of_integer} 3) (@{code nat_of_integer} 4);
*}

end
