section \<open> Injection Universes \<close>

theory InjUniv
  imports 
    "HOL-Library.Countable"
    "Optics.Lenses" 
begin

record ('a, 'u) inj_univ =
  to_univ :: "'a \<Rightarrow> 'u" ("to-univ\<index>")

locale inj_univ = 
  fixes I :: "('a, 'u) inj_univ" (structure)
  assumes inj_to_univ: "inj to-univ"
begin
  
definition from_univ :: "'u \<Rightarrow> 'a" ("from-univ") where
"from_univ = inv to-univ"
  
lemma to_univ_inv [simp]: "from-univ (to-univ x) = x"
  by (simp add: from_univ_def inv_f_f inj_to_univ)

definition to_univ_lens :: "'a \<Longrightarrow> 'u" ("to-univ\<^sub>L") where
"to_univ_lens = \<lparr> lens_get = from-univ, lens_put = (\<lambda> s v. to-univ v) \<rparr>"
  
lemma mwb_to_univ_lens [simp]:
  "mwb_lens to_univ_lens"
  by (unfold_locales, simp_all add: to_univ_lens_def)

end
  
definition nat_inj_univ :: "('a::countable, nat) inj_univ" ("\<U>\<^sub>\<nat>") where
"nat_inj_univ = \<lparr> to_univ = to_nat \<rparr>"

lemma nat_inj_univ: "inj_univ nat_inj_univ"
  by (unfold_locales, simp add: nat_inj_univ_def)
  
end