(******************************************************************************)
(* Project: Isabelle/UTP Toolkit                                              *)
(* File: Injection_Universe.thy                                               *)
(* Authors: Simon Foster and Frank Zeyda                                      *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)

section \<open> Injection Universes \<close>

theory Injection_Universe
  imports 
    "HOL-Library.Countable"
    "Optics.Lenses" 
begin

text \<open> An injection universe shows how one type @{typ "'a"} can be injected into another type,
  @{typ "'u"}. They are applied in UTP to provide local variables which require that we can
  injection a variety of different datatypes into a unified stack type. \<close>

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

text \<open> Lens-based view on universe injection and projection. \<close>

definition to_univ_lens :: "'a \<Longrightarrow> 'u" ("to-univ\<^sub>L") where
"to_univ_lens = \<lparr> lens_get = from-univ, lens_put = (\<lambda> s v. to-univ v) \<rparr>"
  
lemma mwb_to_univ_lens [simp]:
  "mwb_lens to_univ_lens"
  by (unfold_locales, simp_all add: to_univ_lens_def)

end

text \<open> Example universe based on natural numbers. Any countable type can be injected into it. \<close>

definition nat_inj_univ :: "('a::countable, nat) inj_univ" ("\<U>\<^sub>\<nat>") where
"nat_inj_univ = \<lparr> to_univ = to_nat \<rparr>"

lemma nat_inj_univ: "inj_univ nat_inj_univ"
  by (unfold_locales, simp add: nat_inj_univ_def)
  
end