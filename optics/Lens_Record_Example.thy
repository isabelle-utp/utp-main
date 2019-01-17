theory Lens_Record_Example
imports Lens_Instances
begin

text \<open>The alphabet command supports syntax illustrated in the following comments.\<close>

print_theorems

alphabet mylens =
  x :: nat
  y :: string

thm mylens.indeps
thm mylens.sublenses

term "Lens_Record_Example.mylens.x"

term "more\<^sub>L"

alphabet mylens2 = mylens +
  z :: nat

thm mylens2.pl_indeps
thm mylens2.sublenses

alphabet st = 
  k :: int



term z

thm z_def

term "mylens2.child_lens\<^sub>a ;\<^sub>L mylens.child_lens"

definition child_lens :: "_" where
"(child_lens :: _) = mylens2.child_lens\<^sub>a ;\<^sub>L mylens.child_lens"


thm "mylens.indeps"



setup {*

let fun mk_def ty = Const ("Pure.eq", ty --> ty --> Term.propT) in
Named_Target.theory_map (snd o Specification.definition NONE [] [] ((Binding.empty, []), mk_def @{typ nat} $ Free ("mynum", @{typ nat}) $ @{term "1::nat"})) o Sign.qualified_path false (Binding.name "mylens")
end
*}

term "mylens.mynum"


ML {*
Named_Target.theory_map;




Proof_Context.init_global @{theory};



val ctxt = Proof_Context.init_global @{theory};



@{theory} |> Sign.qualified_path false (Binding.name "mylens")

*}


lemma mylens_bij_lens:
  "bij_lens (x +\<^sub>L y +\<^sub>L mylens_child_lens)"
  by (unfold_locales, simp_all add: lens_plus_def x_def y_def mylens_child_lens_def id_lens_def sublens_def lens_comp_def prod.case_eq_if)

alphabet mylens_2 = mylens +
  z :: int
  k :: "string list"

alphabet mylens_3 = mylens_2 +
  n :: real
  h :: nat

end
