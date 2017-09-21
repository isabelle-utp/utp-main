theory Set_extra
  imports Main
begin

lemma uminus_inter_insert [simp]: 
  "(- A) \<inter> (- insert x B) = (- insert x A) \<inter> (- B)"
  by (auto)

end