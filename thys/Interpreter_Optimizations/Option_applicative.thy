theory Option_applicative
  imports Main
begin

context begin

local_setup \<open>
  Local_Theory.map_background_naming (Name_Space.add_path "Option")
\<close>

fun pure where
  "pure x = Some x"

fun ap :: "('a \<Rightarrow> 'b) option \<Rightarrow> 'a option \<Rightarrow> 'b option" (infixl "<*>" 51) where
  "Some f <*> Some x = Some (f x)" |
  "_ <*> _ = None"

end

lemma identity: "pure id <*> x = x"
  by (cases x) simp_all

lemma homomorphism: "pure f <*> pure x = pure (f x)"
  by simp

lemma interchange: "f <*> pure x = pure (\<lambda>g. g x) <*> f"
  by (cases f) simp_all

lemma composition: "pure (\<circ>) <*> u <*> v <*> w = u <*> (v <*> w)"
  apply (cases u, simp)
  apply (cases v, simp)
  apply (cases w, simp)
  by simp

end