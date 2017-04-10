theory LPF_Utilities
imports Main
begin
subsection {* Uncurrying *}

text {* Isabelle provides a currying operator but none for uncurrying. *}

definition uncurry :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<times> 'b \<Rightarrow> 'c)" where
"uncurry = (\<lambda> f p . f (fst p) (snd p))"

lemma uncurry_app [simp]:
"uncurry f (x, y) = f x y"
apply (simp add: uncurry_def)
done

theorem uncurry_inverse [simp]:
"curry (uncurry f) = f"
apply (fastforce)
done

theorem curry_inverse [simp]:
"uncurry (curry f) = f"
apply (metis case_prod_curry uncurry_inverse)
done
end