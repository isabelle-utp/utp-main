(*
  Author: Fred Kurz
*)
theory CNF_Supplement
  imports "Propositional_Proof_Systems.CNF_Formulas_Sema"
begin

(* TODO fix warnings *)

fun is_literal_formula 
  where "is_literal_formula (Atom _) = True"
  | "is_literal_formula (\<^bold>\<not>(Atom _)) = True" 
  | "is_literal_formula _ = False" 

fun literal_formula_to_literal :: "'a formula \<Rightarrow> 'a literal"
  where "literal_formula_to_literal (Atom a) = a\<^sup>+"
  | "literal_formula_to_literal (\<^bold>\<not>(Atom a)) = a\<inverse>" 

lemma is_literal_formula_then_cnf_is_singleton_clause:
  assumes "is_literal_formula f"
  obtains C where "cnf f = { C }" 
proof -
  consider (f_is_positive_literal) "\<exists>a. f = Atom a" 
    | (f_is_negative_literal) "\<exists>a. f = \<^bold>\<not>(Atom a)"
    using assms is_literal_formula.elims(2)[of f]
    by meson 
  then have "\<exists>C. cnf f = { C }"
    proof (cases)
      case f_is_positive_literal
      then obtain a where "f = Atom a" 
        by force
      then have "cnf f = {{ a\<^sup>+ }}"
        by force
      thus ?thesis
        by simp
    next
      case f_is_negative_literal
      then obtain a where "f = \<^bold>\<not>(Atom a)" 
        by force
      then have "cnf f = {{ a\<inverse> }}"
        by force
      thus ?thesis
        by simp
    qed
  thus ?thesis 
    using that
    by presburger 
qed

lemma literal_formula_to_literal_is_inverse_of_form_of_lit: 
  "literal_formula_to_literal (form_of_lit L) = L"
  by (cases L, simp+)

lemma is_nnf_cnf: 
  assumes "is_cnf F" 
    shows "is_nnf F" 
  using assms 
proof (induction F)
  case (Or F1 F2)
  have "is_disj (F1 \<^bold>\<or> F2)"
    using Or.prems is_cnf.simps(5)
    by simp
  thus ?case 
    using disj_is_nnf 
    by blast
qed simp+

lemma cnf_of_literal_formula:
  assumes "is_literal_formula f" 
  shows "cnf f = {{ literal_formula_to_literal f }}"
proof -
  consider (f_is_positive_literal) "\<exists>a. f = Atom a"
    | (f_is_negative_literal) "\<exists>a. f = (\<^bold>\<not>(Atom a))"
    using assms is_literal_formula.elims(2)[of f "\<exists>a. f = Atom a"]
       is_literal_formula.elims(2)[of f "\<exists>a. f = (\<^bold>\<not>(Atom a))"]
    by blast
  thus ?thesis 
    by(cases, force+)
qed

lemma is_cnf_foldr_and_if: 
  assumes "\<forall>f \<in> set fs. is_cnf f"
  shows "is_cnf (foldr (\<^bold>\<and>) fs (\<^bold>\<not>\<bottom>))" 
  using assms
proof (induction fs)
  case (Cons f fs)
  have "foldr (\<^bold>\<and>) (f # fs) (\<^bold>\<not>\<bottom>) = f \<^bold>\<and> (foldr (\<^bold>\<and>) fs (\<^bold>\<not>\<bottom>))" 
    by simp
  moreover {
    have "\<forall>f \<in> set fs. is_cnf f" 
      using Cons.prems
      by force
    hence "is_cnf (foldr (\<^bold>\<and>) fs (\<^bold>\<not>\<bottom>))" 
      using Cons.IH
      by blast
  }
  moreover have "is_cnf f" 
    using Cons.prems
    by simp
  ultimately show ?case
    by simp
qed simp

end