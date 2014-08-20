(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: maxset.thy                                                           *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Maximum over Sets of Naturals *}

theory maxset
imports Main
begin

definition MaxSet :: "nat set \<Rightarrow> nat" where
"MaxSet s = (if s = {} then 0 else Max s)"

subsection {* Theorems *}

theorem subset_singleton:
"A \<subseteq> {x} \<longleftrightarrow> A = {} \<or> A = {x}"
apply (auto)
done

theorem MaxSet_non_empty [simp] :
"s \<noteq> {} \<Longrightarrow> MaxSet s = Max s"
apply (simp add: MaxSet_def)
done

theorem MaxSet_empty [simp] :
"MaxSet {} = 0"
apply (simp add: MaxSet_def)
done

theorem MaxSet_insert [simp] :
"finite s \<Longrightarrow> MaxSet (insert x s) = max x (MaxSet s)"
apply (simp add: MaxSet_def)
done

theorem MaxSet_member [dest] :
"x \<in> s \<Longrightarrow> finite s \<Longrightarrow> MaxSet s = max x (MaxSet (s - {x}))"
apply (simp add: MaxSet_def)
apply (simp add: subset_singleton)
apply (safe)
apply (rename_tac a b)
apply (metis Max.insert_remove insert_Diff_single insert_absorb singleton_iff)
done

theorem MaxSet_union :
"finite s \<Longrightarrow> finite t \<Longrightarrow> MaxSet (s \<union> t) = max (MaxSet s) (MaxSet t)"
apply (simp add: MaxSet_def)
apply (simp add: Max.union)
done

find_theorems name:"finite" name:"induct"

theorem MaxSet_leq [simp] :
"finite s \<Longrightarrow> MaxSet s \<le> n \<longleftrightarrow> (\<forall> x \<in> s . x \<le> n)"
apply (erule finite.induct)
apply (simp_all)
done
end
