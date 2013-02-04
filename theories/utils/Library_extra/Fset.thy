theory Fset
imports HOLCF "~~/src/HOL/Library/List_lexord" "~~/src/HOL/Library/Countable"
begin

default_sort type

definition fsets :: "'a set set" 
where "fsets = Collect finite"

typedef (open) 'a fset = "fsets :: 'a set set"
  by (auto simp add:fsets_def)

notation Rep_fset ("\<langle>_\<rangle>\<^sub>f")

declare Rep_fset [simp]
declare Rep_fset_inverse [simp]
declare Abs_fset_inverse [simp]

lemma Rep_fset_intro [intro!]:
  "Rep_fset x = Rep_fset y \<Longrightarrow> x = y"
  by (simp add:Rep_fset_inject)

lemma Rep_fset_elim [elim]:
  "\<lbrakk> x = y; Rep_fset x = Rep_fset y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

lemma Rep_fset_finite[simp]:
  "finite \<langle>xs\<rangle>\<^sub>f"
  apply (subgoal_tac "Rep_fset xs \<in> Collect finite")
  apply (simp)
  apply (metis Rep_fset fsets_def)
done

lemma Rep_fset_inv [simp]: "finite xs \<Longrightarrow> Rep_fset (Abs_fset xs) = xs"
  apply (subgoal_tac "xs \<in> fsets")
  apply (simp add: Abs_fset_inverse)
  apply (simp add: fsets_def)
done

setup_lifting type_definition_fset

lift_definition fempty :: "'a fset" ("{}\<^sub>f") is "{}"
  by (simp add:fsets_def)

declare fempty.rep_eq [simp]

lift_definition fmember :: "'a \<Rightarrow> 'a fset \<Rightarrow> bool" is "op \<in>" ..

declare fmember.rep_eq [simp]

notation (xsymbols)
  fmember      ("op \<in>\<^sub>f") and
  fmember      ("(_/ \<in>\<^sub>f _)" [50, 51] 50)

lift_definition funion :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" (infixl "\<union>\<^sub>f" 65) is "op \<union>"
  by (simp add:fsets_def)

declare funion.rep_eq [simp]

lift_definition finter :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" (infixl "\<inter>\<^sub>f" 65) is "op \<inter>"
  by (simp add:fsets_def)

declare finter.rep_eq [simp]

lift_definition fminus :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" (infixl "-\<^sub>f" 65) is "op -"
  by (simp add:fsets_def)

declare fminus.rep_eq [simp]

lift_definition fimage :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> 'b fset" (infixr "`\<^sub>f" 90) is "image"
  by (simp add:fsets_def)

declare fimage.rep_eq [simp]

lift_definition finsert :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset" is "insert"
  by (simp add:fsets_def)

declare finsert.rep_eq [simp]

lift_definition fsubset_eq :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" is "subset_eq"
  by (simp add:fsets_def)

declare fsubset_eq.rep_eq [simp]

notation
  fsubset_eq  ("op \<subseteq>\<^sub>f") and
  fsubset_eq  ("(_/ \<subseteq>\<^sub>f _)" [50, 51] 50)

definition fset_elem :: "('a * 'a fset) set" 
where "fset_elem = {(x,xs) | x xs. x \<notin> Rep_fset xs}"

typedef (open) 'a fset_elem = "fset_elem :: ('a * 'a fset) set"
  apply (auto simp add:fset_elem_def)
  apply (rule_tac x="undefined" in exI)
  apply (rule_tac x="fempty" in exI)
  apply (simp add:fempty_def Abs_fset_inverse fsets_def)
done

definition fs_elem :: "'a fset_elem \<Rightarrow> 'a" where
"fs_elem x = fst (Rep_fset_elem x)"

definition fs_set :: "'a fset_elem \<Rightarrow> 'a set" where
"fs_set x = Rep_fset (snd (Rep_fset_elem x))"

lemma fs_elem_set [simp]: "fs_elem fx \<notin> fs_set fx"
  apply (simp add:fs_elem_def fs_set_def)
  apply (case_tac fx)
  apply (auto simp add:fset_elem_def Abs_fset_elem_inverse)
done 
  
context linorder
begin

lemma sorted_list_of_set_inj:
  "\<lbrakk> finite xs; finite ys; sorted_list_of_set xs = sorted_list_of_set ys \<rbrakk>
   \<Longrightarrow> xs = ys"
  apply (simp add:sorted_list_of_set_def)
  apply (induct xs rule:finite_induct)
  apply (induct ys rule:finite_induct)
  apply (simp_all)
  apply (metis insort_not_Nil sorted_list_of_set_def sorted_list_of_set_insert)
  apply (metis finite.insertI sorted_list_of_set sorted_list_of_set_def)
done

definition flist :: "'a fset \<Rightarrow> 'a list" where
"flist xs = sorted_list_of_set (Rep_fset xs)"

lemma flist_inj: "inj flist"
  apply (simp add:flist_def inj_on_def)
  apply (clarify)
  apply (subgoal_tac "Rep_fset x = Rep_fset y")
  apply (simp add:Rep_fset_inject)
  apply (rule sorted_list_of_set_inj, simp_all)
done

lemma flist_props [simp]:
  "sorted (flist xs)"
  "distinct (flist xs)"
  by (simp_all add:flist_def)

lemma flist_empty [simp]:
  "flist {}\<^sub>f = []"
  by (simp add:flist_def)

definition fset :: "'a list \<Rightarrow> 'a fset" where
"fset xs = Abs_fset (set xs)"

lemma flist_inv [simp]: "fset (flist xs) = xs"
  by (simp add:fset_def flist_def Rep_fset_inverse)

lemma fset_empty [simp]: "fset [] = {}\<^sub>f"
  by (simp add:fset_def fempty_def)

end

instantiation fset :: ("{linorder,countable}") countable
begin

instance
  apply (intro_classes)
  apply (rule_tac x="to_nat \<circ> flist" in exI)
  apply (metis flist_inj inj_comp inj_to_nat)
done
end

instantiation fset :: (linorder) linorder
begin

definition "less_eq_fset x y \<equiv> flist x \<le> flist y"
definition "less_fset x y \<equiv> flist x < flist y"

instance
  apply (intro_classes)
  apply (simp_all add: less_fset_def less_eq_fset_def)
  apply (metis linorder_not_less list_le_def)
  apply (blast dest:injD[OF flist_inj])
  apply (metis linorder_linear)
done
end

instantiation fset :: ("{equal,linorder}") equal
begin

definition 
  equal_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" where
  "equal_fset xs ys = equal_class.equal (flist xs) (flist ys)"

instance
  apply (intro_classes)
  apply (unfold equal_fset_def)
  apply (metis (lifting) equal_eq flist_inj injD)
done
end

instantiation fset :: (type) discrete_cpo
begin

definition below_fset_def:
  "(x::'a fset) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_fset_def)

end


(*
lemma fsetE: 
  assumes "s = fempty \<Longrightarrow> P"
    and "\<And>(x::'a) xs. s = finsert x xs \<Longrightarrow> P"
  shows P
proof (rule Abs_fset_cases [of s])
  fix f 
  assume "s = Abs_fset f" and "f \<in> fset"
  with assms show P
    apply (auto simp add: fset_def fempty_def finsert_def)
    apply (metis Abs_fset_inverse `(f\<Colon>'a set) \<in> fset` equals0I insert_absorb)
  done
qed
*)
  
end