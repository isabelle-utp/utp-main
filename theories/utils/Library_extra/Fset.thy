theory Fset
imports Main 
  "~~/src/HOL/Library/List_lexord" 
  "~~/src/HOL/Library/Countable"
  List_extra
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

lift_definition fempty :: "'a fset" ("\<lbrace>\<rbrace>") is "{}"
  by (simp add:fsets_def)

declare fempty.rep_eq [simp]

lift_definition fmember :: "'a \<Rightarrow> 'a fset \<Rightarrow> bool" is "op \<in>" ..
lift_definition fnmember :: "'a \<Rightarrow> 'a fset \<Rightarrow> bool" is "op \<notin>" ..

declare fmember.rep_eq [simp]
declare fnmember.rep_eq [simp]

notation (xsymbols)
  fmember      ("op \<in>\<^sub>f") and
  fmember      ("(_/ \<in>\<^sub>f _)" [50, 51] 50) and
  fnmember      ("op \<notin>\<^sub>f") and
  fnmember      ("(_/ \<notin>\<^sub>f _)" [50, 51] 50)

definition fcard :: "'a fset \<Rightarrow> nat" where 
"fcard xs = card \<langle>xs\<rangle>\<^sub>f" 

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

instantiation fset :: (type) ord
begin

lift_definition less_eq_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" is "subset_eq"
  by (simp add:fsets_def)

lift_definition less_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" is "subset"
  by (simp add:fsets_def)

instance ..

end

abbreviation fsubset_eq :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" where
"fsubset_eq \<equiv> op \<le>"

abbreviation fsubset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" where
"fsubset \<equiv> op <"

(*
lift_definition fsubset_eq :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" is "subset_eq"
  by (simp add:fsets_def)
*)

declare less_eq_fset.rep_eq [simp]
declare less_fset.rep_eq [simp]

notation
  fsubset_eq ("op \<subseteq>\<^sub>f") and
  fsubset_eq ("(_/ \<subseteq>\<^sub>f _)" [50, 51] 50) and
  fsubset ("op \<subset>\<^sub>f") and
  fsubset ("(_/ \<subset>\<^sub>f _)" [50, 51] 50)

syntax
  "_FinFset" :: "args => 'a fset"    ("\<lbrace>(_)\<rbrace>")

translations
  "\<lbrace>x, xs\<rbrace>" == "CONST finsert x \<lbrace>xs\<rbrace>"
  "\<lbrace>x\<rbrace>" == "CONST finsert x \<lbrace>\<rbrace>"

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
  "flist \<lbrace>\<rbrace> = []"
  by (simp add:flist_def)

definition fset :: "'a list \<Rightarrow> 'a fset" where
"fset xs = Abs_fset (set xs)"

lemma fset_rep_eq [simp]: "\<langle>fset xs\<rangle>\<^sub>f = set xs"
  by (simp add:fset_def)

lemma flist_inv [simp]: "fset (flist xs) = xs"
  by (simp add:fset_def flist_def Rep_fset_inverse)

lemma flist_set [simp]: "set (flist xs) = \<langle>xs\<rangle>\<^sub>f"
  by (simp add:fset_def flist_def Rep_fset_inverse)

lemma fset_inv [simp]: "\<lbrakk> sorted xs; distinct xs \<rbrakk> \<Longrightarrow> flist (fset xs) = xs"
  apply (simp add:fset_def flist_def Rep_fset_inverse)
  apply (metis finite_set sorted_distinct_set_unique sorted_list_of_set)
done

lemma fset_empty [simp]: "fset [] = \<lbrace>\<rbrace>"
  by (simp add:fset_def fempty_def)

lemma fset_cons [simp]: "fset (x # xs) = finsert x (fset xs)"
  by (simp add:fset_def finsert_def)

lemma fcard_flist:
  "fcard xs = length (flist xs)"
  apply (simp add:fcard_def)
  apply (fold flist_set)
  apply (unfold distinct_card[OF flist_props(2)])
  apply (rule refl)
done

definition fmax :: "'a fset \<Rightarrow> 'a" where
"fmax xs = (if (xs = \<lbrace>\<rbrace>) then undefined else last (flist xs))"

end

lemma fmax_greatest [simp]:
  fixes x :: "'a::linorder"
  assumes "x \<in>\<^sub>f xs"
  shows "x \<le> fmax xs"
proof -
  obtain xs' where "xs = fset xs'" "sorted xs'" "distinct xs'"
    by (metis flist_inv flist_props)

  with assms show ?thesis
    apply (unfold fmax_def)
    apply (case_tac "xs = \<lbrace>\<rbrace>")
    apply (auto)
  done
qed

instantiation fset :: ("{linorder,countable}") countable
begin

instance
  apply (intro_classes)
  apply (rule_tac x="to_nat \<circ> flist" in exI)
  apply (metis flist_inj inj_comp inj_to_nat)
done
end

(*
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
*)

instantiation fset :: (linorder) order
begin

instance by (intro_classes, auto)
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

(*
instantiation fset :: (type) discrete_cpo
begin

definition below_fset_def:
  "(x::'a fset) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_fset_def)

end

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

(* Induction rule for fset *)  
lemma fset_induct [case_names fempty finsert, induct type]:
  -- {* Discharging @{text "x \<notin> F"} entails extra work. *}
  assumes "P \<lbrace>\<rbrace>"
    and finsert: "\<And>x F. x \<notin>\<^sub>f F \<Longrightarrow> P F \<Longrightarrow> P (finsert x F)"
  shows "P F"
  apply (case_tac F, simp add:fsets_def)
  apply (erule finite_induct)
  apply (metis assms(1) fempty_def)
  apply (auto)
  apply (metis Rep_fset_inv Rep_fset_inverse finsert finsert.rep_eq fnmember.rep_eq)
done

lemma fimage_fempty [simp]:
  "f `\<^sub>f \<lbrace>\<rbrace> = \<lbrace>\<rbrace>"
  by (auto)

lemma fimage_finsert [simp]:
  "f `\<^sub>f finsert x xs = finsert (f x) (f `\<^sub>f xs)"
  by (auto)

lemma fimage_funion [simp]: "f `\<^sub>f (A \<union>\<^sub>f B) = (f `\<^sub>f A) \<union>\<^sub>f (f `\<^sub>f B)"
  by (auto)

lemma fimage_set_diff [simp]: "inj f ==> f `\<^sub>f (A -\<^sub>f B) = f `\<^sub>f A -\<^sub>f f `\<^sub>f B"
  by (clarsimp, simp add:image_set_diff)

lemma funion_assoc [simp]: "(A \<union>\<^sub>f B) \<union>\<^sub>f C =  A \<union>\<^sub>f (B \<union>\<^sub>f C)"
  by (auto)

lemma funion_finsert_left [simp]:
  "finsert a B \<union>\<^sub>f C = finsert a (B \<union>\<^sub>f C)"
  by auto

lemma funion_finsert_right [simp]: 
  "A \<union>\<^sub>f (finsert a B) = finsert a (A \<union>\<^sub>f B)"
  by (auto)

lemma finsert_idem [simp]:
  "finsert x (finsert x xs) = finsert x xs"
  by (auto)

lemma fset_simps [simp]:
  "x \<union>\<^sub>f \<lbrace>\<rbrace> = x"
  "\<lbrace>\<rbrace> \<union>\<^sub>f x = x"
  "x \<inter>\<^sub>f \<lbrace>\<rbrace> = \<lbrace>\<rbrace>"
  "\<lbrace>\<rbrace> \<inter>\<^sub>f x = \<lbrace>\<rbrace>"
  "x \<union>\<^sub>f x = x"
  "x \<inter>\<^sub>f x = x"
  "xs -\<^sub>f xs = \<lbrace>\<rbrace>"
  "xs -\<^sub>f \<lbrace>\<rbrace> = xs"
  "\<lbrace>\<rbrace> -\<^sub>f xs = \<lbrace>\<rbrace>"
  by (auto)

lemma flist_finsert [simp]:
  "\<forall>x'. x'\<in>\<^sub>fA \<longrightarrow> x < x' \<Longrightarrow> flist (finsert x A) = x # flist A"
  apply (subgoal_tac "x \<notin>\<^sub>f A")
  apply (auto)
  apply (induct A)
  apply (simp_all add:flist_def)
  apply (drule_tac x="xa" in spec)
  apply (smt insort_key.simps insort_left_comm linorder_not_less)
done

lemma flist_fimage:
  assumes "strict_mono f"
  shows "flist (f `\<^sub>f A) = map f (flist A)"
proof -
  obtain xs where Alist: "A = fset xs" and sorted:"sorted xs" and distinct:"distinct xs"
    by (metis flist_inv flist_props)

  from sorted distinct have "flist (f `\<^sub>f fset xs) = map f xs"
  proof (induct xs)
    case Nil thus ?case by simp
  next
    case (Cons xs x)
    with assms show ?case
      apply (clarsimp)
      apply (subgoal_tac "\<forall>x'. x'\<in>\<^sub>ffset xs \<longrightarrow> x < x'")
      apply (subgoal_tac "\<forall>x'. x'\<in>\<^sub>f(f `\<^sub>f fset xs) \<longrightarrow> f x < x'")
      apply (simp add: sorted_Cons)
      apply (simp add: strict_mono_def)
      apply (auto)
      apply (metis order_le_neq_trans)
    done
  qed

  with Alist sorted distinct show ?thesis by (simp)

qed

subsection {* Finite set binders *}

abbreviation Fall :: "'a fset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "Fall t P \<equiv> (\<forall>x. x \<in>\<^sub>f t \<longrightarrow> P x)"

abbreviation Fex :: "'a fset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "Fex t P \<equiv> (\<exists>x. x \<in>\<^sub>f t \<and> P x)"

syntax
  "_Fall" :: "pttrn => 'a fset => bool => bool" ("(3\<forall> _\<in>\<^sub>f_./ _)" [0, 0, 10] 10)
  "_Fex"  :: "pttrn => 'a fset => bool => bool" ("(3\<exists> _\<in>\<^sub>f_./ _)" [0, 0, 10] 10)
  
translations
  "\<forall> x\<in>\<^sub>fA. P" == "CONST Fall A (%x. P)"
  "\<exists> x\<in>\<^sub>fA. P" == "CONST Fex A (%x. P)"

(* A version of fset induction which uses the linear order *)
lemma fset_induct_sorted [case_names fempty finsert, induct type]:
  -- {* Discharging @{text "x \<notin> F"} entails extra work. *}
  fixes F :: "'a::linorder fset"
  assumes fempty:"P \<lbrace>\<rbrace>"
    and finsert: "\<And>x F. \<forall>y\<in>\<^sub>fF. x < y \<Longrightarrow> P F \<Longrightarrow> P (finsert x F)"
  shows "P F"
proof -

  obtain xs where xs_def: "F = fset xs" and xs_props: "sorted xs" "distinct xs"
    by (metis flist_inv flist_props(1) flist_props(2))

  from xs_props have "P (fset xs)"
  proof (induct xs)
    case Nil thus ?case 
      by (simp add:fempty)
  next
    case (Cons ys y) thus ?case
      by (metis distinct.simps(2) finsert fmember.rep_eq fset_cons fset_rep_eq order_le_neq_trans)

  qed

  thus ?thesis by (simp add:xs_def)
qed

end

