(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: Fset.thy                                                             *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Finite set type *}

theory Fset
imports Main 
  "../../../contrib/HOL-Algebra2/Complete_Lattice"
  List_lexord
  Countable
  List_extra
(*  Lattice_extra *)
begin

default_sort type

definition fsets :: "'a set set" 
where "fsets = Collect finite"

typedef 'a fset = "fsets :: 'a set set"
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

definition FUnion :: "'a fset fset \<Rightarrow> 'a fset" ("\<Union>\<^sub>f_" [90] 90) where
"FUnion xs = Abs_fset (\<Union>x\<in>\<langle>xs\<rangle>\<^sub>f. \<langle>x\<rangle>\<^sub>f)"

definition FInter :: "'a fset fset \<Rightarrow> 'a fset" ("\<Inter>\<^sub>f_" [90] 90) where
"FInter xs = Abs_fset (\<Inter>x\<in>\<langle>xs\<rangle>\<^sub>f. \<langle>x\<rangle>\<^sub>f)"

text {* Finite power set *}

definition FinPow :: "'a fset \<Rightarrow> 'a fset fset" where
"FinPow xs = Abs_fset (Abs_fset ` Pow \<langle>xs\<rangle>\<^sub>f)"

text {* Set of all finite subsets of a set *}

definition Fow :: "'a set \<Rightarrow> 'a fset set" where
"Fow A = {x. \<langle>x\<rangle>\<^sub>f \<subseteq> A}"

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

text {* Finite least upper bound with respect to a top element *}

definition flub :: "'a fset set \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
"flub A t = (if (\<forall> a\<in>A. a \<subseteq>\<^sub>f t) then Abs_fset (\<Union>x\<in>A. \<langle>x\<rangle>\<^sub>f) else t)"

lemma finite_Union_subsets:
  "\<lbrakk> \<forall> a \<in> A. a \<subseteq> b; finite b \<rbrakk> \<Longrightarrow> finite (\<Union>A)"
  by (metis Sup_le_iff finite_subset)

lemma finite_UN_subsets:
  "\<lbrakk> \<forall> a \<in> A. B a \<subseteq> b; finite b \<rbrakk> \<Longrightarrow> finite (\<Union>a\<in>A. B a)"
  by (metis UN_subset_iff finite_subset)

lemma flub_rep_eq:
  "\<langle>flub A t\<rangle>\<^sub>f = (if (\<forall> a\<in>A. a \<subseteq>\<^sub>f t) then (\<Union>x\<in>A. \<langle>x\<rangle>\<^sub>f) else \<langle>t\<rangle>\<^sub>f)"
  apply (subgoal_tac "(if (\<forall> a\<in>A. a \<subseteq>\<^sub>f t) then (\<Union>x\<in>A. \<langle>x\<rangle>\<^sub>f) else \<langle>t\<rangle>\<^sub>f) \<in> fsets")
  apply (auto simp add:flub_def)
  apply (auto simp add:fsets_def)
  apply (rule finite_UN_subsets[of _ _ "\<langle>t\<rangle>\<^sub>f"])
  apply (auto)
done

definition fglb :: "'a fset set \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
"fglb A t = (if (A = {}) then t else Abs_fset (\<Inter>x\<in>A. \<langle>x\<rangle>\<^sub>f))"

lemma fglb_rep_eq:
  "\<langle>fglb A t\<rangle>\<^sub>f = (if (A = {}) then \<langle>t\<rangle>\<^sub>f else (\<Inter>x\<in>A. \<langle>x\<rangle>\<^sub>f))"
  apply (subgoal_tac "(if (A = {}) then \<langle>t\<rangle>\<^sub>f else (\<Inter>x\<in>A. \<langle>x\<rangle>\<^sub>f)) \<in> fsets")
  apply (metis Abs_fset_inverse fglb_def)
  apply (auto simp add:fsets_def)
  apply (metis Rep_fset_finite finite_INT)
done

definition fset :: "'a list \<Rightarrow> 'a fset" where
"fset xs = Abs_fset (set xs)"

lemma fset_rep_eq [simp]: "\<langle>fset xs\<rangle>\<^sub>f = set xs"
  by (simp add:fset_def)

lemma fset_empty [simp]: "fset [] = \<lbrace>\<rbrace>"
  by (simp add:fset_def fempty_def)

lemma fset_cons [simp]: "fset (x # xs) = finsert x (fset xs)"
  by (simp add:fset_def finsert_def)

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

lemma flist_inv [simp]: "fset (flist xs) = xs"
  by (simp add:fset_def flist_def Rep_fset_inverse)

lemma flist_set [simp]: "set (flist xs) = \<langle>xs\<rangle>\<^sub>f"
  by (simp add:fset_def flist_def Rep_fset_inverse)

lemma fset_inv [simp]: "\<lbrakk> sorted xs; distinct xs \<rbrakk> \<Longrightarrow> flist (fset xs) = xs"
  apply (simp add:fset_def flist_def Rep_fset_inverse)
  apply (metis finite_set sorted_distinct_set_unique sorted_list_of_set)
done


lemma fcard_flist:
  "fcard xs = length (flist xs)"
  apply (simp add:fcard_def)
  apply (fold flist_set)
  apply (unfold distinct_card[OF flist_props(2)])
  apply (rule refl)
done

lemma fcard_empty [simp]:
  "fcard \<lbrace>\<rbrace> = 0"
  by (auto simp add:fcard_def)

lemma fcard_insert [simp]:
  "x \<notin>\<^sub>f xs \<Longrightarrow> fcard (finsert x xs) = Suc (fcard xs)"
  by (auto simp add:fcard_def)

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

lemma funion_comm: "A \<union>\<^sub>f B = B \<union>\<^sub>f A"
  by auto

lemma funion_assoc [simp]: "(A \<union>\<^sub>f B) \<union>\<^sub>f C =  A \<union>\<^sub>f (B \<union>\<^sub>f C)"
  by (auto)

lemma funion_finsert_left [simp]:
  "finsert a B \<union>\<^sub>f C = finsert a (B \<union>\<^sub>f C)"
  by auto

lemma funion_finsert_right [simp]: 
  "A \<union>\<^sub>f (finsert a B) = finsert a (A \<union>\<^sub>f B)"
  by (auto)

lemma finter_comm: "A \<inter>\<^sub>f B = B \<inter>\<^sub>f A"
  by auto

lemma finter_assoc: "(A \<inter>\<^sub>f B) \<inter>\<^sub>f C =  A \<inter>\<^sub>f (B \<inter>\<^sub>f C)"
  by (auto)

lemma finsert_idem [simp]:
  "finsert x (finsert x xs) = finsert x xs"
  by (auto)

lemma finsert_comm_ord [simp]:
  "x < y \<Longrightarrow> finsert y (finsert x xs) = finsert x (finsert y xs)"
  by (auto)

lemma fset_transfer_eq: "xs = ys \<longleftrightarrow> flist xs = flist ys"
  by (metis flist_inv)

lemma fset_transfer_neq: "xs \<noteq> ys \<longleftrightarrow> flist xs \<noteq> flist ys"
  by (metis flist_inv)


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

lemma finsert_member [simp]: 
  "x \<in>\<^sub>f xs \<Longrightarrow> finsert x xs = xs"
  by auto

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

lemma FinPow_rep_eq [simp]: 
  "Rep_fset (FinPow xs) = {ys. ys \<subseteq>\<^sub>f xs}"
  apply (subgoal_tac "finite (Abs_fset ` Pow \<langle>xs\<rangle>\<^sub>f)")
  apply (auto simp add:FinPow_def)
  apply (subgoal_tac "finite xa")
  apply (force)
  apply (metis Rep_fset_finite rev_finite_subset)
  apply (metis Pow_def Rep_fset_inverse image_iff mem_Collect_eq)
done

lemma FUnion_rep_eq [simp]: 
  "\<langle>\<Union>\<^sub>f xs\<rangle>\<^sub>f = (\<Union>x\<in>\<langle>xs\<rangle>\<^sub>f. \<langle>x\<rangle>\<^sub>f)"
  by (simp add:FUnion_def)


lemma FInter_rep_eq [simp]: 
  "xs \<noteq> \<lbrace>\<rbrace> \<Longrightarrow> \<langle>\<Inter>\<^sub>f xs\<rangle>\<^sub>f = (\<Inter>x\<in>\<langle>xs\<rangle>\<^sub>f. \<langle>x\<rangle>\<^sub>f)"
  apply (simp add:FInter_def)
  apply (subgoal_tac "finite (\<Inter>x\<in>\<langle>xs\<rangle>\<^sub>f. \<langle>x\<rangle>\<^sub>f)")
  apply (simp)
  apply (force)
done

lemma FUnion_empty [simp]:
  "\<Union>\<^sub>f \<lbrace>\<rbrace> = \<lbrace>\<rbrace>"
  by (auto)

lemma FinPow_member [simp]:
  "xs \<in>\<^sub>f FinPow xs"
  by (auto)

lemma FUnion_FinPow [simp]:
  "\<Union>\<^sub>f (FinPow x) = x"
  by (auto)

lemma Fow_mem [iff]: "x \<in> Fow A \<longleftrightarrow> \<langle>x\<rangle>\<^sub>f \<subseteq> A"
  by (auto simp add:Fow_def)

lemma Fow_UNIV [simp]: "Fow UNIV = UNIV"
  by (simp add:Fow_def)

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

definition fset_option :: "'a option fset \<Rightarrow> 'a fset option" where
"fset_option xs = (if (None \<in>\<^sub>f xs) then None else Some (the `\<^sub>f xs))"

lemma fset_option_empty: 
  "fset_option \<lbrace>\<rbrace> = Some \<lbrace>\<rbrace>"
  by (simp add:fset_option_def)

(*
fun interleave :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list fset" where
"interleave [] ys = \<lbrace>ys\<rbrace>" |
"interleave (x # xs) (y # ys) = (Cons x) `\<^sub>f (interleave xs (y # ys)) 
                              \<union>\<^sub>f (Cons y) `\<^sub>f (interleave (x # xs) ys)" |
"interleave xs [] = \<lbrace>xs\<rbrace>"

lemma interleave_right_nil [simp]:
  "interleave xs [] = \<lbrace>xs\<rbrace>"
  by (induct xs, auto)

lemma interleave_headE [elim!]:
  "\<lbrakk> z # zs \<in> \<langle>interleave xs ys\<rangle>\<^sub>f
   ; \<And> xs'. xs = z # xs' \<Longrightarrow> P
   ; \<And> ys'. ys = z # ys' \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (induct xs)
  apply (auto)
  apply (induct ys)
  apply (auto)
done

lemma interleave_member:
  "\<lbrakk> zs \<in>\<^sub>f interleave xs ys; z \<in> set zs \<rbrakk> \<Longrightarrow> z \<in> set xs \<or> z \<in> set ys"
  apply (induct xs)
  apply (auto)
  apply (induct ys)
  apply (auto)
oops


(* FIXME: What happens if no progress can be made? *)
fun intersync :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list fset" where
"intersync s (x # xs) (y # ys) 
  = (case (x = y , x \<in> s , y \<in> s) of
          (True  , True   , _      ) \<Rightarrow> Cons x `\<^sub>f intersync s xs ys |
          (True  , False  , _      ) \<Rightarrow> ((Cons x `\<^sub>f intersync s xs (y # ys))
                                         \<union>\<^sub>f (Cons y `\<^sub>f intersync s (x # xs) ys)) |
          (False , True   , True   ) \<Rightarrow> \<lbrace>[]\<rbrace> |
          (False , True   , False  ) \<Rightarrow> Cons y `\<^sub>f intersync s (x # xs) ys |
          (False , False  , True   ) \<Rightarrow> Cons x `\<^sub>f intersync s xs (y # ys) |
          (False , False  , False  ) \<Rightarrow> ((Cons x `\<^sub>f intersync s xs (y # ys))
                                         \<union>\<^sub>f (Cons y `\<^sub>f intersync s (x # xs) ys)))" |
"intersync s [] (y # ys) = 
   (if (y \<in> s) then \<lbrace>[]\<rbrace> else Cons y `\<^sub>f intersync s [] ys)" |
"intersync s (x # xs) [] = 
   (if (x \<in> s) then \<lbrace>[]\<rbrace> else Cons x `\<^sub>f intersync s xs [])" |
"intersync s [] [] = \<lbrace>[]\<rbrace>"

(* FIXME: We should be able to prove this property... *)
lemma intersync_empty_interleave:
  "intersync {} xs ys = interleave xs ys"
  apply (induct xs)
  apply (simp_all)
  apply (induct ys)
  apply (simp_all)
  apply (induct ys arbitrary: a xs)
  apply (simp_all)
  apply (case_tac "aa = a")
  apply (simp_all)
oops
*)

lift_definition FMax :: "('a::linorder) fset \<Rightarrow> 'a" is "Max"
  by (simp)

abbreviation fset_order :: "'a set \<Rightarrow> ('a fset) gorder" where
"fset_order A \<equiv> \<lparr> carrier = Fow A, eq = op =, le = op \<subseteq>\<^sub>f \<rparr>"

interpretation fset_order: partial_order "fset_order A"
  where "carrier (fset_order A) = Fow A "
    and "eq (fset_order A) = op ="
    and "le (fset_order A) = op \<subseteq>\<^sub>f"
  by (unfold_locales, auto)

lemma funion_lub:
  "\<lbrakk> x \<in> Fow A; y \<in> Fow A \<rbrakk> \<Longrightarrow>
     is_lub (fset_order A) (x \<union>\<^sub>f y) {x, y}"
  by (rule least_UpperI, auto simp add:Upper_def)

lemma finter_glb:
  "\<lbrakk> x \<in> Fow A; y \<in> Fow A \<rbrakk> \<Longrightarrow>
     is_glb (fset_order A) (x \<inter>\<^sub>f y) {x, y}"
  by (rule greatest_LowerI, auto simp add:Lower_def)

interpretation fset_lattice: lattice "fset_order A"
  where "carrier (fset_order A) = Fow A "
    and "eq (fset_order A) = op ="
    and "le (fset_order A) = op \<subseteq>\<^sub>f"
  apply (unfold_locales, simp_all)
  apply (rule_tac x="x \<union>\<^sub>f y" in exI, simp add:funion_lub)
  apply (rule_tac x="x \<inter>\<^sub>f y" in exI, simp add:finter_glb)
done
  
lemma flub_lub:
  "B \<subseteq> Fow \<langle>A\<rangle>\<^sub>f \<Longrightarrow> least (fset_order \<langle>A\<rangle>\<^sub>f) (flub B A) (Upper (fset_order \<langle>A\<rangle>\<^sub>f) B)"
  apply (rule least_UpperI, auto simp add:flub_rep_eq Upper_def)
  apply (metis set_rev_mp)
done

lemma fglb_glb:
  "B \<subseteq> Fow \<langle>A\<rangle>\<^sub>f \<Longrightarrow> greatest (fset_order \<langle>A\<rangle>\<^sub>f) (fglb B A) (Lower (fset_order \<langle>A\<rangle>\<^sub>f) B)"
  apply (rule greatest_LowerI, auto simp add:fglb_rep_eq Lower_def)
  apply (metis Fow_mem set_rev_mp)
done

text {* Every set of finite sets with a common finite parent forms a complete lattice *}

lemma fset_complat: "complete_lattice (fset_order \<langle>A\<rangle>\<^sub>f)"
  apply (unfold_locales, simp_all)
  apply (rule_tac x="flub Aa A" in exI, simp add:flub_lub)
  apply (rule_tac x="fglb Aa A" in exI, simp add:fglb_glb)
done

interpretation fset_complete_lattice: complete_lattice "fset_order \<langle>A\<rangle>\<^sub>f"
  where "carrier (fset_order \<langle>A\<rangle>\<^sub>f) = Fow \<langle>A\<rangle>\<^sub>f"
    and "eq (fset_order \<langle>A\<rangle>\<^sub>f) = op ="
    and "le (fset_order \<langle>A\<rangle>\<^sub>f) = op \<subseteq>\<^sub>f"
    and "\<top>\<^bsub>fset_order \<langle>A\<rangle>\<^sub>f\<^esub> = A"
    and  "\<bottom>\<^bsub>fset_order \<langle>A\<rangle>\<^sub>f\<^esub> = \<lbrace>\<rbrace>"
proof -
  interpret fcl: complete_lattice "fset_order \<langle>A\<rangle>\<^sub>f"
  where "carrier (fset_order \<langle>A\<rangle>\<^sub>f) = Fow \<langle>A\<rangle>\<^sub>f"
    and "eq (fset_order \<langle>A\<rangle>\<^sub>f) = op ="
    and "le (fset_order \<langle>A\<rangle>\<^sub>f) = op \<subseteq>\<^sub>f"
    by (metis fset_complat, simp_all)

  show "\<top>\<^bsub>fset_order \<langle>A\<rangle>\<^sub>f\<^esub> = A"
    by (metis Fow_mem fcl.top_weak_eq less_eq_fset.rep_eq order_refl)

  show "\<bottom>\<^bsub>fset_order \<langle>A\<rangle>\<^sub>f\<^esub> = \<lbrace>\<rbrace>"
    by (metis (mono_tags) Fow_mem empty_subsetI fempty.rep_eq fcl.bottom_weak_eq less_eq_fset.rep_eq)

qed (simp_all add: fset_complat)

lemma sup_flub:
  "B \<subseteq> Fow \<langle>A\<rangle>\<^sub>f \<Longrightarrow> sup (fset_order \<langle>A\<rangle>\<^sub>f) B = flub B A"
  by (metis flub_lub fset_complete_lattice.sup_lub fset_order.weak_least_unique)

lemma inf_fglb:
  "B \<subseteq> Fow \<langle>A\<rangle>\<^sub>f \<Longrightarrow> inf (fset_order \<langle>A\<rangle>\<^sub>f) B = fglb B A"
  by (metis fglb_glb fset_complete_lattice.inf_glb fset_order.weak_greatest_unique)

end

