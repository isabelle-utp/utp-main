theory Library_extra
imports
  "../../contrib/HOL-Algebra2/Complete_Lattice"
  "../../contrib/HOL-Algebra2/Galois_Connection"
  "Library_extra/List_extra"
  "Library_extra/Fset"
  "Library_extra/Map_Extra"
  "Library_extra/Fmap"
  "Library_extra/Multi_Elem"
  "Library_extra/Lattices_extra"
(*  "Library_extra/Lattice_extra" *)
  "Library_extra/McCarthy_Logic"
begin

definition complete_inj ::
  "('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a)" where
"complete_inj f vs = (\<lambda> x. if (x \<in> vs) then f x else if (x \<in> f ` vs) then inv_into vs f x else x)"

lemma complete_inj_empty [simp]:
  "complete_inj f {} = id"
  by (auto simp add:complete_inj_def)

lemma complete_inj_dom [simp]:
  "x \<in> vs \<Longrightarrow> complete_inj f vs x = f x"
  by (simp add:complete_inj_def)

lemma complete_inj_ran [simp]:
  "\<lbrakk> x \<notin> vs; x \<in> f ` vs \<rbrakk> \<Longrightarrow> complete_inj f vs x = inv_into vs f x"
  by (simp add:complete_inj_def)

lemma complete_inj_none [simp]:
  "\<lbrakk> x \<notin> vs; x \<notin> f ` vs \<rbrakk> \<Longrightarrow> complete_inj f vs x = x"
  by (simp add:complete_inj_def)

lemma complete_inj_insert_1 [simp]:
  "complete_inj f (insert x xs) x = f x" 
  by (simp add:complete_inj_def)

lemma complete_inj_insert_2:
  "\<lbrakk> inj_on f (insert x xs); f(x) \<notin> xs \<rbrakk> \<Longrightarrow> complete_inj f (insert x xs) (f(x)) = x"
  by (simp add: complete_inj_def)

lemma complete_inj_insert_3:
  "\<lbrakk> inj_on f (insert x xs); y \<noteq> x; y \<noteq> f(x) \<rbrakk> 
     \<Longrightarrow> complete_inj f (insert x xs) y = complete_inj f xs y"
  by (auto simp add: complete_inj_def)

lemma inj_complete_inj: "\<lbrakk> inj_on f vs; f ` vs \<inter> vs = {} \<rbrakk> \<Longrightarrow> inj (complete_inj f vs)"
  apply (rule injI)
  apply (case_tac "x \<in> vs")
  apply (simp)
  apply (case_tac "y \<in> vs")
  apply (simp)
  apply (metis the_inv_into_f_eq)
  apply (case_tac "y \<in> f ` vs")
  apply (force)
  apply (simp)
  apply (force)
  apply (case_tac "x \<in> f ` vs")
  apply (force simp add:complete_inj_def)+
done

lemma surj_complete_inj: "\<lbrakk> inj_on f vs; f ` vs \<inter> vs = {} \<rbrakk> \<Longrightarrow> surj (complete_inj f vs)"
  apply (auto simp add:complete_inj_def)
  apply (smt Int_Collect disjoint_iff_not_equal imageI inf_commute inv_into_f_f)
done
   
lemma bij_complete_inj: "\<lbrakk> inj_on f vs; f ` vs \<inter> vs = {} \<rbrakk> \<Longrightarrow> bij (complete_inj f vs)"
  by (metis bij_def inj_complete_inj surj_complete_inj)

lemma complete_inj_inverse [simp]: 
  "\<lbrakk> inj_on f vs; f ` vs \<inter> vs = {} \<rbrakk> \<Longrightarrow> complete_inj f vs (complete_inj f vs x) = x"
  apply (case_tac "x \<in> vs")
  apply (simp)
  apply (subgoal_tac "f x \<notin> vs")
  apply (auto)
  apply (case_tac "x \<in> f ` vs")
  apply (auto)
done

lemma inv_complete_inj [simp]: 
  "\<lbrakk> inj_on f vs; f ` vs \<inter> vs = {} \<rbrakk> \<Longrightarrow> inv (complete_inj f vs) = complete_inj f vs"
  apply (auto simp add: inv_def)
  apply (rule)
  apply (rule some_equality)
  apply (auto)
done
  
lemma complete_inj_comp [simp]:
  assumes "inj_on f vs" "f ` vs \<inter> vs = {}" "vs = vs1 \<union> vs2" "vs1 \<inter> vs2 = {}"
  shows "complete_inj f vs = complete_inj f vs1 \<circ> complete_inj f vs2"
proof -

  from assms have "f ` vs1 \<inter> f ` vs2 = {}"
    by (metis (lifting) Diff_triv Int_commute inj_on_Un)

  with assms show ?thesis
    apply (simp)
    apply (rule ext)
    apply (case_tac "x \<in> vs2")
    apply (simp)
    apply (subgoal_tac "f x \<notin> vs1")
    apply (subgoal_tac "f x \<notin> f ` vs1")
    apply (simp)
    apply (force)
    apply (force)
    apply (simp)
    apply (case_tac "x \<in> f ` vs2")
    apply (simp)
    apply (subgoal_tac "inv_into vs2 f x \<notin> vs1")
    apply (subgoal_tac "inv_into vs2 f x \<notin> f ` vs1")
    apply (subgoal_tac "x \<notin> vs1 \<union> vs2")
    apply (subgoal_tac "x \<in> f ` (vs1 \<union> vs2)")
    apply (simp)
    apply (smt IntI UnE empty_iff image_iff inj_on_Un inv_into_f_eq)
    apply (force)
    apply (force)
    apply (subgoal_tac "inv_into vs2 f x \<in> vs2")
    apply (force)
    apply (metis inv_into_into)
    apply (metis disjoint_iff_not_equal inv_into_into)
    apply (simp)
    apply (case_tac "x \<in> vs1")
    apply (force)
    apply (case_tac "x \<in> f ` vs1")
    apply (simp)
    apply (subgoal_tac "x \<in> f ` (vs1 \<union> vs2)")
    apply (simp)
    apply (metis (lifting, full_types) UnE image_iff inj_on_Un inv_into_f_eq)
    apply (force)
    apply (simp)
    apply (metis UnE complete_inj_def image_Un)
  done
qed

lemma complete_inj_image [simp]:
  "\<lbrakk> inj_on f vs1; f ` vs1 \<inter> vs1 = {} \<rbrakk> 
   \<Longrightarrow> complete_inj f vs1 ` vs2 = 
       f ` (vs2 \<inter> vs1) \<union> inv_into vs1 f ` (vs2 \<inter> f ` vs1) \<union> (vs2 \<inter> -(vs1 \<union> f ` vs1))"
  apply (auto)
  apply (smt Int_iff complete_inj_def imageI)
  apply (smt Int_iff complete_inj_def imageI)
  apply (metis Int_iff complete_inj_dom complete_inj_inverse imageI)
  apply (metis complete_inj_dom imageI)
  apply (metis complete_inj_dom complete_inj_inverse imageI)
  apply (metis complete_inj_none image_iff)
done

subsection {* Some additional set simplifications *}

lemma set_extra_simps [simp]: 
  "vs1 - vs2 \<subseteq> vs1"
  "xs - (ys - zs) = (zs \<inter> xs) \<union> (xs - ys)"
  "xs - (ys \<union> zs) = (xs - ys) \<inter> (xs - zs)"
  "(xs \<union> ys) \<inter> ys = ys"
  "xs \<inter> (xs \<union> ys) = xs"
  "ys \<inter> (xs \<union> ys) = ys"
  "(xs \<union> (ys - zs)) - ys = (xs - ys)"
  by (auto)

lemma insert_member [simp]: 
  "x \<in> xs \<Longrightarrow> insert x xs = xs"
  by auto

text {* Unfortunately we have to hide the algebra lattice syntax so it doesn't conflict
        with the builtin HOL version. *}

no_notation
  le (infixl "\<sqsubseteq>\<index>" 50) and
  lless (infixl "\<sqsubset>\<index>" 50) and
  sup ("\<Squnion>\<index>_" [90] 90) and
  inf ("\<Sqinter>\<index>_" [90] 90) and
  join (infixl "\<squnion>\<index>" 65) and
  meet (infixl "\<sqinter>\<index>" 70) and
  top ("\<top>\<index>") and
  bottom ("\<bottom>\<index>") and
  LFP ("\<mu>\<index>") and
  GFP ("\<nu>\<index>")

end