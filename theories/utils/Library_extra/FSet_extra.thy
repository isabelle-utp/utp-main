theory FSet_extra
imports FSet
begin

setup_lifting type_definition_fset

notation fempty ("\<lbrace>\<rbrace>")
notation fset ("\<langle>_\<rangle>\<^sub>f")
notation fminus (infixl "-\<^sub>f" 65)

syntax
  "_FinFset" :: "args => 'a fset"    ("\<lbrace>(_)\<rbrace>")

translations
  "\<lbrace>x, xs\<rbrace>" == "CONST finsert x \<lbrace>xs\<rbrace>"
  "\<lbrace>x\<rbrace>" == "CONST finsert x \<lbrace>\<rbrace>"

term "fBall"
  
syntax
  "_fBall" :: "pttrn => 'a fset => bool => bool" ("(3\<forall> _|\<in>|_./ _)" [0, 0, 10] 10)
  "_fBex"  :: "pttrn => 'a fset => bool => bool" ("(3\<exists> _|\<in>|_./ _)" [0, 0, 10] 10)
  
translations
  "\<forall> x|\<in>|A. P" == "CONST fBall A (%x. P)"
  "\<exists> x|\<in>|A. P" == "CONST fBex A (%x. P)"

lemma fset_intro:
  "fset x = fset y \<Longrightarrow> x = y"
  by (simp add:fset_inject)

lemma fset_elim:
  "\<lbrakk> x = y; fset x = fset y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)
  
lemma fmember_intro:
  "\<lbrakk> x \<in> fset(xs) \<rbrakk> \<Longrightarrow> x |\<in>| xs"
  by (metis fmember.rep_eq)
  
lemma fmember_elim:
  "\<lbrakk> x |\<in>| xs; x \<in> fset(xs) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis fmember.rep_eq)

lemma fnmember_intro [intro]:
  "\<lbrakk> x \<notin> fset(xs) \<rbrakk> \<Longrightarrow> x |\<notin>| xs"
  by (metis fmember.rep_eq)
  
lemma fnmember_elim [elim]:
  "\<lbrakk> x |\<notin>| xs; x \<notin> fset(xs) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis fmember.rep_eq)

lemma fsubset_intro [intro]:
  "\<langle>xs\<rangle>\<^sub>f \<subseteq> \<langle>ys\<rangle>\<^sub>f \<Longrightarrow> xs |\<subseteq>| ys"
  by (metis less_eq_fset.rep_eq)
  
lemma fsubset_elim [elim]:
  "\<lbrakk> xs |\<subseteq>| ys; \<langle>xs\<rangle>\<^sub>f \<subseteq> \<langle>ys\<rangle>\<^sub>f \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis less_eq_fset.rep_eq)
  
lemma fBall_intro [intro]:
  "Ball \<langle>A\<rangle>\<^sub>f P \<Longrightarrow> fBall A P"
  by (metis (poly_guards_query) fBallI fmember.rep_eq)
  
lemma fBall_elim [elim]:
  "\<lbrakk> fBall A P; Ball \<langle>A\<rangle>\<^sub>f P \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (metis fBallE fmember.rep_eq)
  
lift_definition finset :: "'a list \<Rightarrow> 'a fset" is set ..
  
context linorder
begin

lemma sorted_list_of_set_inj:
  "\<lbrakk> finite xs; finite ys; sorted_list_of_set xs = sorted_list_of_set ys \<rbrakk>
   \<Longrightarrow> xs = ys"
  apply (simp add:sorted_list_of_set_def)
  apply (induct xs rule:finite_induct)
  apply (induct ys rule:finite_induct)
  apply (simp_all)
  apply (metis finite.insertI insert_not_empty sorted_list_of_set_def sorted_list_of_set_empty sorted_list_of_set_eq_Nil_iff)
  apply (metis finite.insertI finite_list set_remdups set_sort sorted_list_of_set_def sorted_list_of_set_sort_remdups)
done

definition flist :: "'a fset \<Rightarrow> 'a list" where
"flist xs = sorted_list_of_set (fset xs)"

lemma flist_inj: "inj flist"
  apply (simp add:flist_def inj_on_def)
  apply (clarify)
  apply (subgoal_tac "fset x = fset y")
  apply (simp add:fset_inject)
  apply (rule sorted_list_of_set_inj, simp_all)
done

lemma flist_props [simp]:
  "sorted (flist xs)"
  "distinct (flist xs)"
  by (simp_all add:flist_def)

lemma flist_empty [simp]:
  "flist \<lbrace>\<rbrace> = []"
  by (simp add:flist_def)

lemma flist_inv [simp]: "finset (flist xs) = xs"
  by (simp add:finset_def flist_def fset_inverse)

lemma flist_set [simp]: "set (flist xs) = fset xs"
  by (simp add:finset_def flist_def fset_inverse)

lemma fset_inv [simp]: "\<lbrakk> sorted xs; distinct xs \<rbrakk> \<Longrightarrow> flist (finset xs) = xs"
  apply (simp add:finset_def flist_def fset_inverse)
  apply (metis finset.abs_eq finset.rep_eq local.sorted_list_of_set_sort_remdups local.sorted_sort_id remdups_id_iff_distinct)
done

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
  
end
