(*  Title:      RTS/JinjaSuppl/ClassesChanged.thy
    Author:    Susannah Mansky, UIUC 2020
    Description: Theory around the classes changed from one program to another
*)

section "@{term classes_changed} theory"

theory ClassesChanged
imports JinjaDCI.Decl
begin

text "A class is considered changed if it exists only in one program or the other,
  or exists in both but is different."
definition classes_changed :: "'m prog \<Rightarrow> 'm prog \<Rightarrow> cname set" where
"classes_changed P1 P2 = {cn. class P1 cn \<noteq> class P2 cn}"

definition class_changed :: "'m prog \<Rightarrow> 'm prog \<Rightarrow> cname \<Rightarrow> bool" where
"class_changed P1 P2 cn = (class P1 cn \<noteq> class P2 cn)"

lemma classes_changed_class_changed[simp]: "cn \<in> classes_changed P1 P2 = class_changed P1 P2 cn"
 by (simp add: classes_changed_def class_changed_def)

lemma classes_changed_self[simp]: "classes_changed P P = {}"
 by (auto simp: class_changed_def)

lemma classes_changed_sym: "classes_changed P P' = classes_changed P' P"
 by (auto simp: class_changed_def)

lemma classes_changed_class: "\<lbrakk> cn \<notin> classes_changed P P'\<rbrakk> \<Longrightarrow> class P cn = class P' cn"
 by (clarsimp simp: class_changed_def)

lemma classes_changed_class_set: "\<lbrakk> S \<inter> classes_changed P P' = {} \<rbrakk>
  \<Longrightarrow> \<forall>C \<in> S. class P C = class P' C"
 by (fastforce simp: disjoint_iff_not_equal dest: classes_changed_class)

text "We now relate @{term classes_changed} over two programs to those
 over programs with an added class (such as a test class)."

lemma classes_changed_cons_eq:
 "classes_changed (t # P) P' = (classes_changed P P' - {fst t})
                     \<union> (if class_changed [t] P' (fst t) then {fst t} else {})"
 by (auto simp: classes_changed_def class_changed_def class_def)

lemma class_changed_cons:
 "fst t \<notin> classes_changed (t#P) (t#P')"
 by (simp add: class_changed_def class_def)

lemma classes_changed_cons:
 "classes_changed (t # P) (t # P') = classes_changed P P' - {fst t}"
proof(cases "fst t \<in> classes_changed P P'")
  case True
  then show ?thesis using class_changed_cons[where t=t and P=P and P'=P']
    classes_changed_cons_eq[where t=t] by (auto simp: class_changed_def class_cons)
next
  case False
  then show ?thesis using class_changed_cons[where t=t and P=P and P'=P']
    by (auto simp: class_changed_def) (metis (no_types, lifting) class_cons)+
qed

lemma classes_changed_int_Cons:
assumes "coll \<inter> classes_changed P P' = {}"
shows "coll \<inter> classes_changed (t # P) (t # P') = {}"
proof(cases "fst t \<in> classes_changed P P'")
  case True
  then have "classes_changed P P' = classes_changed (t # P) (t # P') \<union> {fst t}"
    using classes_changed_cons[where t=t and P=P and P'=P'] by fastforce
  then show ?thesis using assms by simp
next
  case False
  then have "classes_changed P P' = classes_changed (t # P) (t # P')"
    using classes_changed_cons[where t=t and P=P and P'=P'] by fastforce
  then show ?thesis using assms by simp
qed

end