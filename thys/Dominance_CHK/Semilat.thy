
(*  Title:      HOL/MicroJava/BV/Semilat.thy
    Author:     Tobias Nipkow
    Copyright   2000 TUM

Semilattices.
*)

section \<open>Semilattices\<close>

theory Semilat
imports Main 
begin

text \<open>Most definitions are lemmas in this theory are extracted from Jinja \cite{Semilat-AFP}, 
      'order r' is redefined to 'order r A', so related lemmas are also modified. \<close>

type_synonym 'a ord    = "'a \<Rightarrow> 'a \<Rightarrow> bool"
type_synonym 'a binop  = "'a \<Rightarrow> 'a \<Rightarrow> 'a"
type_synonym 'a sl     = "'a set \<times> 'a ord \<times> 'a binop"

definition lesub :: "'a \<Rightarrow> 'a ord \<Rightarrow> 'a \<Rightarrow> bool"
  where "lesub x r y \<longleftrightarrow> r x y"

definition lesssub :: "'a \<Rightarrow> 'a ord \<Rightarrow> 'a \<Rightarrow> bool"
  where "lesssub x r y \<longleftrightarrow> lesub x r y \<and> x \<noteq> y"

definition plussub :: "'a \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'c"
  where "plussub x f y = f x y"
                                       
notation (ASCII)
  "lesub"  ("(_ /<='__ _)" [50, 1000, 51] 50) and
  "lesssub"  ("(_ /<'__ _)" [50, 1000, 51] 50) and
  "plussub"  ("(_ /+'__ _)" [65, 1000, 66] 65)

notation
  "lesub"  ("(_ /\<sqsubseteq>\<^bsub>_\<^esub> _)" [50, 0, 51] 50) and
  "lesssub"  ("(_ /\<sqsubset>\<^bsub>_\<^esub> _)" [50, 0, 51] 50) and
  "plussub"  ("(_ /\<squnion>\<^bsub>_\<^esub> _)" [65, 0, 66] 65)


(* allow \<sub> instead of \<bsub>..\<esub> *)
abbreviation (input)
  lesub1 :: "'a \<Rightarrow> 'a ord \<Rightarrow> 'a \<Rightarrow> bool" ("(_ /\<sqsubseteq>\<^sub>_ _)" [50, 1000, 51] 50)
  where "x \<sqsubseteq>\<^sub>r y == x \<sqsubseteq>\<^bsub>r\<^esub> y"

abbreviation (input)
  lesssub1 :: "'a \<Rightarrow> 'a ord \<Rightarrow> 'a \<Rightarrow> bool" ("(_ /\<sqsubset>\<^sub>_ _)" [50, 1000, 51] 50)
  where "x \<sqsubset>\<^sub>r y == x \<sqsubset>\<^bsub>r\<^esub> y"

abbreviation (input)
  plussub1 :: "'a \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'c" ("(_ /\<squnion>\<^sub>_ _)" [65, 1000, 66] 65)
  where "x \<squnion>\<^sub>f y == x \<squnion>\<^bsub>f\<^esub> y"

definition ord :: "('a \<times> 'a) set \<Rightarrow> 'a ord"
where
  "ord r = (\<lambda>x y. (x,y) \<in> r)"

definition order :: "'a ord \<Rightarrow> 'a set \<Rightarrow> bool"
where
  "order r A \<longleftrightarrow> (\<forall>x\<in>A. x \<sqsubseteq>\<^sub>r x) \<and> (\<forall>x\<in>A. \<forall>y\<in>A. x \<sqsubseteq>\<^sub>r y \<and> y \<sqsubseteq>\<^sub>r x \<longrightarrow> x=y) \<and> (\<forall>x\<in>A.  \<forall>y\<in>A. \<forall>z\<in>A. x \<sqsubseteq>\<^sub>r y \<and> y \<sqsubseteq>\<^sub>r z \<longrightarrow> x \<sqsubseteq>\<^sub>r z)"

definition top :: "'a ord \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow>  bool"
where
  "top r T A \<longleftrightarrow> (\<forall>x\<in>A. x \<sqsubseteq>\<^sub>r T)"
  
definition acc :: "'a ord \<Rightarrow>  bool"
where
  "acc r \<longleftrightarrow> wf {(y,x). x \<sqsubset>\<^sub>r y }"

definition closed :: "'a set \<Rightarrow> 'a binop \<Rightarrow> bool"
where
  "closed A f \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>A. x \<squnion>\<^sub>f y \<in> A)"

definition semilat :: "'a sl \<Rightarrow> bool"
where
  "semilat = (\<lambda>(A,r,f). order r A \<and> closed A f \<and> 
                       (\<forall>x\<in>A. \<forall>y\<in>A. x \<sqsubseteq>\<^sub>r x \<squnion>\<^sub>f y) \<and>
                       (\<forall>x\<in>A. \<forall>y\<in>A. y \<sqsubseteq>\<^sub>r x \<squnion>\<^sub>f y) \<and>
                       (\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A. x \<sqsubseteq>\<^sub>r z \<and> y \<sqsubseteq>\<^sub>r z \<longrightarrow> x \<squnion>\<^sub>f y \<sqsubseteq>\<^sub>r z))"

definition is_ub :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "is_ub r x y u \<longleftrightarrow> (x,u)\<in>r \<and> (y,u)\<in>r"

definition is_lub :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "is_lub r x y u \<longleftrightarrow> is_ub r x y u \<and> (\<forall>z. is_ub r x y z \<longrightarrow> (u,z)\<in>r)"

definition some_lub :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "some_lub r x y = (SOME z. is_lub r x y z)"

lemma closedD: "\<lbrakk> closed A f; x\<in>A; y\<in>A \<rbrakk> \<Longrightarrow> x \<squnion>\<^sub>f y \<in> A"
  (*<*) by (unfold closed_def) blast (*>*)


lemma order_trans: "\<lbrakk> order r A;  x \<sqsubseteq>\<^sub>r y;  y \<sqsubseteq>\<^sub>r z \<rbrakk> \<Longrightarrow>  x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> x \<sqsubseteq>\<^sub>r z"
  (*<*) by (unfold order_def) blast (*>*)

lemma order_antisym: "\<lbrakk> order r A; x \<sqsubseteq>\<^sub>r y; y \<sqsubseteq>\<^sub>r x \<rbrakk> \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow>  x = y"
  (*<*) by (unfold order_def) ( simp (no_asm_simp)) (*>*)

lemma order_refl [simp, intro]: "order r A \<Longrightarrow> x \<in> A \<Longrightarrow>  x \<sqsubseteq>\<^sub>r x"
  (*<*) by (unfold order_def) (simp (no_asm_simp)) (*>*)

locale Semilat =
  fixes A :: "'a set"
  fixes r :: "'a ord"
  fixes f :: "'a binop"
  assumes semilat: "semilat (A, r, f)"

lemma semilat_Def:
"semilat(A,r,f) \<longleftrightarrow> order r A \<and> closed A f \<and> 
                 (\<forall>x\<in>A. \<forall>y\<in>A. x \<sqsubseteq>\<^sub>r x \<squnion>\<^sub>f y) \<and> 
                 (\<forall>x\<in>A. \<forall>y\<in>A. y \<sqsubseteq>\<^sub>r x \<squnion>\<^sub>f y) \<and> 
                 (\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A. x \<sqsubseteq>\<^sub>r z \<and> y \<sqsubseteq>\<^sub>r z \<longrightarrow> x \<squnion>\<^sub>f y \<sqsubseteq>\<^sub>r z)"
  (*<*) by (unfold semilat_def) clarsimp (*>*)

lemma (in Semilat) orderI [simp, intro]: "order r A"
  (*<*) using semilat by (simp add: semilat_Def) (*>*)

lemma (in Semilat) refl_r [intro, simp]: "x \<in> A \<Longrightarrow> x \<sqsubseteq>\<^sub>r x" by auto

lemma (in Semilat) antisym_r [intro?]: "\<lbrakk> x \<sqsubseteq>\<^sub>r y; y \<sqsubseteq>\<^sub>r x \<rbrakk> \<Longrightarrow> x\<in>A \<Longrightarrow>y\<in>A \<Longrightarrow>x = y"
  (*<*) by (rule order_antisym) auto (*>*)

lemma (in Semilat) lub [simp, intro?]:
  "\<lbrakk> x \<sqsubseteq>\<^sub>r z; y \<sqsubseteq>\<^sub>r z; x \<in> A; y \<in> A; z \<in> A \<rbrakk> \<Longrightarrow> x \<squnion>\<^sub>f y \<sqsubseteq>\<^sub>r z"
  (*<*) by (insert semilat) (unfold semilat_Def, simp) (*>*)

lemma (in Semilat) ub2 [simp, intro?]: "\<lbrakk> x \<in> A; y \<in> A \<rbrakk> \<Longrightarrow> y \<sqsubseteq>\<^sub>r x \<squnion>\<^sub>f y"
  (*<*) by (insert semilat) (unfold semilat_Def, simp) (*>*)

lemma (in Semilat) closedI [simp, intro]: "closed A f"
  (*<*) using semilat by (simp add: semilat_Def) (*>*)

lemma (in Semilat) closed_f [simp, intro]: "\<lbrakk>x \<in> A; y \<in> A\<rbrakk>  \<Longrightarrow> x \<squnion>\<^sub>f y \<in> A"
  (*<*) by (simp add: closedD [OF closedI]) (*>*)  
  
lemma (in Semilat) ub1 [simp, intro?]: "\<lbrakk> x \<in> A; y \<in> A \<rbrakk> \<Longrightarrow> x \<sqsubseteq>\<^sub>r x \<squnion>\<^sub>f y"
  (*<*) by (insert semilat) (unfold semilat_Def, simp) (*>*)

lemma (in Semilat) le_iff_plus_unchanged:
  assumes "x \<in> A" and "y \<in> A"
  shows "x \<sqsubseteq>\<^sub>r y \<longleftrightarrow> x \<squnion>\<^sub>f y = y" (is "?P \<longleftrightarrow> ?Q")
(*<*)
proof
  assume ?P
  with assms show ?Q by (blast intro: antisym_r lub ub2)
next
  assume ?Q
  then have "y = x \<squnion>\<^bsub>f\<^esub> y" by simp
  moreover from assms have "x \<sqsubseteq>\<^bsub>r\<^esub> x \<squnion>\<^bsub>f\<^esub> y" by simp
  ultimately show ?P by simp
qed

lemma (in Semilat) plus_le_conv :
  "\<lbrakk> x \<in> A; y \<in> A; z \<in> A \<rbrakk> \<Longrightarrow> (x \<squnion>\<^sub>f y \<sqsubseteq>\<^sub>r z) = (x \<sqsubseteq>\<^sub>r z \<and> y \<sqsubseteq>\<^sub>r z)"
  (*<*) by (blast intro: ub1 ub2 lub order_trans) (*>*)


end

