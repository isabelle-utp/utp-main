(*  Title:      HOL/MicroJava/BV/Listn.thy
    Author:     Tobias Nipkow
    Copyright   2000 TUM

Lists of a fixed length. 
*)

text \<open>Most definitions and lemmas in this theory are extracted from Jinja \cite{Listn-AFP}. 
      Two lemmas "acc\_le\_listI" and "Cons\_less\_Conss" in the original Listn.thy are proved in the 'Dom\_kildall\_Property.thy'.\<close>

section \<open>Fixed Length Lists\<close>

theory Listn
imports Semilat
begin

definition list :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a list set"
where
  "list n A = {xs. size xs = n \<and> set xs \<subseteq> A}"

definition le :: "'a ord \<Rightarrow> ('a list)ord"
where
  "le r = list_all2 (\<lambda>x y. x \<sqsubseteq>\<^sub>r y)"

abbreviation
  lesublist :: "'a list \<Rightarrow> 'a ord \<Rightarrow> 'a list \<Rightarrow> bool"  ("(_ /[\<sqsubseteq>\<^bsub>_\<^esub>] _)" [50, 0, 51] 50) where
  "x [\<sqsubseteq>\<^bsub>r\<^esub>] y == x <=_(Listn.le r) y"

abbreviation
  lesssublist :: "'a list \<Rightarrow> 'a ord \<Rightarrow> 'a list \<Rightarrow> bool"  ("(_ /[\<sqsubset>\<^bsub>_\<^esub>] _)" [50, 0, 51] 50) where
  "x [\<sqsubset>\<^bsub>r\<^esub>] y == x <_(Listn.le r) y"

(*<*)
notation (ASCII)
  lesublist  ("(_ /[<=_] _)" [50, 0, 51] 50) and
  lesssublist  ("(_ /[<_] _)" [50, 0, 51] 50)

abbreviation (input)
  lesublist2 :: "'a list \<Rightarrow> 'a ord \<Rightarrow> 'a list \<Rightarrow> bool"  ("(_ /[\<sqsubseteq>\<^sub>_] _)" [50, 0, 51] 50) where
  "x [\<sqsubseteq>\<^sub>r] y == x [\<sqsubseteq>\<^bsub>r\<^esub>] y"

abbreviation (input)
  lesssublist2 :: "'a list \<Rightarrow> 'a ord \<Rightarrow> 'a list \<Rightarrow> bool"  ("(_ /[\<sqsubset>\<^sub>_] _)" [50, 0, 51] 50) where
  "x [\<sqsubset>\<^sub>r] y == x [\<sqsubset>\<^bsub>r\<^esub>] y"
(*>*)

abbreviation
  plussublist :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b list \<Rightarrow> 'c list"
    ("(_ /[\<squnion>\<^bsub>_\<^esub>] _)" [65, 0, 66] 65) where
  "x [\<squnion>\<^bsub>f\<^esub>] y == x \<squnion>\<^bsub>map2 f\<^esub> y"

(*<*)
notation (ASCII)
  plussublist  ("(_ /[+_] _)" [65, 0, 66] 65)

abbreviation (input)
  plussublist2 :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b list \<Rightarrow> 'c list"
    ("(_ /[\<squnion>\<^sub>_] _)" [65, 0, 66] 65) where
  "x [\<squnion>\<^sub>f] y == x [\<squnion>\<^bsub>f\<^esub>] y"
(*>*)

definition sl :: "nat \<Rightarrow> 'a sl \<Rightarrow> 'a list sl"
where
  "sl n = (\<lambda>(A,r,f). (list n A, le r, map2 f))"

lemmas [simp] = set_update_subsetI

lemma unfold_lesub_list: "xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys = Listn.le r xs ys"
(*<*) by (simp add: lesub_def) (*>*)

lemma le_listD: "\<lbrakk> xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys; p < size xs \<rbrakk> \<Longrightarrow> xs!p \<sqsubseteq>\<^sub>r ys!p"
(*<*)
by (simp add: Listn.le_def lesub_def list_all2_nthD)
(*>*)

lemma lesub_list_impl_same_size [simp]: "xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys \<Longrightarrow> size ys = size xs"
(*<*)
apply (unfold Listn.le_def lesub_def)
apply (simp add: list_all2_lengthD)
done
(*>*)

lemma lesssub_lengthD: "xs [\<sqsubset>\<^sub>r] ys \<Longrightarrow> size ys = size xs"  
(*<*)
apply (unfold lesssub_def)
apply auto  \<comment> \<open>use lemma: lesub_list_impl_same_size \<close>
done

lemma listI: "\<lbrakk> size xs = n; set xs \<subseteq> A \<rbrakk> \<Longrightarrow> xs \<in> list n A"
(*<*)
apply (unfold list_def)
apply blast
done
(*>*)

(* FIXME: remove simp *)
lemma listE_length [simp]: "xs \<in> list n A \<Longrightarrow> size xs = n"
(*<*)
apply (unfold list_def)
apply blast
done
(*>*)


lemma listE_set [simp]: "xs \<in> list n A \<Longrightarrow> set xs \<subseteq> A"
(*<*)
apply (unfold list_def)
apply blast
done
(*>*)


lemma in_list_Suc_iff:
  "(xs \<in> list (Suc n) A) = (\<exists>y\<in>A. \<exists>ys \<in> list n A. xs = y#ys)"
(*<*)
apply (unfold list_def)
apply (case_tac "xs")
apply auto
done

lemma nth_in [rule_format, simp]:
  "\<forall>i n. size xs = n \<longrightarrow> set xs \<subseteq> A \<longrightarrow> i < n \<longrightarrow> (xs!i) \<in> A"
(*<*)
apply (induct "xs")
 apply simp
apply (simp add: nth_Cons split: nat.split)
done


lemma listt_update_in_list [simp, intro!]:
  "\<lbrakk> xs \<in> list n A; x\<in>A \<rbrakk> \<Longrightarrow> xs[i := x] \<in> list n A" 
(*<*)
apply (unfold list_def)
apply simp
done
(*>*)


lemma Cons_le_Cons [iff]: "x#xs [\<sqsubseteq>\<^bsub>r\<^esub>] y#ys = (x \<sqsubseteq>\<^sub>r y \<and> xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys)"
(*<*)
  by (simp add: lesub_def Listn.le_def)



end
