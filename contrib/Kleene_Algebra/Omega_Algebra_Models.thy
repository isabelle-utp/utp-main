(* Title:      Kleene Algebra
   Author:     Alasdair Armstrong, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

header {* Models of Omega Algebras *}

theory Omega_Algebra_Models
imports Omega_Algebra Kleene_Algebra_Models
begin

text {* The trace, path and language model are not really interesting
in this setting. *}

subsection {* Relation Omega Algebras *}

text {* In the relational model, the omega of a relation relates all
those elements in the domain of the relation, from which an infinite
chain starts, with all other elements; all other elements are not
related to anything~\cite{hofnerstruth10nontermination}. Thus, the
omega of a relation is most naturally defined coinductively. *}

coinductive_set omega :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set" for R where
  "\<lbrakk> (x, y) \<in> R; (y, z) \<in> omega R \<rbrakk> \<Longrightarrow> (x, z) \<in> omega R"

(* FIXME: The equivalent, but perhaps more elegant point-free version
  "x \<in> R O omega R \<Longrightarrow> x \<in> omega R"
fails due to missing monotonicity lemmas. *)

text {* Isabelle automatically derives a case rule and a coinduction
theorem for @{const omega}. We prove slightly more elegant
variants. *}

lemma omega_cases: "(x, z) \<in> omega R \<Longrightarrow>
  (\<And>y. (x, y) \<in> R \<Longrightarrow> (y, z) \<in> omega R \<Longrightarrow> P) \<Longrightarrow> P"
by (metis omega.cases)

lemma omega_coinduct: "X x z \<Longrightarrow>
  (\<And>x z. X x z \<Longrightarrow> \<exists>y. (x, y) \<in> R \<and> (X y z \<or> (y, z) \<in> omega R)) \<Longrightarrow>
  (x, z) \<in> omega R"
by (metis omega.coinduct)

lemma omega_weak_coinduct: "X x z \<Longrightarrow>
  (\<And>x z. X x z \<Longrightarrow> \<exists>y. (x, y) \<in> R \<and> X y z) \<Longrightarrow>
  (x, z) \<in> omega R"
by (metis omega.coinduct)

lemma context_conjI_R:
  assumes "Q" "Q ==> P" shows "P & Q"
by (iprover intro: conjI assms)

interpretation rel_omega_algebra: omega_algebra "op \<union>" "op O" Id "{}" "op \<subseteq>" "op \<subset>" rtrancl omega
proof
  fix x y z :: "'a rel"
  show "omega x \<subseteq> x O omega x"
    by (auto elim: omega_cases)
  show "y \<subseteq> z \<union> x O y \<longrightarrow> y \<subseteq> omega x \<union> x\<^sup>* O z"
    apply auto
    apply (rule omega_weak_coinduct[where X="\<lambda>a b. (a, b) \<in> x O y \<and> (a, b) \<notin> x\<^sup>* O z"])
     apply (metis UnE in_mono relcompI rtrancl_refl)
    apply (thin_tac "(a, b) \<in> y")
    apply (thin_tac "(a, b) \<notin> x\<^sup>* O z")
    apply clarsimp
    apply (rename_tac a b c)
    apply (rule_tac x="b" in exI)
    apply simp
    apply (rule context_conjI_R)
     apply (metis rel_dioid.mult_assoc relcompI rtrancl_into_rtrancl rtrancl_refl rtrancl_idemp_self_comp)
    apply (metis UnE in_mono relcompI rtrancl_refl)
  done
qed

end
