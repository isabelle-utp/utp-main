(*  Title:      RTS/JinjaSuppl/Subcls.thy
    Author:    Susannah Mansky, UIUC 2020
    Description:  Theory for the subcls relation
*)

section "@{term subcls} theory"

theory Subcls
imports JinjaDCI.TypeRel
begin

lemma subcls_class_ex: "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* C'; C \<noteq> C' \<rbrakk>
 \<Longrightarrow> \<exists>D' fs ms. class P C = \<lfloor>(D', fs, ms)\<rfloor>"
proof(induct rule: converse_rtrancl_induct)
  case (step y z) then show ?case by(auto dest: subcls1D)
qed(simp)

lemma class_subcls1:
 "\<lbrakk> class P y = class P' y; P \<turnstile> y \<prec>\<^sup>1 z \<rbrakk> \<Longrightarrow> P' \<turnstile> y \<prec>\<^sup>1 z"
 by(auto dest!: subcls1D intro!: subcls1I intro: sym)


lemma subcls1_single_valued: "single_valued (subcls1 P)"
by (clarsimp simp: single_valued_def subcls1.simps)

lemma subcls_confluent:
  "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* C'; P \<turnstile> C \<preceq>\<^sup>* C'' \<rbrakk> \<Longrightarrow> P \<turnstile> C' \<preceq>\<^sup>* C'' \<or> P \<turnstile> C'' \<preceq>\<^sup>* C'"
 by (simp add: single_valued_confluent subcls1_single_valued)

lemma subcls1_confluent: "\<lbrakk> P \<turnstile> a \<prec>\<^sup>1 b; P \<turnstile> a \<preceq>\<^sup>* c; a \<noteq> c \<rbrakk> \<Longrightarrow> P \<turnstile> b \<preceq>\<^sup>* c"
using subcls1_single_valued
 by (auto elim!: converse_rtranclE[where x=a] simp: single_valued_def)


lemma subcls_self_superclass: "\<lbrakk> P \<turnstile> C \<prec>\<^sup>1 C; P \<turnstile> C \<preceq>\<^sup>* D \<rbrakk> \<Longrightarrow> D = C"
using subcls1_single_valued
 by (auto elim!: rtrancl_induct[where b=D] simp: single_valued_def)

lemma subcls_of_Obj_acyclic:
 "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* Object; C \<noteq> D\<rbrakk> \<Longrightarrow> \<not>(P \<turnstile> C \<preceq>\<^sup>* D \<and> P \<turnstile> D \<preceq>\<^sup>* C)"
proof(induct arbitrary: D rule: converse_rtrancl_induct)
  case base then show ?case by simp
next
  case (step y z) show ?case
  proof(cases "y=z")
    case True with step show ?thesis by simp
  next
    case False show ?thesis
    proof(cases "z = D")
      case True with False step.hyps(3)[of y] show ?thesis by clarsimp
    next
      case neq: False
      with step.hyps(3) have "\<not>(P \<turnstile> z \<preceq>\<^sup>* D \<and> P \<turnstile> D \<preceq>\<^sup>* z)" by simp
      moreover from step.hyps(1)
      have "P \<turnstile> D \<preceq>\<^sup>* y \<Longrightarrow> P \<turnstile> D \<preceq>\<^sup>* z" by(simp add: rtrancl_into_rtrancl)
      moreover from step.hyps(1) step.prems(1)
      have "P \<turnstile> y \<preceq>\<^sup>* D \<Longrightarrow> P \<turnstile> z \<preceq>\<^sup>* D" by(simp add: subcls1_confluent)
      ultimately show ?thesis by clarsimp
    qed
  qed
qed

lemma subcls_of_Obj: "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* Object; P \<turnstile> C \<preceq>\<^sup>* D \<rbrakk> \<Longrightarrow> P \<turnstile> D \<preceq>\<^sup>* Object"
 by(auto dest: subcls_confluent)

end