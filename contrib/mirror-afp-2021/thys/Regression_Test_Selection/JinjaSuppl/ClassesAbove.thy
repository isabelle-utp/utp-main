(*  Title:      RTS/JinjaSuppl/ClassesAbove.thy
    Author:    Susannah Mansky, UIUC 2020
*)

section "@{term classes_above} theory"

text "This section contains theory around the classes above
 (superclasses of) a class in the class structure, in particular
 noting that if their contents have not changed, then much of what
 that class sees (methods, fields) stays the same."

theory ClassesAbove
imports ClassesChanged Subcls JinjaDCI.Exceptions
begin

abbreviation classes_above :: "'m prog \<Rightarrow> cname \<Rightarrow> cname set" where
"classes_above P c \<equiv> { cn. P \<turnstile> c \<preceq>\<^sup>* cn }"

abbreviation classes_between :: "'m prog \<Rightarrow> cname \<Rightarrow> cname \<Rightarrow> cname set" where
"classes_between P c d \<equiv> { cn. (P \<turnstile> c \<preceq>\<^sup>* cn \<and> P \<turnstile> cn \<preceq>\<^sup>* d) }"

abbreviation classes_above_xcpts :: "'m prog \<Rightarrow> cname set" where
"classes_above_xcpts P \<equiv> \<Union>x\<in>sys_xcpts. classes_above P x"

(******************************************************************************)

lemma classes_above_def2:
 "P \<turnstile> C \<prec>\<^sup>1 D \<Longrightarrow> classes_above P C = {C} \<union> classes_above P D"
using subcls1_confluent by auto

lemma classes_above_class:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {}; P \<turnstile> C \<preceq>\<^sup>* C' \<rbrakk>
  \<Longrightarrow> class P C' = class P' C'"
 by (drule classes_changed_class_set, simp)

lemma classes_above_subset:
assumes "classes_above P C \<inter> classes_changed P P' = {}"
shows "classes_above P C \<subseteq> classes_above P' C"
proof -
  have ind: "\<And>x. P \<turnstile> C \<preceq>\<^sup>* x \<Longrightarrow> P' \<turnstile> C \<preceq>\<^sup>* x"
  proof -
    fix x assume sub: "P \<turnstile> C \<preceq>\<^sup>* x"
    then show "P' \<turnstile> C \<preceq>\<^sup>* x"
    proof(induct rule: rtrancl_induct)
      case base then show ?case by simp
    next
      case (step y z)
      have "P' \<turnstile> y \<prec>\<^sup>1 z" by(rule class_subcls1[OF classes_above_class[OF assms step(1)] step(2)])
      then show ?case using step(3) by simp
    qed
  qed
  with classes_changed_class_set[OF assms] show ?thesis by clarsimp
qed

lemma classes_above_subcls:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {}; P \<turnstile> C \<preceq>\<^sup>* C' \<rbrakk>
   \<Longrightarrow> P' \<turnstile> C \<preceq>\<^sup>* C'"
 by (fastforce dest: classes_above_subset)

lemma classes_above_subset2:
assumes "classes_above P C \<inter> classes_changed P P' = {}"
shows "classes_above P' C \<subseteq> classes_above P C"
proof -
  have ind: "\<And>x. P' \<turnstile> C \<preceq>\<^sup>* x \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* x"
  proof -
    fix x assume sub: "P' \<turnstile> C \<preceq>\<^sup>* x"
    then show "P \<turnstile> C \<preceq>\<^sup>* x"
    proof(induct rule: rtrancl_induct)
      case base then show ?case by simp
    next
      case (step y z)
      with class_subcls1 classes_above_class[OF assms] rtrancl_into_rtrancl show ?case by metis
    qed
  qed
  with classes_changed_class_set[OF assms] show ?thesis by clarsimp
qed

lemma classes_above_subcls2:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {}; P' \<turnstile> C \<preceq>\<^sup>* C' \<rbrakk>
   \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* C'"
 by (fastforce dest: classes_above_subset2)

lemma classes_above_set:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {} \<rbrakk>
  \<Longrightarrow> classes_above P C = classes_above P' C"
 by(fastforce dest: classes_above_subset classes_above_subset2)

lemma classes_above_classes_changed_sym:
assumes "classes_above P C \<inter> classes_changed P P' = {}"
shows "classes_above P' C \<inter> classes_changed P' P = {}"
proof -
  have "classes_above P C = classes_above P' C" by(rule classes_above_set[OF assms])
  with classes_changed_sym[where P=P] assms show ?thesis by simp
qed

lemma classes_above_sub_classes_between_eq:
 "P \<turnstile> C \<preceq>\<^sup>* D \<Longrightarrow> classes_above P C = (classes_between P C D - {D}) \<union> classes_above P D"
using subcls_confluent by auto

lemma classes_above_subcls_subset:
 "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* C' \<rbrakk> \<Longrightarrow> classes_above P C' \<subseteq> classes_above P C"
 by auto

(************************************************************)
subsection "Methods"

lemma classes_above_sees_methods:
assumes int: "classes_above P C \<inter> classes_changed P P' = {}" and ms: "P \<turnstile> C sees_methods Mm"
shows "P' \<turnstile> C sees_methods Mm"
proof -
  have cls: "\<forall>C'\<in>classes_above P C. class P C' = class P' C'"
   by(rule classes_changed_class_set[OF int])

  have "\<And>C Mm. P \<turnstile> C sees_methods Mm \<Longrightarrow>
               \<forall>C'\<in>classes_above P C. class P C' = class P' C' \<Longrightarrow> P' \<turnstile> C sees_methods Mm"
  proof -
    fix C Mm assume "P \<turnstile> C sees_methods Mm" and "\<forall>C'\<in>classes_above P C. class P C' = class P' C'"
    then show "P' \<turnstile> C sees_methods Mm"
    proof(induct rule: Methods.induct)
      case Obj: (sees_methods_Object D fs ms Mm)
      with cls have "class P' Object = \<lfloor>(D, fs, ms)\<rfloor>" by simp
      with Obj show ?case by(auto intro!: sees_methods_Object)
    next
      case rec: (sees_methods_rec C D fs ms Mm Mm')
      then have "P \<turnstile> C \<preceq>\<^sup>* D" by (simp add: r_into_rtrancl[OF subcls1I])
      with converse_rtrancl_into_rtrancl have "\<And>x. P \<turnstile> D \<preceq>\<^sup>* x \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* x" by simp
      with rec.prems(1) have "\<forall>C'\<in>classes_above P D. class P C' = class P' C'" by simp
      with rec show ?case by(auto intro: sees_methods_rec)
    qed
  qed
  with ms cls show ?thesis by simp
qed

lemma classes_above_sees_method:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {};
     P \<turnstile> C sees M,b: Ts\<rightarrow>T = m in C' \<rbrakk>
  \<Longrightarrow> P' \<turnstile> C sees M,b: Ts\<rightarrow>T = m in C'"
 by (auto dest: classes_above_sees_methods simp: Method_def)

lemma classes_above_sees_method2:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {};
     P' \<turnstile> C sees M,b: Ts\<rightarrow>T = m in C' \<rbrakk>
  \<Longrightarrow> P \<turnstile> C sees M,b: Ts\<rightarrow>T = m in C'"
 by (auto dest: classes_above_classes_changed_sym intro: classes_above_sees_method)

lemma classes_above_method:
assumes "classes_above P C \<inter> classes_changed P P' = {}"
shows "method P C M = method P' C M"
proof(cases "\<exists>Ts T m D b. P \<turnstile> C sees M,b :  Ts\<rightarrow>T = m in D")
  case True
  with assms show ?thesis by (auto dest: classes_above_sees_method)
next
  case False
  with assms have "\<not>(\<exists>Ts T m D b. P' \<turnstile> C sees M,b :  Ts\<rightarrow>T = m in D)"
    by (auto dest: classes_above_sees_method2)
  with False show ?thesis by(simp add: method_def)
qed

(*********************************************)
subsection "Fields"

lemma classes_above_has_fields:
assumes int: "classes_above P C \<inter> classes_changed P P' = {}" and fs: "P \<turnstile> C has_fields FDTs"
shows "P' \<turnstile> C has_fields FDTs"
proof -
  have cls: "\<forall>C'\<in>classes_above P C. class P C' = class P' C'"
   by(rule classes_changed_class_set[OF int])

  have "\<And>C Mm. P \<turnstile> C has_fields FDTs \<Longrightarrow>
               \<forall>C'\<in>classes_above P C. class P C' = class P' C' \<Longrightarrow> P' \<turnstile> C has_fields FDTs"
  proof -
    fix C Mm assume "P \<turnstile> C has_fields FDTs" and "\<forall>C'\<in>classes_above P C. class P C' = class P' C'"
    then show "P' \<turnstile> C has_fields FDTs"
    proof(induct rule: Fields.induct)
      case Obj: (has_fields_Object D fs ms FDTs)
      with cls have "class P' Object = \<lfloor>(D, fs, ms)\<rfloor>" by simp
      with Obj show ?case by(auto intro!: has_fields_Object)
    next
      case rec: (has_fields_rec C D fs ms FDTs FDTs')
      then have "P \<turnstile> C \<preceq>\<^sup>* D" by (simp add: r_into_rtrancl[OF subcls1I])
      with converse_rtrancl_into_rtrancl have "\<And>x. P \<turnstile> D \<preceq>\<^sup>* x \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* x" by simp
      with rec.prems(1) have "\<forall>x. P \<turnstile> D \<preceq>\<^sup>* x \<longrightarrow> class P x = class P' x" by simp
      with rec show ?case by(auto intro: has_fields_rec)
    qed
  qed
  with fs cls show ?thesis by simp
qed

lemma classes_above_has_fields_dne:
assumes "classes_above P C \<inter> classes_changed P P' = {}"
shows "(\<forall>FDTs. \<not> P \<turnstile> C has_fields FDTs) = (\<forall>FDTs. \<not> P' \<turnstile> C has_fields FDTs)"
proof(rule iffI)
  assume asm: "\<forall>FDTs. \<not> P \<turnstile> C has_fields FDTs"
  from assms classes_changed_sym[where P=P] classes_above_set[OF assms]
   have int': "classes_above P' C \<inter> classes_changed P' P = {}" by simp
  from asm classes_above_has_fields[OF int'] show "\<forall>FDTs. \<not> P' \<turnstile> C has_fields FDTs" by auto
next
  assume "\<forall>FDTs. \<not> P' \<turnstile> C has_fields FDTs"
  with assms show "\<forall>FDTs. \<not> P \<turnstile> C has_fields FDTs" by(auto dest: classes_above_has_fields)
qed

lemma classes_above_has_field:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {};
    P \<turnstile> C has F,b:t in C' \<rbrakk>
   \<Longrightarrow> P' \<turnstile> C has F,b:t in C'"
 by(auto dest: classes_above_has_fields simp: has_field_def)

lemma classes_above_has_field2:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {};
     P' \<turnstile> C has F,b:t in C' \<rbrakk>
  \<Longrightarrow> P \<turnstile> C has F,b:t in C'"
 by(auto intro: classes_above_has_field dest: classes_above_classes_changed_sym)

lemma classes_above_sees_field:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {};
    P \<turnstile> C sees F,b:t in C' \<rbrakk>
   \<Longrightarrow> P' \<turnstile> C sees F,b:t in C'"
 by(auto dest: classes_above_has_fields simp: sees_field_def)

lemma classes_above_sees_field2:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {};
     P' \<turnstile> C sees F,b:t in C' \<rbrakk>
  \<Longrightarrow> P \<turnstile> C sees F,b:t in C'"
 by (auto intro: classes_above_sees_field dest: classes_above_classes_changed_sym)

lemma classes_above_field:
assumes "classes_above P C \<inter> classes_changed P P' = {}"
shows "field P C F = field P' C F"
proof(cases "\<exists>T D b. P \<turnstile> C sees F,b : T in D")
  case True
  with assms show ?thesis by (auto dest: classes_above_sees_field)
next
  case False
  with assms have "\<not>(\<exists>T D b. P' \<turnstile> C sees F,b : T in D)"
    by (auto dest: classes_above_sees_field2)
  with False show ?thesis by(simp add: field_def)
qed

lemma classes_above_fields:
assumes "classes_above P C \<inter> classes_changed P P' = {}"
shows "fields P C = fields P' C"
proof(cases "\<exists>FDTs. P \<turnstile> C has_fields FDTs")
  case True
  with assms show ?thesis by(auto dest: classes_above_has_fields)
next
  case False
  with assms show ?thesis by (auto dest: classes_above_has_fields_dne simp: fields_def)
qed

lemma classes_above_ifields:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {} \<rbrakk>
 \<Longrightarrow>
  ifields P C = ifields P' C"
 by (simp add: ifields_def classes_above_fields)


lemma classes_above_blank:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {} \<rbrakk>
 \<Longrightarrow>
  blank P C = blank P' C"
 by (simp add: blank_def classes_above_ifields)

lemma classes_above_isfields:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {} \<rbrakk>
 \<Longrightarrow>
  isfields P C = isfields P' C"
 by (simp add: isfields_def classes_above_fields)

lemma classes_above_sblank:
 "\<lbrakk> classes_above P C \<inter> classes_changed P P' = {} \<rbrakk>
 \<Longrightarrow>
  sblank P C = sblank P' C"
 by (simp add: sblank_def classes_above_isfields)

(******************************************)
subsection "Other"

lemma classes_above_start_heap:
assumes "classes_above_xcpts P \<inter> classes_changed P P' = {}"
shows "start_heap P = start_heap P'"
proof -
  from assms have "\<forall>C \<in> sys_xcpts. blank P C = blank P' C" by (auto intro: classes_above_blank)
  then show ?thesis by(simp add: start_heap_def)
qed

end