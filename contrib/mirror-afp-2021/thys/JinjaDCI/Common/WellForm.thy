(*  Title:      JinjaDCI/Common/WellForm.thy

    Author:     Tobias Nipkow, Susannah Mansky
    Copyright   2003 Technische Universitaet Muenchen, 2019-20 UIUC

    Based on the Jinja theory J/WellForm.thy by Tobias Nipkow
*)

section \<open> Generic Well-formedness of programs \<close>

theory WellForm imports TypeRel SystemClasses begin

text \<open>\noindent This theory defines global well-formedness conditions
for programs but does not look inside method bodies.  Hence it works
for both Jinja and JVM programs. Well-typing of expressions is defined
elsewhere (in theory @{text WellType}).

Because Jinja does not have method overloading, its policy for method
overriding is the classical one: \emph{covariant in the result type
but contravariant in the argument types.} This means the result type
of the overriding method becomes more specific, the argument types
become more general.
\<close>

type_synonym 'm wf_mdecl_test = "'m prog \<Rightarrow> cname \<Rightarrow> 'm mdecl \<Rightarrow> bool"

definition wf_fdecl :: "'m prog \<Rightarrow> fdecl \<Rightarrow> bool"
where
  "wf_fdecl P \<equiv> \<lambda>(F,b,T). is_type P T"

definition wf_mdecl :: "'m wf_mdecl_test \<Rightarrow> 'm wf_mdecl_test"
where
  "wf_mdecl wf_md P C \<equiv> \<lambda>(M,b,Ts,T,m).
  (\<forall>T\<in>set Ts. is_type P T) \<and> is_type P T \<and> wf_md P C (M,b,Ts,T,m)"

definition wf_clinit :: "'m mdecl list \<Rightarrow> bool" where
"wf_clinit ms = (\<exists>m. (clinit,Static,[],Void,m)\<in>set ms)"

definition wf_cdecl :: "'m wf_mdecl_test \<Rightarrow> 'm prog \<Rightarrow> 'm cdecl \<Rightarrow> bool"
where
  "wf_cdecl wf_md P  \<equiv>  \<lambda>(C,(D,fs,ms)).
  (\<forall>f\<in>set fs. wf_fdecl P f) \<and>  distinct_fst fs \<and>
  (\<forall>m\<in>set ms. wf_mdecl wf_md P C m) \<and>  distinct_fst ms \<and>
  (C \<noteq> Object \<longrightarrow>
   is_class P D \<and> \<not> P \<turnstile> D \<preceq>\<^sup>* C \<and>
   (\<forall>(M,b,Ts,T,m)\<in>set ms.
      \<forall>D' b' Ts' T' m'. P \<turnstile> D sees M,b':Ts' \<rightarrow> T' = m' in D' \<longrightarrow>
                       b = b' \<and> P \<turnstile> Ts' [\<le>] Ts \<and> P \<turnstile> T \<le> T')) \<and>
  wf_clinit ms"

definition wf_syscls :: "'m prog \<Rightarrow> bool"
where
  "wf_syscls P  \<equiv>  {Object} \<union> sys_xcpts \<subseteq> set(map fst P)"

definition wf_prog :: "'m wf_mdecl_test \<Rightarrow> 'm prog \<Rightarrow> bool"
where
  "wf_prog wf_md P  \<equiv>  wf_syscls P \<and> (\<forall>c \<in> set P. wf_cdecl wf_md P c) \<and> distinct_fst P"


subsection\<open> Well-formedness lemmas \<close>

lemma class_wf: 
  "\<lbrakk>class P C = Some c; wf_prog wf_md P\<rbrakk> \<Longrightarrow> wf_cdecl wf_md P (C,c)"
(*<*)by (unfold wf_prog_def class_def) (fast dest: map_of_SomeD)(*>*)


lemma class_Object [simp]: 
  "wf_prog wf_md P \<Longrightarrow> \<exists>C fs ms. class P Object = Some (C,fs,ms)"
(*<*)by (unfold wf_prog_def wf_syscls_def class_def)
        (auto simp: map_of_SomeI)
(*>*)


lemma is_class_Object [simp]:
  "wf_prog wf_md P \<Longrightarrow> is_class P Object"
(*<*)by (simp add: is_class_def)(*>*)

lemma is_class_supclass:
assumes wf: "wf_prog wf_md P" and sub: "P \<turnstile> C \<preceq>\<^sup>* D"
shows "is_class P C \<Longrightarrow> is_class P D"
(*<*)
using sub proof(induct)
  case step then show ?case
    by(auto simp:wf_cdecl_def is_class_def dest!:class_wf[OF _ wf] subcls1D)
qed simp
(*>*)

lemma is_class_xcpt:
  "\<lbrakk> C \<in> sys_xcpts; wf_prog wf_md P \<rbrakk> \<Longrightarrow> is_class P C"
(*<*)
by (fastforce intro!: map_of_SomeI
              simp add: wf_prog_def wf_syscls_def is_class_def class_def)
(*>*)


lemma subcls1_wfD:
assumes sub1: "P \<turnstile> C \<prec>\<^sup>1 D" and wf: "wf_prog wf_md P"
shows "D \<noteq> C \<and> (D,C) \<notin> (subcls1 P)\<^sup>+"
(*<*)
proof -
  obtain fs ms where "C \<noteq> Object" and cls: "class P C = \<lfloor>(D, fs, ms)\<rfloor>"
    using subcls1D[OF sub1] by clarify
  then show ?thesis using wf class_wf[OF cls wf] r_into_trancl[OF sub1]
    by(force simp add: wf_cdecl_def reflcl_trancl [THEN sym]
             simp del: reflcl_trancl)
qed
(*>*)


lemma wf_cdecl_supD: 
  "\<lbrakk>wf_cdecl wf_md P (C,D,r); C \<noteq> Object\<rbrakk> \<Longrightarrow> is_class P D"
(*<*)by (auto simp: wf_cdecl_def)(*>*)


lemma subcls_asym:
  "\<lbrakk> wf_prog wf_md P; (C,D) \<in> (subcls1 P)\<^sup>+ \<rbrakk> \<Longrightarrow> (D,C) \<notin> (subcls1 P)\<^sup>+"
(*<*)by(erule tranclE; fast dest!: subcls1_wfD intro: trancl_trans)(*>*)


lemma subcls_irrefl:
  "\<lbrakk> wf_prog wf_md P; (C,D) \<in> (subcls1 P)\<^sup>+ \<rbrakk> \<Longrightarrow> C \<noteq> D"
(*<*)by (erule trancl_trans_induct) (auto dest: subcls1_wfD subcls_asym)(*>*)


lemma acyclic_subcls1:
  "wf_prog wf_md P \<Longrightarrow> acyclic (subcls1 P)"
(*<*)by (unfold acyclic_def) (fast dest: subcls_irrefl)(*>*)


lemma wf_subcls1:
  "wf_prog wf_md P \<Longrightarrow> wf ((subcls1 P)\<inverse>)"
(*<*)
proof -
  assume wf: "wf_prog wf_md P"
  have "finite (subcls1 P)" by(rule finite_subcls1)
  then have fin': "finite ((subcls1 P)\<inverse>)" by(subst finite_converse)

  from wf have "acyclic (subcls1 P)" by(rule acyclic_subcls1)
  then have acyc': "acyclic ((subcls1 P)\<inverse>)" by (subst acyclic_converse)

  from fin' acyc' show ?thesis by (rule finite_acyclic_wf)
qed
(*>*)


lemma single_valued_subcls1:
  "wf_prog wf_md G \<Longrightarrow> single_valued (subcls1 G)"
(*<*)
by(auto simp:wf_prog_def distinct_fst_def single_valued_def dest!:subcls1D)
(*>*)


lemma subcls_induct: 
  "\<lbrakk> wf_prog wf_md P; \<And>C. \<forall>D. (C,D) \<in> (subcls1 P)\<^sup>+ \<longrightarrow> Q D \<Longrightarrow> Q C \<rbrakk> \<Longrightarrow> Q C"
(*<*)
  (is "?A \<Longrightarrow> PROP ?P \<Longrightarrow> _")
proof -
  assume p: "PROP ?P"
  assume ?A then have wf: "wf_prog wf_md P" by assumption
  have wf':"wf (((subcls1 P)\<^sup>+)\<inverse>)" using wf_trancl[OF wf_subcls1[OF wf]]
    by(simp only: trancl_converse)
  show ?thesis using wf_induct[where a = C and P = Q, OF wf' p] by simp
qed
(*>*)


lemma subcls1_induct_aux:
assumes "is_class P C" and wf: "wf_prog wf_md P" and QObj: "Q Object"
shows
 "\<lbrakk> \<And>C D fs ms.
    \<lbrakk> C \<noteq> Object; is_class P C; class P C = Some (D,fs,ms) \<and>
      wf_cdecl wf_md P (C,D,fs,ms) \<and> P \<turnstile> C \<prec>\<^sup>1 D \<and> is_class P D \<and> Q D\<rbrakk> \<Longrightarrow> Q C \<rbrakk>
  \<Longrightarrow> Q C"
(*<*)
  (is "PROP ?P \<Longrightarrow> _")
proof -
  assume p: "PROP ?P"
  have "class P C \<noteq> None \<longrightarrow> Q C"
  proof(induct rule: subcls_induct[OF wf])
    case (1 C)
    have "class P C \<noteq> None \<Longrightarrow> Q C"
    proof(cases "C = Object")
      case True
      then show ?thesis using QObj by fast
    next
      case False
      assume nNone: "class P C \<noteq> None"
      then have is_cls: "is_class P C" by(simp add: is_class_def)
      obtain D fs ms where cls: "class P C = \<lfloor>(D, fs, ms)\<rfloor>" using nNone by safe
      also have wfC: "wf_cdecl wf_md P (C, D, fs, ms)" by(rule class_wf[OF cls wf])
      moreover have D: "is_class P D" by(rule wf_cdecl_supD[OF wfC False])
      moreover have "P \<turnstile> C \<prec>\<^sup>1 D" by(rule subcls1I[OF cls False])
      moreover have "class P D \<noteq> None" using D by(simp add: is_class_def)
      ultimately show ?thesis using 1 by (auto intro: p[OF False is_cls])
    qed
  then show "class P C \<noteq> None \<longrightarrow> Q C" by simp
  qed
  thus ?thesis using assms by(unfold is_class_def) simp
qed
(*>*)

(* FIXME can't we prove this one directly?? *)
lemma subcls1_induct [consumes 2, case_names Object Subcls]:
  "\<lbrakk> wf_prog wf_md P; is_class P C; Q Object;
    \<And>C D. \<lbrakk>C \<noteq> Object; P \<turnstile> C \<prec>\<^sup>1 D; is_class P D; Q D\<rbrakk> \<Longrightarrow> Q C \<rbrakk>
  \<Longrightarrow> Q C"
(*<*)by (erule (2) subcls1_induct_aux) blast(*>*)


lemma subcls_C_Object:
assumes "class": "is_class P C" and wf: "wf_prog wf_md P"
shows "P \<turnstile> C \<preceq>\<^sup>* Object"
(*<*)
using wf "class"
proof(induct rule: subcls1_induct)
  case Subcls
  then show ?case by(simp add: converse_rtrancl_into_rtrancl)
qed fast
(*>*)


lemma is_type_pTs:
assumes "wf_prog wf_md P" and "(C,S,fs,ms) \<in> set P" and "(M,b,Ts,T,m) \<in> set ms"
shows "set Ts \<subseteq> types P"
(*<*)
proof
  from assms have "wf_mdecl wf_md P C (M,b,Ts,T,m)" 
    by (unfold wf_prog_def wf_cdecl_def) auto
  hence "\<forall>t \<in> set Ts. is_type P t" by (unfold wf_mdecl_def) auto
  moreover fix t assume "t \<in> set Ts"
  ultimately have "is_type P t" by blast
  thus "t \<in> types P" ..
qed
(*>*)

lemma wf_supercls_distinct_app:
assumes wf:"wf_prog wf_md P"
  and nObj: "C \<noteq> Object" and cls: "class P C = \<lfloor>(D, fs, ms)\<rfloor>"
  and super: "supercls_lst P (C#Cs)" and dist: "distinct (C#Cs)"
shows "distinct (D#C#Cs)"
proof -
  have "\<not> P \<turnstile> D \<preceq>\<^sup>* C" using subcls1_wfD[OF subcls1I[OF cls nObj] wf]
    by (simp add: rtrancl_eq_or_trancl)
  then show ?thesis using assms by auto
qed


subsection\<open> Well-formedness and method lookup \<close>

lemma sees_wf_mdecl:
assumes wf: "wf_prog wf_md P" and sees: "P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in D"
shows "wf_mdecl wf_md P D (M,b,Ts,T,m)"
(*<*)
using wf visible_method_exists[OF sees] proof(cases b)
qed (fastforce simp:wf_cdecl_def dest!:class_wf dest:map_of_SomeD)+
(*>*)

lemma sees_method_mono [rule_format (no_asm)]: 
assumes sub: "P \<turnstile> C' \<preceq>\<^sup>* C" and wf: "wf_prog wf_md P"
shows "\<forall>D b Ts T m. P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in D \<longrightarrow>
     (\<exists>D' Ts' T' m'. P \<turnstile> C' sees M,b:Ts'\<rightarrow>T' = m' in D' \<and> P \<turnstile> Ts [\<le>] Ts' \<and> P \<turnstile> T' \<le> T)"
(*<*)
  (is "\<forall>D b Ts T m. ?P C D b Ts T m \<longrightarrow> ?Q C' D b Ts T m")
proof(rule disjE[OF rtranclD[OF sub]])
  assume "C' = C"
  then show ?thesis using assms by fastforce
next
  assume "C' \<noteq> C \<and> (C', C) \<in> (subcls1 P)\<^sup>+"
  then have neq: "C' \<noteq> C" and subcls1: "(C', C) \<in> (subcls1 P)\<^sup>+" by simp+
  show ?thesis proof(induct rule: trancl_trans_induct[OF subcls1])
    case (2 x y z)
    then have zy: "\<And>D b Ts T m. ?P z D b Ts T m \<Longrightarrow> ?Q y D b Ts T m" by blast
    have "\<And>D b Ts T m. ?P z D b Ts T m \<Longrightarrow> ?Q x D b Ts T m"
    proof -
      fix D b Ts T m assume P: "?P z D b Ts T m"
      then show "?Q x D b Ts T m" using zy[OF P] 2(2)
        by(fast elim: widen_trans widens_trans)
    qed
    then show ?case by blast
  next
    case (1 x y)
    have "\<And>D b Ts T m. ?P y D b Ts T m \<Longrightarrow> ?Q x D b Ts T m"
    proof -
      fix D b Ts T m assume P: "?P y D b Ts T m"
      then obtain Mm where sees: "P \<turnstile> y sees_methods Mm" and
                           M: "Mm M = \<lfloor>((b, Ts, T, m), D)\<rfloor>"
        by(clarsimp simp:Method_def)
      obtain fs ms where nObj: "x \<noteq> Object" and
                         cls: "class P x = \<lfloor>(y, fs, ms)\<rfloor>"
        using subcls1D[OF 1] by clarsimp
      have x_meth: "P \<turnstile> x sees_methods Mm ++ (map_option (\<lambda>m. (m, x)) \<circ> map_of ms)"
        using sees_methods_rec[OF cls nObj sees] by simp
      show "?Q x D b Ts T m" proof(cases "map_of ms M")
        case None
        then have "\<exists>m'. P \<turnstile> x sees M, b :  Ts\<rightarrow>T = m' in D" using M x_meth
          by(fastforce simp add:Method_def map_add_def split:option.split)
        then show ?thesis by auto
      next
        case (Some a)
        then obtain b' Ts' T' m' where a: "a = (b',Ts',T',m')" by(cases a)
        then have "(\<exists>m' Mm. P \<turnstile> y sees_methods Mm \<and> Mm M = \<lfloor>((b, Ts, T, m'), D)\<rfloor>)
              \<longrightarrow> b' = b \<and> P \<turnstile> Ts [\<le>] Ts' \<and> P \<turnstile> T' \<le> T"
          using nObj class_wf[OF cls wf] map_of_SomeD[OF Some]
          by(clarsimp simp: wf_cdecl_def Method_def) fast
        then show ?thesis using Some a sees M x_meth
          by(fastforce simp:Method_def map_add_def split:option.split)
      qed
    qed
    then show ?case by simp
  qed
qed
(*>*)


lemma sees_method_mono2:
  "\<lbrakk> P \<turnstile> C' \<preceq>\<^sup>* C; wf_prog wf_md P;
     P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in D; P \<turnstile> C' sees M,b':Ts'\<rightarrow>T' = m' in D' \<rbrakk>
  \<Longrightarrow> b = b' \<and> P \<turnstile> Ts [\<le>] Ts' \<and> P \<turnstile> T' \<le> T"
(*<*)by(blast dest:sees_method_mono sees_method_fun)(*>*)

lemma mdecls_visible:
assumes wf: "wf_prog wf_md P" and "class": "is_class P C"
shows "\<And>D fs ms. class P C = Some(D,fs,ms)
         \<Longrightarrow> \<exists>Mm. P \<turnstile> C sees_methods Mm \<and> (\<forall>(M,b,Ts,T,m) \<in> set ms. Mm M = Some((b,Ts,T,m),C))"
(*<*)
using wf "class"
proof (induct rule:subcls1_induct)
  case Object
  with wf have dfst:"distinct_fst ms"
    by (unfold class_def wf_prog_def wf_cdecl_def) (fastforce dest:map_of_SomeD)
  with dfst have "distinct_fst ms"
    by(blast dest: distinct_fst_appendD)
  with Object show ?case by(fastforce intro!: sees_methods_Object map_of_SomeI)
next
  case Subcls
  with wf have dfst:"distinct_fst ms"
    by (unfold class_def wf_prog_def wf_cdecl_def) (fastforce dest:map_of_SomeD)
  with dfst have "distinct_fst ms"
    by(blast dest: distinct_fst_appendD)
  with Subcls show ?case
    by(fastforce elim:sees_methods_rec dest:subcls1D map_of_SomeI
                simp:is_class_def)
qed
(*>*)

lemma mdecl_visible:
assumes wf: "wf_prog wf_md P" and C: "(C,S,fs,ms) \<in> set P" and  m: "(M,b,Ts,T,m) \<in> set ms"
shows "P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in C"
(*<*)
proof -
  from wf C have "class": "class P C = Some (S,fs,ms)"
    by (auto simp add: wf_prog_def class_def is_class_def intro: map_of_SomeI)
  from "class" have "is_class P C" by(auto simp:is_class_def)                   
  with assms "class" show ?thesis
    by(bestsimp simp:Method_def dest:mdecls_visible)
qed
(*>*)


lemma Call_lemma:
assumes sees: "P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in D" and sub: "P \<turnstile> C' \<preceq>\<^sup>* C" and wf: "wf_prog wf_md P"
shows "\<exists>D' Ts' T' m'.
       P \<turnstile> C' sees M,b:Ts'\<rightarrow>T' = m' in D' \<and> P \<turnstile> Ts [\<le>] Ts' \<and> P \<turnstile> T' \<le> T \<and> P \<turnstile> C' \<preceq>\<^sup>* D'
       \<and> is_type P T' \<and> (\<forall>T\<in>set Ts'. is_type P T) \<and> wf_md P D' (M,b,Ts',T',m')"
(*<*)
using assms sees_method_mono[OF sub wf sees]
by(fastforce intro:sees_method_decl_above dest:sees_wf_mdecl
             simp: wf_mdecl_def)
(*>*)


lemma wf_prog_lift:
  assumes wf: "wf_prog (\<lambda>P C bd. A P C bd) P"
  and rule:
  "\<And>wf_md C M b Ts C T m bd.
   wf_prog wf_md P \<Longrightarrow>
   P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in C \<Longrightarrow>
   set Ts \<subseteq>  types P \<Longrightarrow>
   bd = (M,b,Ts,T,m) \<Longrightarrow>
   A P C bd \<Longrightarrow>
   B P C bd"
  shows "wf_prog (\<lambda>P C bd. B P C bd) P"
(*<*)
proof -
  have "\<And>c. c\<in>set P \<Longrightarrow> wf_cdecl A P c \<Longrightarrow> wf_cdecl B P c"
  proof -
    fix c assume "c\<in>set P" and "wf_cdecl A P c"
    then show "wf_cdecl B P c"
     using rule[OF wf mdecl_visible[OF wf] is_type_pTs[OF wf]]
     by (auto simp: wf_cdecl_def wf_mdecl_def)
  qed
  then show ?thesis using wf by (clarsimp simp: wf_prog_def)
qed
(*>*)

lemma wf_sees_clinit:
assumes wf:"wf_prog wf_md P" and ex: "class P C = Some a"
shows "\<exists>m. P \<turnstile> C sees clinit,Static:[] \<rightarrow> Void = m in C"
proof -
  from ex obtain D fs ms where "a = (D,fs,ms)" by(cases a)
  then have sP: "(C, D, fs, ms) \<in> set P" using ex map_of_SomeD[of P C a] by(simp add: class_def)
  then have "wf_clinit ms" using assms by(unfold wf_prog_def wf_cdecl_def, auto)
  then obtain m where sm: "(clinit, Static, [], Void, m) \<in> set ms" by (meson wf_clinit_def)
  then have "P \<turnstile> C sees clinit,Static:[] \<rightarrow> Void = m in C"
    using mdecl_visible[OF wf sP sm] by simp
  then show ?thesis by(rule exI)
qed
(*>*)

lemma wf_sees_clinit1:
assumes wf:"wf_prog wf_md P" and ex: "class P C = Some a"
and "P \<turnstile> C sees clinit,b:Ts \<rightarrow> T = m in D"
shows "b = Static \<and> Ts = [] \<and> T = Void \<and> D = C"
proof -
  obtain m' where sees: "P \<turnstile> C sees clinit,Static:[] \<rightarrow> Void = m' in C"
    using wf_sees_clinit[OF wf ex] by clarify
  then show ?thesis using sees wf by (meson assms(3) sees_method_fun)
qed

lemma wf_NonStatic_nclinit:
assumes wf: "wf_prog wf_md P" and meth: "P \<turnstile> C sees M,NonStatic:Ts\<rightarrow>T=(mxs,mxl,ins,xt) in D"
shows "M \<noteq> clinit"
proof -
  from sees_method_is_class[OF meth] obtain a where cls: "class P C = Some a"
    by(clarsimp simp: is_class_def)
  with wf wf_sees_clinit[OF wf cls]
   obtain m where "P \<turnstile> C sees clinit,Static:[]\<rightarrow>Void=m in C" by clarsimp
  with meth show ?thesis by(auto dest: sees_method_fun)
qed

subsection\<open> Well-formedness and field lookup \<close>

lemma wf_Fields_Ex:
assumes wf: "wf_prog wf_md P" and "is_class P C"
shows "\<exists>FDTs. P \<turnstile> C has_fields FDTs"
(*<*)
using assms proof(induct rule:subcls1_induct)
  case Object
  then show ?case using class_Object[OF wf]
    by(blast intro:has_fields_Object)
next
  case Subcls
  then show ?case by(blast intro:has_fields_rec dest:subcls1D)
qed
(*>*)


lemma has_fields_types:
  "\<lbrakk> P \<turnstile> C has_fields FDTs; (FD,b,T) \<in> set FDTs; wf_prog wf_md P \<rbrakk> \<Longrightarrow> is_type P T"
(*<*)
proof(induct rule:Fields.induct)
qed(fastforce dest!: class_wf simp: wf_cdecl_def wf_fdecl_def)+
(*>*)

lemma sees_field_is_type:
  "\<lbrakk> P \<turnstile> C sees F,b:T in D; wf_prog wf_md P \<rbrakk> \<Longrightarrow> is_type P T"
(*<*)
  by (meson has_field_def has_fields_types has_visible_field map_of_SomeD)
(*>*)


lemma wf_syscls:
  "set SystemClasses \<subseteq> set P \<Longrightarrow> wf_syscls P"
(*<*)
by (force simp: image_def SystemClasses_def wf_syscls_def sys_xcpts_def
                ObjectC_def NullPointerC_def ClassCastC_def OutOfMemoryC_def
                NoClassDefFoundC_def
                IncompatibleClassChangeC_def NoSuchFieldC_def NoSuchMethodC_def)
(*>*)


subsection\<open> Well-formedness and subclassing \<close>

lemma wf_subcls_nCls:
assumes wf: "wf_prog wf_md P" and ns: "\<not> is_class P C"
shows "\<lbrakk> P \<turnstile> D \<preceq>\<^sup>* D'; D \<noteq> C \<rbrakk> \<Longrightarrow> D' \<noteq> C"
proof(induct rule: rtrancl.induct)
  case (rtrancl_into_rtrancl a b c)
  with ns show ?case by(clarsimp dest!: subcls1D wf_cdecl_supD[OF class_wf[OF _ wf]])
qed(simp)

lemma wf_subcls_nCls':
assumes wf: "wf_prog wf_md P" and ns: "\<not>is_class P C\<^sub>0"
shows "\<And>cd D'. cd \<in> set P \<Longrightarrow> \<not>P \<turnstile> fst cd \<preceq>\<^sup>* C\<^sub>0"
proof -
  fix cd D' assume cd: "cd \<in> set P"
  then have cls: "is_class P (fst cd)" using class_exists_equiv is_class_def by blast
  with wf_subcls_nCls[OF wf ns] ns show "\<not>P \<turnstile> fst cd \<preceq>\<^sup>* C\<^sub>0" by(cases "fst cd = D'", auto)
qed

lemma wf_nclass_nsub:
 "\<lbrakk> wf_prog wf_md P; is_class P C; \<not>is_class P C' \<rbrakk> \<Longrightarrow> \<not>P \<turnstile> C \<preceq>\<^sup>* C'"
 by(rule notI, auto dest: wf_subcls_nCls[where C=C' and D=C])

lemma wf_sys_xcpt_nsub_Start:
assumes wf: "wf_prog wf_md P" and ns: "\<not>is_class P Start" and sx: "C \<in> sys_xcpts"
shows "\<not>P \<turnstile> C \<preceq>\<^sup>* Start"
proof -
  have Cns: "C \<noteq> Start" using Start_nsys_xcpts sx by clarsimp
  show ?thesis using wf_subcls_nCls[OF wf ns _ Cns] by auto
qed

end
