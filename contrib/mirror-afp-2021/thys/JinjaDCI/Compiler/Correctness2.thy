(*  Title:      JinjaDCI/Compiler/Correctness2.thy
    Author:     Tobias Nipkow, Susannah Mansky
    Copyright   TUM 2003, UIUC 2019-20

    Based on the Jinja theory Compiler/Correctness2.thy by Tobias Nipkow
*)

section \<open> Correctness of Stage 2 \<close>

theory Correctness2
imports "HOL-Library.Sublist" Compiler2 J1WellForm "../J/EConform"
begin

(*<*)hide_const (open) Throw(*>*)

subsection\<open> Instruction sequences \<close>

text\<open> How to select individual instructions and subsequences of
instructions from a program given the class, method and program
counter. \<close>

definition before :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> nat \<Rightarrow> instr list \<Rightarrow> bool"
   ("(_,_,_,_/ \<rhd> _)" [51,0,0,0,51] 50) where
 "P,C,M,pc \<rhd> is \<longleftrightarrow> prefix is (drop pc (instrs_of P C M))"

definition at :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> nat \<Rightarrow> instr \<Rightarrow> bool"
   ("(_,_,_,_/ \<triangleright> _)" [51,0,0,0,51] 50) where
 "P,C,M,pc \<triangleright> i \<longleftrightarrow> (\<exists>is. drop pc (instrs_of P C M) = i#is)"

lemma [simp]: "P,C,M,pc \<rhd> []"
(*<*)by(simp add:before_def)(*>*)


lemma [simp]: "P,C,M,pc \<rhd> (i#is) = (P,C,M,pc \<triangleright> i \<and> P,C,M,pc + 1 \<rhd> is)"
(*<*)by(fastforce simp add:before_def at_def prefix_def drop_Suc drop_tl)(*>*)

(*<*)
declare drop_drop[simp del]
(*>*)


lemma [simp]: "P,C,M,pc \<rhd> (is\<^sub>1 @ is\<^sub>2) = (P,C,M,pc \<rhd> is\<^sub>1 \<and> P,C,M,pc + size is\<^sub>1 \<rhd> is\<^sub>2)"
(*<*)
apply(simp add:before_def prefix_def)
apply(subst add.commute)
apply(simp add: drop_drop[symmetric])
apply fastforce
done
(*>*)

(*<*)
declare drop_drop[simp]
(*>*)


lemma [simp]: "P,C,M,pc \<triangleright> i \<Longrightarrow> instrs_of P C M ! pc = i"
(*<*)by(clarsimp simp add:at_def strict_prefix_def nth_via_drop)(*>*)

lemma beforeM:
  "P \<turnstile> C sees M,b: Ts\<rightarrow>T = body in D \<Longrightarrow>
  compP\<^sub>2 P,D,M,0 \<rhd> compE\<^sub>2 body @ [Return]"
(*<*)
apply(drule sees_method_idemp)
apply(simp add:before_def compP\<^sub>2_def compMb\<^sub>2_def)
done
(*>*)

text\<open> This lemma executes a single instruction by rewriting: \<close>

lemma [simp]:
  "P,C,M,pc \<triangleright> instr \<Longrightarrow>
  (P \<turnstile> (None, h, (vs,ls,C,M,pc,ics) # frs, sh) -jvm\<rightarrow> \<sigma>') =
  ((None, h, (vs,ls,C,M,pc,ics) # frs, sh) = \<sigma>' \<or>
   (\<exists>\<sigma>. exec(P,(None, h, (vs,ls,C,M,pc,ics) # frs, sh)) = Some \<sigma> \<and> P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>'))"
(*<*)
apply(simp only: exec_all_def)
apply(blast intro: converse_rtranclE converse_rtrancl_into_rtrancl)
done
(*>*)


subsection\<open> Exception tables \<close>

definition pcs :: "ex_table \<Rightarrow> nat set"
where
  "pcs xt  \<equiv>  \<Union>(f,t,C,h,d) \<in> set xt. {f ..< t}"

lemma pcs_subset:
shows "(\<And>pc d. pcs(compxE\<^sub>2 e pc d) \<subseteq> {pc..<pc+size(compE\<^sub>2 e)})"
and "(\<And>pc d. pcs(compxEs\<^sub>2 es pc d) \<subseteq> {pc..<pc+size(compEs\<^sub>2 es)})"
(*<*)
apply(induct e and es rule: compxE\<^sub>2.induct compxEs\<^sub>2.induct)
apply (simp_all add:pcs_def)
apply (fastforce split:bop.splits)+
done
(*>*)


lemma [simp]: "pcs [] = {}"
(*<*)by(simp add:pcs_def)(*>*)


lemma [simp]: "pcs (x#xt) = {fst x ..< fst(snd x)} \<union> pcs xt"
(*<*)by(auto simp add: pcs_def)(*>*)


lemma [simp]: "pcs(xt\<^sub>1 @ xt\<^sub>2) = pcs xt\<^sub>1 \<union> pcs xt\<^sub>2"
(*<*)by(simp add:pcs_def)(*>*)


lemma [simp]: "pc < pc\<^sub>0 \<or> pc\<^sub>0+size(compE\<^sub>2 e) \<le> pc \<Longrightarrow> pc \<notin> pcs(compxE\<^sub>2 e pc\<^sub>0 d)"
(*<*)using pcs_subset by fastforce(*>*)


lemma [simp]: "pc < pc\<^sub>0 \<or> pc\<^sub>0+size(compEs\<^sub>2 es) \<le> pc \<Longrightarrow> pc \<notin> pcs(compxEs\<^sub>2 es pc\<^sub>0 d)"
(*<*)using pcs_subset by fastforce(*>*)


lemma [simp]: "pc\<^sub>1 + size(compE\<^sub>2 e\<^sub>1) \<le> pc\<^sub>2 \<Longrightarrow> pcs(compxE\<^sub>2 e\<^sub>1 pc\<^sub>1 d\<^sub>1) \<inter> pcs(compxE\<^sub>2 e\<^sub>2 pc\<^sub>2 d\<^sub>2) = {}"
(*<*)using pcs_subset by fastforce(*>*)


lemma [simp]: "pc\<^sub>1 + size(compE\<^sub>2 e) \<le> pc\<^sub>2 \<Longrightarrow> pcs(compxE\<^sub>2 e pc\<^sub>1 d\<^sub>1) \<inter> pcs(compxEs\<^sub>2 es pc\<^sub>2 d\<^sub>2) = {}"
(*<*)using pcs_subset by fastforce(*>*)


lemma [simp]:
 "pc \<notin> pcs xt\<^sub>0 \<Longrightarrow> match_ex_table P C pc (xt\<^sub>0 @ xt\<^sub>1) = match_ex_table P C pc xt\<^sub>1"
(*<*)by (induct xt\<^sub>0) (auto simp: matches_ex_entry_def)(*>*)


lemma [simp]: "\<lbrakk> x \<in> set xt; pc \<notin> pcs xt \<rbrakk> \<Longrightarrow> \<not> matches_ex_entry P D pc x"
(*<*)by(auto simp:matches_ex_entry_def pcs_def)(*>*)


lemma [simp]:
assumes xe: "xe \<in> set(compxE\<^sub>2 e pc d)" and outside: "pc' < pc \<or> pc+size(compE\<^sub>2 e) \<le> pc'"
shows "\<not> matches_ex_entry P C pc' xe"
(*<*)
proof
  assume "matches_ex_entry P C pc' xe"
  with xe have "pc' \<in> pcs(compxE\<^sub>2 e pc d)"
    by(force simp add:matches_ex_entry_def pcs_def)
  with outside show False by simp
qed
(*>*)


lemma [simp]:
assumes xe: "xe \<in> set(compxEs\<^sub>2 es pc d)" and outside: "pc' < pc \<or> pc+size(compEs\<^sub>2 es) \<le> pc'"
shows "\<not> matches_ex_entry P C pc' xe"
(*<*)
proof
  assume "matches_ex_entry P C pc' xe"
  with xe have "pc' \<in> pcs(compxEs\<^sub>2 es pc d)"
    by(force simp add:matches_ex_entry_def pcs_def)
  with outside show False by simp
qed
(*>*)


lemma match_ex_table_app[simp]:
  "\<forall>xte \<in> set xt\<^sub>1. \<not> matches_ex_entry P D pc xte \<Longrightarrow>
  match_ex_table P D pc (xt\<^sub>1 @ xt) = match_ex_table P D pc xt"
(*<*)by(induct xt\<^sub>1) simp_all(*>*)


lemma [simp]:
  "\<forall>x \<in> set xtab. \<not> matches_ex_entry P C pc x \<Longrightarrow>
  match_ex_table P C pc xtab = None"
(*<*)using match_ex_table_app[where ?xt = "[]"] by fastforce(*>*)


lemma match_ex_entry:
  "matches_ex_entry P C pc (start, end, catch_type, handler) =
  (start \<le> pc \<and> pc < end \<and>  P \<turnstile> C \<preceq>\<^sup>* catch_type)"
(*<*)by(simp add:matches_ex_entry_def)(*>*)


definition caught :: "jvm_prog \<Rightarrow> pc \<Rightarrow> heap \<Rightarrow> addr \<Rightarrow> ex_table \<Rightarrow> bool" where
  "caught P pc h a xt \<longleftrightarrow>
  (\<exists>entry \<in> set xt. matches_ex_entry P (cname_of h a) pc entry)"

definition beforex :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> ex_table \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> bool"
              ("(2_,/_,/_ \<rhd>/ _ /'/ _,/_)" [51,0,0,0,0,51] 50) where
  "P,C,M \<rhd> xt / I,d \<longleftrightarrow>
  (\<exists>xt\<^sub>0 xt\<^sub>1. ex_table_of P C M = xt\<^sub>0 @ xt @ xt\<^sub>1 \<and> pcs xt\<^sub>0 \<inter> I = {} \<and> pcs xt \<subseteq> I \<and>
    (\<forall>pc \<in> I. \<forall>C pc' d'. match_ex_table P C pc xt\<^sub>1 = \<lfloor>(pc',d')\<rfloor> \<longrightarrow> d' \<le> d))"

definition dummyx :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> ex_table \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> bool"  ("(2_,_,_ \<triangleright>/ _ '/_,_)" [51,0,0,0,0,51] 50) where
  "P,C,M \<triangleright> xt/I,d \<longleftrightarrow> P,C,M \<rhd> xt/I,d"

lemma beforexD1: "P,C,M \<rhd> xt / I,d \<Longrightarrow> pcs xt \<subseteq> I"
(*<*)by(auto simp add:beforex_def)(*>*)


lemma beforex_mono: "\<lbrakk> P,C,M \<rhd> xt/I,d'; d' \<le> d \<rbrakk> \<Longrightarrow> P,C,M \<rhd> xt/I,d"
(*<*)by(fastforce simp:beforex_def)(*>*)


lemma [simp]: "P,C,M \<rhd> xt/I,d \<Longrightarrow> P,C,M \<rhd> xt/I,Suc d"
(*<*)by(fastforce intro:beforex_mono)(*>*)


lemma beforex_append[simp]:
  "pcs xt\<^sub>1 \<inter> pcs xt\<^sub>2 = {} \<Longrightarrow>
  P,C,M \<rhd> xt\<^sub>1 @ xt\<^sub>2/I,d =
  (P,C,M \<rhd> xt\<^sub>1/I-pcs xt\<^sub>2,d  \<and>  P,C,M \<rhd> xt\<^sub>2/I-pcs xt\<^sub>1,d \<and> P,C,M \<triangleright> xt\<^sub>1@xt\<^sub>2/I,d)"
(*<*)
apply(rule iffI)
 prefer 2
 apply(simp add:dummyx_def)
apply(auto simp add: beforex_def dummyx_def)
 apply(rule_tac x = xt\<^sub>0 in exI)
 apply auto
apply(rule_tac x = "xt\<^sub>0@xt\<^sub>1" in exI)
apply auto
done
(*>*)


lemma beforex_appendD1:
  "\<lbrakk> P,C,M \<rhd> xt\<^sub>1 @ xt\<^sub>2 @ [(f,t,D,h,d)] / I,d;
    pcs xt\<^sub>1 \<subseteq> J; J \<subseteq> I; J \<inter> pcs xt\<^sub>2 = {} \<rbrakk>
  \<Longrightarrow> P,C,M \<rhd> xt\<^sub>1 / J,d"
(*<*)
apply(auto simp:beforex_def)
apply(rule exI,rule exI,rule conjI, rule refl)
apply(rule conjI, blast)
apply(auto)
apply(subgoal_tac "pc \<notin> pcs xt\<^sub>2")
 prefer 2 apply blast
apply (auto split:if_split_asm)
done
(*>*)


lemma beforex_appendD2:
  "\<lbrakk> P,C,M \<rhd> xt\<^sub>1 @ xt\<^sub>2 @ [(f,t,D,h,d)] / I,d;
    pcs xt\<^sub>2 \<subseteq> J; J \<subseteq> I; J \<inter> pcs xt\<^sub>1 = {} \<rbrakk>
  \<Longrightarrow> P,C,M \<rhd> xt\<^sub>2 / J,d"
(*<*)
apply(auto simp:beforex_def)
apply(rule_tac x = "xt\<^sub>0 @ xt\<^sub>1" in exI)
apply fastforce
done
(*>*)


lemma beforexM:
  "P \<turnstile> C sees M,b: Ts\<rightarrow>T = body in D \<Longrightarrow> compP\<^sub>2 P,D,M \<rhd> compxE\<^sub>2 body 0 0/{..<size(compE\<^sub>2 body)},0"
(*<*)
apply(drule sees_method_idemp)
apply(drule sees_method_compP[where f = compMb\<^sub>2])
apply(simp add:beforex_def compP\<^sub>2_def compMb\<^sub>2_def)
apply(rule_tac x = "[]" in exI)
using pcs_subset apply fastforce
done
(*>*)


lemma match_ex_table_SomeD2:
 "\<lbrakk> match_ex_table P D pc (ex_table_of P C M) = \<lfloor>(pc',d')\<rfloor>;
    P,C,M \<rhd> xt/I,d; \<forall>x \<in> set xt. \<not> matches_ex_entry P D pc x; pc \<in> I \<rbrakk>
 \<Longrightarrow> d' \<le> d"
(*<*)
apply(auto simp:beforex_def)
apply(subgoal_tac "pc \<notin> pcs xt\<^sub>0")
apply auto
done
(*>*)


lemma match_ex_table_SomeD1:
  "\<lbrakk> match_ex_table P D pc (ex_table_of P C M) = \<lfloor>(pc',d')\<rfloor>;
     P,C,M \<rhd> xt / I,d; pc \<in> I; pc \<notin> pcs xt \<rbrakk> \<Longrightarrow> d' \<le> d"
(*<*)by(auto elim: match_ex_table_SomeD2)(*>*)


subsection\<open> The correctness proof \<close>

(*<*)
declare nat_add_distrib[simp] caught_def[simp]
declare fun_upd_apply[simp del]
(*>*)

definition
  handle :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> addr \<Rightarrow> heap \<Rightarrow> val list \<Rightarrow> val list \<Rightarrow> nat \<Rightarrow> init_call_status \<Rightarrow> frame list \<Rightarrow> sheap
                \<Rightarrow> jvm_state" where
  "handle P C M a h vs ls pc ics frs sh = find_handler P a h ((vs,ls,C,M,pc,ics) # frs) sh"

lemma aux_isin[simp]: "\<lbrakk> B \<subseteq> A; a \<in> B \<rbrakk> \<Longrightarrow> a \<in> A"
(*<*)by blast(*>*)

lemma handle_frs_tl_neq:
 "ics_of f \<noteq> No_ics
  \<Longrightarrow> (xp, h, f#frs, sh) \<noteq> handle P C M xa h' vs l pc ics frs sh'"
 by(simp add: handle_def find_handler_frs_tl_neq del: find_handler.simps)

subsubsection "Correctness proof inductive hypothesis"

\<comment> \<open> frame definitions for use by correctness proof inductive hypothesis \<close>
fun calling_to_called :: "frame \<Rightarrow> frame" where
"calling_to_called (stk,loc,D,M,pc,ics) = (stk,loc,D,M,pc,case ics of Calling C Cs \<Rightarrow> Called (C#Cs))"

fun calling_to_scalled :: "frame \<Rightarrow> frame" where
"calling_to_scalled (stk,loc,D,M,pc,ics) = (stk,loc,D,M,pc,case ics of Calling C Cs \<Rightarrow> Called Cs)"

fun calling_to_calling :: "frame \<Rightarrow> cname \<Rightarrow> frame" where
"calling_to_calling (stk,loc,D,M,pc,ics) C' = (stk,loc,D,M,pc,case ics of Calling C Cs \<Rightarrow> Calling C' (C#Cs))"

fun calling_to_throwing :: "frame \<Rightarrow> addr \<Rightarrow> frame" where
"calling_to_throwing (stk,loc,D,M,pc,ics) a = (stk,loc,D,M,pc,case ics of Calling C Cs \<Rightarrow> Throwing (C#Cs) a)"

fun calling_to_sthrowing :: "frame \<Rightarrow> addr \<Rightarrow> frame" where
"calling_to_sthrowing (stk,loc,D,M,pc,ics) a = (stk,loc,D,M,pc,case ics of Calling C Cs \<Rightarrow> Throwing Cs a)"


\<comment> \<open> pieces of the correctness proof's inductive hypothesis, which depend on the
 expression being compiled) \<close>

fun Jcc_cond :: "J\<^sub>1_prog \<Rightarrow> ty list \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> val list \<Rightarrow> pc \<Rightarrow> init_call_status
   \<Rightarrow> nat set \<Rightarrow> heap \<Rightarrow> sheap \<Rightarrow> expr\<^sub>1 \<Rightarrow> bool" where
"Jcc_cond P E C M vs pc ics I h sh (INIT C\<^sub>0 (Cs,b) \<leftarrow> e')
  = ((\<exists>T. P,E,h,sh \<turnstile>\<^sub>1 INIT C\<^sub>0 (Cs,b) \<leftarrow> e' : T) \<and> unit = e' \<and> ics = No_ics)" |
"Jcc_cond P E C M vs pc ics I h sh (RI(C',e\<^sub>0);Cs \<leftarrow> e')
  = (((e\<^sub>0 = C'\<bullet>\<^sub>sclinit([]) \<and> (\<exists>T. P,E,h,sh \<turnstile>\<^sub>1 RI(C',e\<^sub>0);Cs \<leftarrow> e':T))
         \<or> ((\<exists>a. e\<^sub>0 = Throw a) \<and> (\<forall>C \<in> set(C'#Cs). is_class P C)))
      \<and> unit = e' \<and> ics = No_ics)" |
"Jcc_cond P E C M vs pc ics I h sh (C'\<bullet>\<^sub>sM'(es))
  = (let e = (C'\<bullet>\<^sub>sM'(es))
     in if M' = clinit \<and> es = [] then (\<exists>T. P,E,h,sh \<turnstile>\<^sub>1 e:T) \<and> (\<exists>Cs. ics = Called Cs)
        else (compP\<^sub>2 P,C,M,pc \<rhd> compE\<^sub>2 e \<and> compP\<^sub>2 P,C,M \<rhd> compxE\<^sub>2 e pc (size vs)/I,size vs
                  \<and> {pc..<pc+size(compE\<^sub>2 e)} \<subseteq> I \<and> \<not>sub_RI e \<and> ics = No_ics)
    )" |
"Jcc_cond P E C M vs pc ics I h sh e
  = (compP\<^sub>2 P,C,M,pc \<rhd> compE\<^sub>2 e \<and> compP\<^sub>2 P,C,M \<rhd> compxE\<^sub>2 e pc (size vs)/I,size vs
                  \<and> {pc..<pc+size(compE\<^sub>2 e)} \<subseteq> I \<and> \<not>sub_RI e \<and> ics = No_ics)"


fun Jcc_frames :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> val list \<Rightarrow> val list \<Rightarrow> pc \<Rightarrow> init_call_status
  \<Rightarrow> frame list \<Rightarrow> expr\<^sub>1 \<Rightarrow> frame list" where
"Jcc_frames P C M vs ls pc ics frs (INIT C\<^sub>0 (C'#Cs,b) \<leftarrow> e')
  = (case b of False \<Rightarrow> (vs,ls,C,M,pc,Calling C' Cs) # frs
             | True \<Rightarrow> (vs,ls,C,M,pc,Called (C'#Cs)) # frs
    )" |
"Jcc_frames P C M vs ls pc ics frs (INIT C\<^sub>0 (Nil,b) \<leftarrow> e')
  = (vs,ls,C,M,pc,Called [])#frs" |
"Jcc_frames P C M vs ls pc ics frs (RI(C',e\<^sub>0);Cs \<leftarrow> e')
  = (case e\<^sub>0 of Throw a \<Rightarrow> (vs,ls,C,M,pc,Throwing (C'#Cs) a) # frs
              | _ \<Rightarrow> (vs,ls,C,M,pc,Called (C'#Cs)) # frs )" |
"Jcc_frames P C M vs ls pc ics frs (C'\<bullet>\<^sub>sM'(es))
  = (if M' = clinit \<and> es = []
     then create_init_frame P C'#(vs,ls,C,M,pc,ics)#frs
     else (vs,ls,C,M,pc,ics)#frs
    )" |
"Jcc_frames P C M vs ls pc ics frs e
  = (vs,ls,C,M,pc,ics)#frs"

fun Jcc_rhs :: "J\<^sub>1_prog \<Rightarrow> ty list \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> val list \<Rightarrow> val list \<Rightarrow> pc \<Rightarrow> init_call_status
  \<Rightarrow> frame list \<Rightarrow> heap \<Rightarrow> val list \<Rightarrow> sheap \<Rightarrow> val \<Rightarrow> expr\<^sub>1 \<Rightarrow> jvm_state" where
"Jcc_rhs P E C M vs ls pc ics frs h' ls' sh' v (INIT C\<^sub>0 (Cs,b) \<leftarrow> e')
  = (None,h',(vs,ls,C,M,pc,Called [])#frs,sh')" |
"Jcc_rhs P E C M vs ls pc ics frs h' ls' sh' v (RI(C',e\<^sub>0);Cs \<leftarrow> e')
  = (None,h',(vs,ls,C,M,pc,Called [])#frs,sh')" |
"Jcc_rhs P E C M vs ls pc ics frs h' ls' sh' v (C'\<bullet>\<^sub>sM'(es))
  = (let e = (C'\<bullet>\<^sub>sM'(es))
     in if M' = clinit \<and> es = []
        then (None,h',(vs,ls,C,M,pc,ics)#frs,sh'(C'\<mapsto>(fst(the(sh' C')),Done)))
        else (None,h',(v#vs,ls',C,M,pc+size(compE\<^sub>2 e),ics)#frs,sh')
    )" |
"Jcc_rhs P E C M vs ls pc ics frs h' ls' sh' v e
  = (None,h',(v#vs,ls',C,M,pc+size(compE\<^sub>2 e),ics)#frs,sh')"

fun Jcc_err :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> heap \<Rightarrow> val list \<Rightarrow> val list \<Rightarrow> pc \<Rightarrow> init_call_status
  \<Rightarrow> frame list \<Rightarrow> sheap \<Rightarrow> nat set \<Rightarrow> heap \<Rightarrow> val list \<Rightarrow> sheap \<Rightarrow> addr \<Rightarrow> expr\<^sub>1
  \<Rightarrow> bool" where
"Jcc_err P C M h vs ls pc ics frs sh I h' ls' sh' xa (INIT C\<^sub>0 (Cs,b) \<leftarrow> e')
  = (\<exists>vs'. P \<turnstile> (None,h,Jcc_frames P C M vs ls pc ics frs (INIT C\<^sub>0 (Cs,b) \<leftarrow> e'),sh)
           -jvm\<rightarrow> handle P C M xa h' (vs'@vs) ls pc ics frs sh')" |
"Jcc_err P C M h vs ls pc ics frs sh I h' ls' sh' xa (RI(C',e\<^sub>0);Cs \<leftarrow> e')
  = (\<exists>vs'. P \<turnstile> (None,h,Jcc_frames P C M vs ls pc ics frs (RI(C',e\<^sub>0);Cs \<leftarrow> e'),sh)
           -jvm\<rightarrow> handle P C M xa h' (vs'@vs) ls pc ics frs sh')" |
"Jcc_err P C M h vs ls pc ics frs sh I h' ls' sh' xa (C'\<bullet>\<^sub>sM'(es))
  = (let e = (C'\<bullet>\<^sub>sM'(es))
     in if M' = clinit \<and> es = []
        then case ics of
               Called Cs \<Rightarrow> P \<turnstile> (None,h,Jcc_frames P C M vs ls pc ics frs e,sh)
                       -jvm\<rightarrow> (None,h',(vs,ls,C,M,pc,Throwing Cs xa)#frs,(sh'(C' \<mapsto> (fst(the(sh' C')),Error))))
        else (\<exists>pc\<^sub>1. pc \<le> pc\<^sub>1 \<and> pc\<^sub>1 < pc + size(compE\<^sub>2 e) \<and>
               \<not> caught P pc\<^sub>1 h' xa (compxE\<^sub>2 e pc (size vs)) \<and>
               (\<exists>vs'. P \<turnstile> (None,h,Jcc_frames P C M vs ls pc ics frs e,sh)
                      -jvm\<rightarrow> handle P C M xa h' (vs'@vs) ls' pc\<^sub>1 ics frs sh'))
    )" |
"Jcc_err P C M h vs ls pc ics frs sh I h' ls' sh' xa e
  = (\<exists>pc\<^sub>1. pc \<le> pc\<^sub>1 \<and> pc\<^sub>1 < pc + size(compE\<^sub>2 e) \<and>
               \<not> caught P pc\<^sub>1 h' xa (compxE\<^sub>2 e pc (size vs)) \<and>
               (\<exists>vs'. P \<turnstile> (None,h,Jcc_frames P C M vs ls pc ics frs e,sh)
                      -jvm\<rightarrow> handle P C M xa h' (vs'@vs) ls' pc\<^sub>1 ics frs sh'))"

fun Jcc_pieces :: "J\<^sub>1_prog \<Rightarrow> ty list \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> heap \<Rightarrow> val list \<Rightarrow> val list \<Rightarrow> pc \<Rightarrow> init_call_status
  \<Rightarrow> frame list \<Rightarrow> sheap \<Rightarrow> nat set \<Rightarrow> heap \<Rightarrow> val list \<Rightarrow> sheap \<Rightarrow> val \<Rightarrow> addr \<Rightarrow> expr\<^sub>1
  \<Rightarrow> bool \<times> frame list \<times> jvm_state \<times> bool" where
"Jcc_pieces P E C M h vs ls pc ics frs sh I h' ls' sh' v xa e
  = (Jcc_cond P E C M vs pc ics I h sh e, Jcc_frames (compP\<^sub>2 P) C M vs ls pc ics frs e,
      Jcc_rhs P E C M vs ls pc ics frs h' ls' sh' v e,
      Jcc_err (compP\<^sub>2 P) C M h vs ls pc ics frs sh I h' ls' sh' xa e)"

\<comment> \<open> @{text Jcc_pieces} lemmas \<close>

lemma nsub_RI_Jcc_pieces:
assumes [simp]: "P \<equiv> compP\<^sub>2 P\<^sub>1"
  and nsub: "\<not>sub_RI e"
shows "Jcc_pieces P\<^sub>1 E C M h vs ls pc ics frs sh I h' ls' sh' v xa e 
  = (let cond = P,C,M,pc \<rhd> compE\<^sub>2 e \<and> P,C,M \<rhd> compxE\<^sub>2 e pc (size vs)/I,size vs
                  \<and> {pc..<pc+size(compE\<^sub>2 e)} \<subseteq> I \<and> ics = No_ics;
         frs' = (vs,ls,C,M,pc,ics)#frs;
         rhs = (None,h',(v#vs,ls',C,M,pc+size(compE\<^sub>2 e),ics)#frs,sh');
         err = (\<exists>pc\<^sub>1. pc \<le> pc\<^sub>1 \<and> pc\<^sub>1 < pc + size(compE\<^sub>2 e) \<and>
               \<not> caught P pc\<^sub>1 h' xa (compxE\<^sub>2 e pc (size vs)) \<and>
               (\<exists>vs'. P \<turnstile> (None,h,frs',sh) -jvm\<rightarrow> handle P C M xa h' (vs'@vs) ls' pc\<^sub>1 ics frs sh'))
     in (cond, frs',rhs, err)
    )"
proof -
  have NC: "\<forall>C'. e \<noteq> C'\<bullet>\<^sub>sclinit([])" using assms(2) proof(cases e) qed(simp_all)
  then show ?thesis using assms
  proof(cases e)
    case (SCall C M es)
    then have "M \<noteq> clinit" using nsub by simp
    then show ?thesis using SCall nsub proof(cases es) qed(simp_all)
  qed(simp_all)
qed

lemma Jcc_pieces_Cast:
assumes [simp]: "P \<equiv> compP\<^sub>2 P\<^sub>1"
 and "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v xa (Cast C' e)
   = (True, frs\<^sub>0, (xp',h',(v#vs',ls',C\<^sub>0,M',pc',ics')#frs',sh'), err)"
shows "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v' xa e
   = (True, frs\<^sub>0, (xp',h',(v'#vs',ls',C\<^sub>0,M',pc' - 1,ics')#frs',sh'),
        (\<exists>pc\<^sub>1. pc \<le> pc\<^sub>1 \<and> pc\<^sub>1 < pc + size(compE\<^sub>2 e) \<and>
               \<not> caught P pc\<^sub>1 h\<^sub>1 xa (compxE\<^sub>2 e pc (size vs)) \<and>
               (\<exists>vs'. P \<turnstile> (None,h\<^sub>0,frs\<^sub>0,sh\<^sub>0) -jvm\<rightarrow> handle P C M xa h\<^sub>1 (vs'@vs) ls\<^sub>1 pc\<^sub>1 ics frs sh\<^sub>1)))"
proof -
  have pc: "{pc..<pc + length (compE\<^sub>2 e)} \<subseteq> I" using assms by clarsimp
  show ?thesis using assms nsub_RI_Jcc_pieces[where e=e] pc by clarsimp
qed

lemma Jcc_pieces_BinOp1:
assumes
 "Jcc_pieces P E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>2 ls\<^sub>2 sh\<^sub>2 v xa (e \<guillemotleft>bop\<guillemotright> e')
   = (True, frs\<^sub>0, (xp',h',(v#vs',ls',C\<^sub>0,M',pc',ics')#frs',sh'), err)"
shows "\<exists>err. Jcc_pieces P E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0
 (I - pcs (compxE\<^sub>2 e' (pc + length (compE\<^sub>2 e)) (Suc (length vs')))) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v' xa e
   = (True, frs\<^sub>0, (xp',h\<^sub>1,(v'#vs',ls\<^sub>1,C\<^sub>0,M',pc' - size (compE\<^sub>2 e') - 1,ics')#frs',sh\<^sub>1), err)"
proof -
  have bef: "compP compMb\<^sub>2 P,C\<^sub>0,M' \<rhd> compxE\<^sub>2 e pc (length vs) 
         / I - pcs (compxE\<^sub>2 e' (pc + length (compE\<^sub>2 e)) (Suc (length vs'))),length vs"
    using assms by clarsimp
  have vs: "vs = vs'" using assms by simp
  show ?thesis using assms nsub_RI_Jcc_pieces[where e=e] bef vs by clarsimp
qed

lemma Jcc_pieces_BinOp2:
assumes [simp]: "P \<equiv> compP\<^sub>2 P\<^sub>1"
 and "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>2 ls\<^sub>2 sh\<^sub>2 v xa (e \<guillemotleft>bop\<guillemotright> e')
   = (True, frs\<^sub>0, (xp',h',(v#vs',ls',C\<^sub>0,M',pc',ics')#frs',sh'), err)"
shows "\<exists>err. Jcc_pieces P\<^sub>1 E C M h\<^sub>1 (v\<^sub>1#vs) ls\<^sub>1 (pc + size (compE\<^sub>2 e)) ics frs sh\<^sub>1
   (I - pcs (compxE\<^sub>2 e pc (length vs'))) h\<^sub>2 ls\<^sub>2 sh\<^sub>2 v' xa e'
   = (True, (v\<^sub>1#vs,ls\<^sub>1,C,M,pc + size (compE\<^sub>2 e),ics)#frs,
       (xp',h',(v'#v\<^sub>1#vs',ls',C\<^sub>0,M',pc' - 1,ics')#frs',sh'),
          (\<exists>pc\<^sub>1. pc + size (compE\<^sub>2 e) \<le> pc\<^sub>1 \<and> pc\<^sub>1 < pc + size (compE\<^sub>2 e) + length (compE\<^sub>2 e') \<and>
               \<not> caught P pc\<^sub>1 h\<^sub>2 xa (compxE\<^sub>2 e' (pc + size (compE\<^sub>2 e)) (Suc (length vs))) \<and>
               (\<exists>vs'. P \<turnstile> (None,h\<^sub>1,(v\<^sub>1#vs,ls\<^sub>1,C,M,pc + size (compE\<^sub>2 e),ics)#frs,sh\<^sub>1)
                       -jvm\<rightarrow> handle P C M xa h\<^sub>2 (vs'@v\<^sub>1#vs) ls\<^sub>2 pc\<^sub>1 ics frs sh\<^sub>2)))"
proof -
  have bef: "compP compMb\<^sub>2 P\<^sub>1,C\<^sub>0,M' \<rhd> compxE\<^sub>2 e pc (length vs) 
         / I - pcs (compxE\<^sub>2 e' (pc + length (compE\<^sub>2 e)) (Suc (length vs'))),length vs"
    using assms by clarsimp
  have vs: "vs = vs'" using assms by simp
  show ?thesis using assms nsub_RI_Jcc_pieces[where e=e'] bef vs by clarsimp
qed

lemma Jcc_pieces_FAcc:
assumes
 "Jcc_pieces P E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v xa (e\<bullet>F{D})
   = (True, frs\<^sub>0, (xp',h',(v#vs',ls',C\<^sub>0,M',pc',ics')#frs',sh'), err)"
shows "\<exists>err. Jcc_pieces P E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v' xa e
   = (True, frs\<^sub>0, (xp',h',(v'#vs',ls',C\<^sub>0,M',pc' - 1,ics')#frs',sh'), err)"
proof -
  have pc: "{pc..<pc + length (compE\<^sub>2 e)} \<subseteq> I" using assms by clarsimp
  then show ?thesis using assms nsub_RI_Jcc_pieces[where e=e] by clarsimp
qed

lemma Jcc_pieces_LAss:
assumes [simp]: "P \<equiv> compP\<^sub>2 P\<^sub>1"
 and "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v xa (i:=e)
   = (True, frs\<^sub>0, (xp',h',(v#vs',ls',C\<^sub>0,M',pc',ics')#frs',sh'), err)"
shows "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v' xa e
   = (True, frs\<^sub>0, (xp',h',(v'#vs',ls',C\<^sub>0,M',pc' - 2,ics')#frs',sh'),
        (\<exists>pc\<^sub>1. pc \<le> pc\<^sub>1 \<and> pc\<^sub>1 < pc + size(compE\<^sub>2 e) \<and>
               \<not> caught P pc\<^sub>1 h\<^sub>1 xa (compxE\<^sub>2 e pc (size vs)) \<and>
               (\<exists>vs'. P \<turnstile> (None,h\<^sub>0,frs\<^sub>0,sh\<^sub>0) -jvm\<rightarrow> handle P C M xa h\<^sub>1 (vs'@vs) ls\<^sub>1 pc\<^sub>1 ics frs sh\<^sub>1)))"
proof -
  have pc: "{pc..<pc + length (compE\<^sub>2 e)} \<subseteq> I" using assms by clarsimp
  show ?thesis using assms nsub_RI_Jcc_pieces[where e=e] pc by clarsimp
qed

lemma Jcc_pieces_FAss1:
assumes
 "Jcc_pieces P E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>2 ls\<^sub>2 sh\<^sub>2 v xa (e\<bullet>F{D}:=e')
   = (True, frs\<^sub>0, (xp',h',(v#vs',ls',C\<^sub>0,M',pc',ics')#frs',sh'), err)"
shows "\<exists>err. Jcc_pieces P E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0
 (I - pcs (compxE\<^sub>2 e' (pc + length (compE\<^sub>2 e)) (Suc (length vs')))) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v' xa e
   = (True, frs\<^sub>0, (xp',h\<^sub>1,(v'#vs',ls\<^sub>1,C\<^sub>0,M',pc' - size (compE\<^sub>2 e') - 2,ics')#frs',sh\<^sub>1), err)"
proof -
  show ?thesis using assms nsub_RI_Jcc_pieces[where e=e] by clarsimp
qed

lemma Jcc_pieces_FAss2:
assumes
 "Jcc_pieces P E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>2 ls\<^sub>2 sh\<^sub>2 v xa (e\<bullet>F{D}:=e')
   = (True, frs\<^sub>0, (xp',h',(v#vs',ls',C\<^sub>0,M',pc',ics')#frs',sh'), err)"
shows "Jcc_pieces P E C M h\<^sub>1 (v\<^sub>1#vs) ls\<^sub>1 (pc + size (compE\<^sub>2 e)) ics frs sh\<^sub>1
   (I - pcs (compxE\<^sub>2 e pc (length vs'))) h\<^sub>2 ls\<^sub>2 sh\<^sub>2 v' xa e'
   = (True, (v\<^sub>1#vs,ls\<^sub>1,C,M,pc + size (compE\<^sub>2 e),ics)#frs,
       (xp',h',(v'#v\<^sub>1#vs',ls',C\<^sub>0,M',pc' - 2,ics')#frs',sh'),
        (\<exists>pc\<^sub>1. (pc + size (compE\<^sub>2 e)) \<le> pc\<^sub>1 \<and> pc\<^sub>1 < pc + size (compE\<^sub>2 e) + size(compE\<^sub>2 e') \<and>
               \<not> caught (compP\<^sub>2 P) pc\<^sub>1 h\<^sub>2 xa (compxE\<^sub>2 e' (pc + size (compE\<^sub>2 e)) (size (v\<^sub>1#vs))) \<and>
               (\<exists>vs'. (compP\<^sub>2 P) \<turnstile> (None,h\<^sub>1,(v\<^sub>1#vs,ls\<^sub>1,C,M,pc + size (compE\<^sub>2 e),ics)#frs,sh\<^sub>1)
                                   -jvm\<rightarrow> handle (compP\<^sub>2 P) C M xa h\<^sub>2 (vs'@v\<^sub>1#vs) ls\<^sub>2 pc\<^sub>1 ics frs sh\<^sub>2)))"
proof -
  show ?thesis using assms nsub_RI_Jcc_pieces[where e=e'] by clarsimp
qed

lemma Jcc_pieces_SFAss:
assumes
 "Jcc_pieces P E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h' ls' sh' v xa (C'\<bullet>\<^sub>sF{D}:=e)
   = (True, frs\<^sub>0, (xp',h',(v#vs',ls',C\<^sub>0,M',pc',ics')#frs',sh'), err)"
shows "\<exists>err. Jcc_pieces P E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v' xa e
   = (True, frs\<^sub>0, (xp',h\<^sub>1,(v'#vs',ls\<^sub>1,C\<^sub>0,M',pc' - 2,ics')#frs',sh\<^sub>1), err)"
proof -
  have pc: "{pc..<pc + length (compE\<^sub>2 e)} \<subseteq> I" using assms by clarsimp
  show ?thesis using assms nsub_RI_Jcc_pieces[where e=e] pc by clarsimp
qed

lemma Jcc_pieces_Call1:
assumes
 "Jcc_pieces P E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>3 ls\<^sub>3 sh\<^sub>3 v xa (e\<bullet>M\<^sub>0(es))
   = (True, frs\<^sub>0, (xp',h',(v#vs',ls',C',M',pc',ics')#frs',sh'), err)"
shows "\<exists>err. Jcc_pieces P E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0
    (I - pcs (compxEs\<^sub>2 es (pc + length (compE\<^sub>2 e)) (Suc (length vs')))) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v' xa e
   = (True, frs\<^sub>0,
       (xp',h\<^sub>1,(v'#vs',ls\<^sub>1,C',M',pc' - size (compEs\<^sub>2 es) - 1,ics')#frs',sh\<^sub>1), err)"
proof -
  show ?thesis using assms nsub_RI_Jcc_pieces[where e=e] by clarsimp
qed

lemma Jcc_pieces_clinit:
assumes [simp]: "P \<equiv> compP\<^sub>2 P\<^sub>1"
  and cond: "Jcc_cond P\<^sub>1 E C M vs pc ics I h sh (C1\<bullet>\<^sub>sclinit([]))"
shows "Jcc_pieces P\<^sub>1 E C M h vs ls pc ics frs sh I h' ls' sh' v xa (C1\<bullet>\<^sub>sclinit([]))
     = (True, create_init_frame P C1 # (vs,ls,C,M,pc,ics)#frs,
          (None, h', (vs,ls,C,M,pc,ics)#frs, sh'(C1\<mapsto>(fst(the(sh' C1)),Done))), 
      P \<turnstile> (None,h,create_init_frame P C1 # (vs,ls,C,M,pc,ics)#frs,sh) -jvm\<rightarrow>
     (case ics of Called Cs \<Rightarrow> (None,h',(vs,ls,C,M,pc,Throwing Cs xa)#frs,(sh'(C1 \<mapsto> (fst(the(sh' C1)),Error))))))"
using assms by(auto split: init_call_status.splits list.splits bool.splits)

lemma Jcc_pieces_SCall_clinit_body:
assumes [simp]: "P \<equiv> compP\<^sub>2 P\<^sub>1" and wf: "wf_J\<^sub>1_prog P\<^sub>1"
 and "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>3 ls\<^sub>2 sh\<^sub>3 v xa (C1\<bullet>\<^sub>sclinit([]))
         = (True, frs', rhs', err')"
 and method: "P\<^sub>1 \<turnstile> C1 sees clinit,Static: []\<rightarrow>Void = body in D"
shows "Jcc_pieces P\<^sub>1 [] D clinit h\<^sub>2 [] (replicate (max_vars body) undefined) 0
          No_ics (tl frs') sh\<^sub>2 {..<length (compE\<^sub>2 body)} h\<^sub>3 ls\<^sub>3 sh\<^sub>3 v xa body
           = (True, frs', 
                (None,h\<^sub>3,([v],ls\<^sub>3,D,clinit,size(compE\<^sub>2 body), No_ics)#tl frs',sh\<^sub>3),
                    \<exists>pc\<^sub>1. 0 \<le> pc\<^sub>1 \<and> pc\<^sub>1 < size(compE\<^sub>2 body) \<and>
                      \<not> caught P pc\<^sub>1 h\<^sub>3 xa (compxE\<^sub>2 body 0 0) \<and>
                      (\<exists>vs'. P \<turnstile> (None,h\<^sub>2,frs',sh\<^sub>2) -jvm\<rightarrow> handle P D clinit xa h\<^sub>3 vs' ls\<^sub>3 pc\<^sub>1
                            No_ics (tl frs') sh\<^sub>3))"
proof -
  have M_in_D: "P\<^sub>1 \<turnstile> D sees clinit,Static: []\<rightarrow>Void = body in D"
    using method by(rule sees_method_idemp) 
  hence M_code: "compP\<^sub>2 P\<^sub>1,D,clinit,0 \<rhd> compE\<^sub>2 body @ [Return]"
    and M_xtab: "compP\<^sub>2 P\<^sub>1,D,clinit \<rhd> compxE\<^sub>2 body 0 0/{..<size(compE\<^sub>2 body)},0"
    by(rule beforeM, rule beforexM)
  have nsub: "\<not>sub_RI body" by(rule sees_wf\<^sub>1_nsub_RI[OF wf method])
  then show ?thesis using assms nsub_RI_Jcc_pieces M_code M_xtab by clarsimp
qed

lemma Jcc_pieces_Cons:
assumes [simp]: "P \<equiv> compP\<^sub>2 P\<^sub>1"
 and "P,C,M,pc \<rhd> compEs\<^sub>2 (e#es)" and "P,C,M \<rhd> compxEs\<^sub>2 (e#es) pc (size vs)/I,size vs"
 and "{pc..<pc+size(compEs\<^sub>2 (e#es))} \<subseteq> I"
 and "ics = No_ics"
 and "\<not>sub_RIs (e#es)"
shows "Jcc_pieces P\<^sub>1 E C M h vs ls pc ics frs sh
  (I - pcs (compxEs\<^sub>2 es (pc + length (compE\<^sub>2 e)) (Suc (length vs)))) h' ls' sh' v xa e
  = (True, (vs, ls, C, M, pc, ics) # frs,
        (None, h', (v#vs, ls', C, M, pc + length (compE\<^sub>2 e), ics) # frs, sh'),
          \<exists>pc\<^sub>1\<ge>pc. pc\<^sub>1 < pc + length (compE\<^sub>2 e) \<and> \<not> caught P pc\<^sub>1 h' xa (compxE\<^sub>2 e pc (length vs))
                   \<and> (\<exists>vs'. P \<turnstile> (None, h, (vs, ls, C, M, pc, ics) # frs, sh)
                         -jvm\<rightarrow> handle P C M xa h' (vs'@vs) ls' pc\<^sub>1 ics frs sh'))"
proof -
  show ?thesis using assms nsub_RI_Jcc_pieces[where e=e] by auto
qed

lemma Jcc_pieces_InitNone:
assumes [simp]: "P \<equiv> compP\<^sub>2 P\<^sub>1"
 and "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs sh I h' l' sh' v xa (INIT C' (C\<^sub>0 # Cs,False) \<leftarrow> e)
    = (True, frs', (None, h', (vs, l, C, M, pc, Called []) # frs, sh'), err)"
shows
 "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs (sh(C\<^sub>0 \<mapsto> (sblank P C\<^sub>0, Prepared)))
     I h' l' sh' v xa (INIT C' (C\<^sub>0 # Cs,False) \<leftarrow> e)
    = (True, frs', (None, h', (vs, l, C, M, pc, Called []) # frs, sh'),
        \<exists>vs'. P \<turnstile> (None,h,frs',(sh(C\<^sub>0 \<mapsto> (sblank P\<^sub>1 C\<^sub>0, Prepared))))
            -jvm\<rightarrow> handle P C M xa h' (vs'@vs) l pc ics frs sh')"
proof -
  have  "Jcc_cond P\<^sub>1 E C M vs pc ics I h sh (INIT C' (C\<^sub>0 # Cs,False) \<leftarrow> e)" using assms by simp
  then obtain T where "P\<^sub>1,E,h,sh \<turnstile>\<^sub>1 INIT C' (C\<^sub>0 # Cs,False) \<leftarrow> unit : T" by fastforce
  then have "P\<^sub>1,E,h,sh(C\<^sub>0 \<mapsto> (sblank P\<^sub>1 C\<^sub>0, Prepared)) \<turnstile>\<^sub>1 INIT C' (C\<^sub>0 # Cs,False) \<leftarrow> unit : T"
    by(auto simp: fun_upd_apply)
  then have "Ex (WTrt2\<^sub>1 P\<^sub>1 E h (sh(C\<^sub>0 \<mapsto> (sblank P\<^sub>1 C\<^sub>0, Prepared))) (INIT C' (C\<^sub>0 # Cs,False) \<leftarrow> unit))"
    by(simp only: exI)
  then show ?thesis using assms by clarsimp
qed

lemma Jcc_pieces_InitDP:
assumes [simp]: "P \<equiv> compP\<^sub>2 P\<^sub>1"
 and "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs sh I h' l' sh' v xa (INIT C' (C\<^sub>0 # Cs,False) \<leftarrow> e)
    = (True, frs', (None, h', (vs, l, C, M, pc, Called []) # frs, sh'), err)"
shows
 "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs sh I h' l' sh' v xa (INIT C' (Cs,True) \<leftarrow> e)
    = (True, (calling_to_scalled (hd frs'))#(tl frs'),
         (None, h', (vs, l, C, M, pc, Called []) # frs, sh'),
             \<exists>vs'. P \<turnstile> (None,h,calling_to_scalled (hd frs')#(tl frs'),sh)
                        -jvm\<rightarrow> handle P C M xa h' (vs'@vs) l pc ics frs sh')"
proof -
  have "Jcc_cond P\<^sub>1 E C M vs pc ics I h sh (INIT C' (C\<^sub>0 # Cs,False) \<leftarrow> e)" using assms by simp
  then obtain T where "P\<^sub>1,E,h,sh \<turnstile>\<^sub>1 INIT C' (C\<^sub>0 # Cs,False) \<leftarrow> unit : T" by fastforce
  then have "P\<^sub>1,E,h,sh \<turnstile>\<^sub>1 INIT C' (Cs,True) \<leftarrow> unit : T"
    by (auto; metis list.sel(2) list.set_sel(2))
  then have wtrt: "Ex (WTrt2\<^sub>1 P\<^sub>1 E h sh (INIT C' (Cs,True) \<leftarrow> unit))" by(simp only: exI)
  show ?thesis using assms wtrt
  proof(cases Cs)
    case (Cons C1 Cs1)
    then show ?thesis using assms wtrt
      by(case_tac "method P C1 clinit") clarsimp
  qed(clarsimp)
qed

lemma Jcc_pieces_InitError:
assumes [simp]: "P \<equiv> compP\<^sub>2 P\<^sub>1"
 and "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs sh I h' l' sh' v xa (INIT C' (C\<^sub>0 # Cs,False) \<leftarrow> e)
    = (True, frs', (None, h', (vs, l, C, M, pc, Called []) # frs, sh'), err)"
 and err: "sh C\<^sub>0 = Some(sfs,Error)"
shows
 "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs sh I h' l' sh' v xa (RI (C\<^sub>0, THROW NoClassDefFoundError);Cs \<leftarrow> e)
    = (True, (calling_to_throwing (hd frs') (addr_of_sys_xcpt NoClassDefFoundError))#(tl frs'),
         (None, h', (vs, l, C, M, pc, Called []) # frs, sh'),
             \<exists>vs'. P \<turnstile> (None,h, (calling_to_throwing (hd frs') (addr_of_sys_xcpt NoClassDefFoundError))#(tl frs'),sh)
                        -jvm\<rightarrow> handle P C M xa h' (vs'@vs) l pc ics frs sh')"
proof -
  show ?thesis using assms
  proof(cases Cs)
    case (Cons C1 Cs1)
    then show ?thesis using assms
      by(case_tac "method P C1 clinit", case_tac "method P C\<^sub>0 clinit") clarsimp
  qed(clarsimp)
qed

lemma Jcc_pieces_InitObj:
assumes [simp]: "P \<equiv> compP\<^sub>2 P\<^sub>1"
 and "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs sh I h' l' (sh(C\<^sub>0 \<mapsto> (sfs,Processing))) v xa (INIT C' (C\<^sub>0 # Cs,False) \<leftarrow> e)
    = (True, frs', (None, h', (vs, l, C, M, pc, Called []) # frs, sh'), err)"
shows
 "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs (sh(C\<^sub>0 \<mapsto> (sfs,Processing))) I h' l' sh'' v xa (INIT C' (C\<^sub>0 # Cs,True) \<leftarrow> e)
    = (True, calling_to_called (hd frs')#(tl frs'),
         (None, h', (vs, l, C, M, pc, Called []) # frs, sh''),
             \<exists>vs'. P \<turnstile> (None,h,calling_to_called (hd frs')#(tl frs'),sh')
                        -jvm\<rightarrow> handle P C M xa h' (vs'@vs) l pc ics frs sh'')"
proof -
  have "Jcc_cond P\<^sub>1 E C M vs pc ics I h sh (INIT C' (C\<^sub>0 # Cs,False) \<leftarrow> e)" using assms by simp
  then obtain T where "P\<^sub>1,E,h,sh \<turnstile>\<^sub>1 INIT C' (C\<^sub>0 # Cs,False) \<leftarrow> unit : T" by fastforce
  then have "P\<^sub>1,E,h,sh(C\<^sub>0 \<mapsto> (sfs,Processing)) \<turnstile>\<^sub>1 INIT C' (C\<^sub>0 # Cs,True) \<leftarrow> unit : T"
    using assms by clarsimp (auto simp: fun_upd_apply)
  then have wtrt: "Ex (WTrt2\<^sub>1 P\<^sub>1 E h (sh(C\<^sub>0 \<mapsto> (sfs,Processing))) (INIT C' (C\<^sub>0 # Cs,True) \<leftarrow> unit))"
    by(simp only: exI)
  show ?thesis using assms wtrt by clarsimp
qed

lemma Jcc_pieces_InitNonObj:
assumes [simp]: "P \<equiv> compP\<^sub>2 P\<^sub>1"
 and "is_class P\<^sub>1 D" and "D \<notin> set (C\<^sub>0#Cs)" and "\<forall>C \<in> set (C\<^sub>0#Cs). P\<^sub>1 \<turnstile> C \<preceq>\<^sup>* D"
 and pcs: "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs sh I h' l' (sh(C\<^sub>0 \<mapsto> (sfs,Processing))) v xa (INIT C' (C\<^sub>0 # Cs,False) \<leftarrow> e)
    = (True, frs', (None, h', (vs, l, C, M, pc, Called []) # frs, sh'), err)"
shows
 "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs (sh(C\<^sub>0 \<mapsto> (sfs,Processing))) I h' l' sh'' v xa (INIT C' (D # C\<^sub>0 # Cs,False) \<leftarrow> e)
    = (True, calling_to_calling (hd frs') D#(tl frs'),
         (None, h', (vs, l, C, M, pc, Called []) # frs, sh''),
             \<exists>vs'. P \<turnstile> (None,h,calling_to_calling (hd frs') D#(tl frs'),sh')
                        -jvm\<rightarrow> handle P C M xa h' (vs'@vs) l pc ics frs sh'')"
proof -
  have "Jcc_cond P\<^sub>1 E C M vs pc ics I h sh (INIT C' (C\<^sub>0 # Cs,False) \<leftarrow> e)" using assms by simp
  then obtain T where "P\<^sub>1,E,h,sh \<turnstile>\<^sub>1 INIT C' (C\<^sub>0 # Cs,False) \<leftarrow> unit : T" by fastforce
  then have "P\<^sub>1,E,h,sh(C\<^sub>0 \<mapsto> (sfs,Processing)) \<turnstile>\<^sub>1 INIT C' (D # C\<^sub>0 # Cs,False) \<leftarrow> unit : T"
    using assms by clarsimp (auto simp: fun_upd_apply)
  then have wtrt: "Ex (WTrt2\<^sub>1 P\<^sub>1 E h (sh(C\<^sub>0 \<mapsto> (sfs,Processing))) (INIT C' (D # C\<^sub>0 # Cs,False) \<leftarrow> unit))"
    by(simp only: exI)
  show ?thesis using assms wtrt by clarsimp
qed

lemma Jcc_pieces_InitRInit:
assumes [simp]: "P \<equiv> compP\<^sub>2 P\<^sub>1" and wf: "wf_J\<^sub>1_prog P\<^sub>1"
 and "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs sh I h' l' sh' v xa (INIT C' (C\<^sub>0 # Cs,True) \<leftarrow> e)
    = (True, frs', (None, h', (vs, l, C, M, pc, Called []) # frs, sh'), err)"
shows
 "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs sh I h' l' sh' v xa (RI (C\<^sub>0,C\<^sub>0\<bullet>\<^sub>sclinit([])) ; Cs \<leftarrow> e)
    = (True, frs',
         (None, h', (vs, l, C, M, pc, Called []) # frs, sh'),
             \<exists>vs'. P \<turnstile> (None,h,frs',sh)
                        -jvm\<rightarrow> handle P C M xa h' (vs'@vs) l pc ics frs sh')"
proof -
  have cond: "Jcc_cond P\<^sub>1 E C M vs pc ics I h sh (INIT C' (C\<^sub>0 # Cs,True) \<leftarrow> e)" using assms by simp
  then have clinit: "\<exists>T. P\<^sub>1,E,h,sh \<turnstile>\<^sub>1 C\<^sub>0\<bullet>\<^sub>sclinit([]) : T" using wf
    by clarsimp (auto simp: is_class_def intro: wf\<^sub>1_types_clinit)
  then obtain T where cT: "P\<^sub>1,E,h,sh \<turnstile>\<^sub>1 C\<^sub>0\<bullet>\<^sub>sclinit([]) : T" by blast
  obtain T where "P\<^sub>1,E,h,sh \<turnstile>\<^sub>1 INIT C' (C\<^sub>0 # Cs,True) \<leftarrow> unit : T" using cond by fastforce
  then have "P\<^sub>1,E,h,sh \<turnstile>\<^sub>1 RI (C\<^sub>0,C\<^sub>0\<bullet>\<^sub>sclinit([])) ; Cs \<leftarrow> unit : T"
    using assms by (auto intro: cT)
  then have wtrt: "Ex (WTrt2\<^sub>1 P\<^sub>1 E h sh (RI (C\<^sub>0,C\<^sub>0\<bullet>\<^sub>sclinit([])) ; Cs \<leftarrow> unit))"
    by(simp only: exI)
  then show ?thesis using assms by simp
qed

lemma Jcc_pieces_RInit_clinit:
assumes [simp]: "P \<equiv> compP\<^sub>2 P\<^sub>1" and wf: "wf_J\<^sub>1_prog P\<^sub>1"
 and "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs sh I h\<^sub>1 l\<^sub>1 sh\<^sub>1 v xa (RI (C\<^sub>0,C\<^sub>0\<bullet>\<^sub>sclinit([]));Cs \<leftarrow> e)
    = (True, frs',
         (None, h\<^sub>1, (vs, l, C, M, pc, Called []) # frs, sh\<^sub>1), err)"
shows
 "Jcc_pieces P\<^sub>1 E C M h vs l pc (Called Cs) (tl frs') sh I h' l' sh' v xa (C\<^sub>0\<bullet>\<^sub>sclinit([]))
    = (True, create_init_frame P C\<^sub>0#(vs,l,C,M,pc,Called Cs)#tl frs',
         (None, h', (vs,l,C,M,pc,Called Cs)#tl frs', sh'(C\<^sub>0\<mapsto>(fst(the(sh' C\<^sub>0)),Done))),
             P \<turnstile> (None,h,create_init_frame P C\<^sub>0#(vs,l,C,M,pc,Called Cs)#tl frs',sh)
   -jvm\<rightarrow> (None,h',(vs, l, C, M, pc, Throwing Cs xa) # tl frs',sh'(C\<^sub>0 \<mapsto> (fst(the(sh' C\<^sub>0)),Error))))"
proof -
  have cond: "Jcc_cond P\<^sub>1 E C M vs pc ics I h sh (RI (C\<^sub>0,C\<^sub>0\<bullet>\<^sub>sclinit([]));Cs \<leftarrow> e)" using assms by simp
  then have wtrt: "\<exists>T. P\<^sub>1,E,h,sh \<turnstile>\<^sub>1 C\<^sub>0\<bullet>\<^sub>sclinit([]) : T" using wf
    by clarsimp (auto simp: is_class_def intro: wf\<^sub>1_types_clinit)
  then show ?thesis using assms by clarsimp
qed

lemma Jcc_pieces_RInit_Init:
assumes [simp]: "P \<equiv> compP\<^sub>2 P\<^sub>1" and wf: "wf_J\<^sub>1_prog P\<^sub>1"
 and proc: "\<forall>C' \<in> set Cs. \<exists>sfs. sh'' C' = \<lfloor>(sfs,Processing)\<rfloor>"
 and "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs sh I h\<^sub>1 l\<^sub>1 sh\<^sub>1 v xa (RI (C\<^sub>0,C\<^sub>0\<bullet>\<^sub>sclinit([]));Cs \<leftarrow> e)
    = (True, frs',
         (None, h\<^sub>1, (vs, l, C, M, pc, Called []) # frs, sh\<^sub>1), err)"
shows
 "Jcc_pieces P\<^sub>1 E C M h' vs l pc ics frs sh'' I h\<^sub>1 l\<^sub>1 sh\<^sub>1 v xa (INIT (last (C\<^sub>0#Cs)) (Cs,True) \<leftarrow> e)
    = (True, (vs, l, C, M, pc, Called Cs) # frs,
         (None, h\<^sub>1, (vs, l, C, M, pc, Called []) # frs, sh\<^sub>1),
             \<exists>vs'. P \<turnstile> (None,h',(vs, l, C, M, pc, Called Cs) # frs,sh'')
                        -jvm\<rightarrow> handle P C M xa h\<^sub>1 (vs'@vs) l pc ics frs sh\<^sub>1)"
proof -
  have "Jcc_cond P\<^sub>1 E C M vs pc ics I h sh (RI (C\<^sub>0,C\<^sub>0\<bullet>\<^sub>sclinit([]));Cs \<leftarrow> e)" using assms by simp
  then have "Ex (WTrt2\<^sub>1 P\<^sub>1 E h sh (RI (C\<^sub>0,C\<^sub>0\<bullet>\<^sub>sclinit([])) ; Cs \<leftarrow> unit))" by simp
  then obtain T where riwt: "P\<^sub>1,E,h,sh \<turnstile>\<^sub>1 RI (C\<^sub>0,C\<^sub>0\<bullet>\<^sub>sclinit([]));Cs \<leftarrow> unit : T" by meson
  then have "P\<^sub>1,E,h',sh'' \<turnstile>\<^sub>1 INIT (last (C\<^sub>0#Cs)) (Cs,True) \<leftarrow> unit : T" using proc
  proof(cases Cs) qed(auto)
  then have wtrt: "Ex (WTrt2\<^sub>1 P\<^sub>1 E h' sh'' (INIT (last (C\<^sub>0#Cs)) (Cs,True) \<leftarrow> unit))" by(simp only: exI)
  show ?thesis using assms wtrt
  proof(cases Cs)
    case (Cons C1 Cs1)
    then show ?thesis using assms wtrt
      by(case_tac "method P C1 clinit") clarsimp
  qed(clarsimp)
qed

lemma Jcc_pieces_RInit_RInit:
assumes [simp]: "P \<equiv> compP\<^sub>2 P\<^sub>1"
 and "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs sh I h\<^sub>1 l\<^sub>1 sh\<^sub>1 v xa (RI (C\<^sub>0,e);D#Cs \<leftarrow> e')
    = (True, frs', rhs, err)"
 and hd: "hd frs' = (vs1,l1,C1,M1,pc1,ics1)"
shows
 "Jcc_pieces P\<^sub>1 E C M h' vs l pc ics frs sh'' I h\<^sub>1 l\<^sub>1 sh\<^sub>1 v xa (RI (D,Throw xa) ; Cs \<leftarrow> e')
    = (True, (vs1, l1, C1, M1, pc1, Throwing (D#Cs) xa) # tl frs',
         (None, h\<^sub>1, (vs, l, C, M, pc, Called []) # frs, sh\<^sub>1),
             \<exists>vs'. P \<turnstile> (None,h',(vs1, l1, C1, M1, pc1, Throwing (D#Cs) xa) # tl frs',sh'')
                        -jvm\<rightarrow> handle P C M xa h\<^sub>1 (vs'@vs) l pc ics frs sh\<^sub>1)"
using assms by(case_tac "method P D clinit", cases "e = C\<^sub>0\<bullet>\<^sub>sclinit([])") clarsimp+


subsubsection "JVM stepping lemmas"

lemma jvm_Invoke:
assumes [simp]: "P \<equiv> compP\<^sub>2 P\<^sub>1"
 and "P,C,M,pc \<triangleright> Invoke M' (length Ts)"
 and ha: "h\<^sub>2 a = \<lfloor>(Ca, fs)\<rfloor>" and method: "P\<^sub>1 \<turnstile> Ca sees M', NonStatic :  Ts\<rightarrow>T = body in D"
 and len: "length pvs = length Ts" and "ls\<^sub>2' = Addr a # pvs @ replicate (max_vars body) undefined"
shows "P \<turnstile> (None, h\<^sub>2, (rev pvs @ Addr a # vs, ls\<^sub>2, C, M, pc, No_ics) # frs, sh\<^sub>2) -jvm\<rightarrow>
    (None, h\<^sub>2, ([], ls\<^sub>2', D, M', 0, No_ics) # (rev pvs @ Addr a # vs, ls\<^sub>2, C, M, pc, No_ics) # frs, sh\<^sub>2)"
proof -
  have cname: "cname_of h\<^sub>2 (the_Addr ((rev pvs @ Addr a # vs) ! length Ts)) = Ca"
    using ha method len by(auto simp: nth_append)
  have r: "(rev pvs @ Addr a # vs) ! (length Ts) = Addr a" using len by(auto simp: nth_append)
  have exm: "\<exists>Ts T m D b. P \<turnstile> Ca sees M',b:Ts \<rightarrow> T = m in D"
    using sees_method_compP[OF method] by fastforce
  show ?thesis using assms cname r exm by simp
qed

lemma jvm_Invokestatic:
assumes [simp]: "P \<equiv> compP\<^sub>2 P\<^sub>1"
 and "P,C,M,pc \<triangleright> Invokestatic C' M' (length Ts)"
 and sh: "sh\<^sub>2 D = Some(sfs,Done)"
 and method: "P\<^sub>1 \<turnstile> C' sees M', Static :  Ts\<rightarrow>T = body in D"
 and len: "length pvs = length Ts" and "ls\<^sub>2' = pvs @ replicate (max_vars body) undefined"
shows "P \<turnstile> (None, h\<^sub>2, (rev pvs @ vs, ls\<^sub>2, C, M, pc, No_ics) # frs, sh\<^sub>2) -jvm\<rightarrow>
    (None, h\<^sub>2, ([], ls\<^sub>2', D, M', 0, No_ics) # (rev pvs @ vs, ls\<^sub>2, C, M, pc, No_ics) # frs, sh\<^sub>2)"
proof -
  have exm: "\<exists>Ts T m D b. P \<turnstile> C' sees M',b:Ts \<rightarrow> T = m in D"
    using sees_method_compP[OF method] by fastforce
  show ?thesis using assms exm by simp
qed

lemma jvm_Invokestatic_Called:
assumes [simp]: "P \<equiv> compP\<^sub>2 P\<^sub>1"                       
 and "P,C,M,pc \<triangleright> Invokestatic C' M' (length Ts)"
 and sh: "sh\<^sub>2 D = Some(sfs,i)"
 and method: "P\<^sub>1 \<turnstile> C' sees M', Static :  Ts\<rightarrow>T = body in D"
 and len: "length pvs = length Ts" and "ls\<^sub>2' = pvs @ replicate (max_vars body) undefined"
shows "P \<turnstile> (None, h\<^sub>2, (rev pvs @ vs, ls\<^sub>2, C, M, pc, Called []) # frs, sh\<^sub>2) -jvm\<rightarrow>
    (None, h\<^sub>2, ([], ls\<^sub>2', D, M', 0, No_ics) # (rev pvs @ vs, ls\<^sub>2, C, M, pc, No_ics) # frs, sh\<^sub>2)"
proof -
  have exm: "\<exists>Ts T m D b. P \<turnstile> C' sees M',b:Ts \<rightarrow> T = m in D"
    using sees_method_compP[OF method] by fastforce
  show ?thesis using assms exm by simp
qed

lemma jvm_Return_Init:
"P,D,clinit,0 \<rhd> compE\<^sub>2 body @ [Return]
  \<Longrightarrow> P \<turnstile> (None, h, (vs, ls, D, clinit, size(compE\<^sub>2 body), No_ics) # frs, sh)
              -jvm\<rightarrow> (None, h, frs, sh(D\<mapsto>(fst(the(sh D)),Done)))"
apply(simp add: exec_all_def1, rule r_into_rtrancl, rule exec_1I)
apply(cases frs, auto)
done

lemma jvm_InitNone:
 "\<lbrakk> ics_of f = Calling C Cs;
    sh C = None \<rbrakk>
  \<Longrightarrow> P \<turnstile> (None,h,f#frs,sh) -jvm\<rightarrow> (None,h,f#frs,sh(C \<mapsto> (sblank P C, Prepared)))"
apply(simp add: exec_all_def1, rule r_into_rtrancl, rule exec_1I)
apply(cases f) apply(rename_tac ics, case_tac ics, simp_all)
done

lemma jvm_InitDP:
 "\<lbrakk> ics_of f = Calling C Cs;
    sh C = \<lfloor>(sfs,i)\<rfloor>; i = Done \<or> i = Processing \<rbrakk>
  \<Longrightarrow> P \<turnstile> (None,h,f#frs,sh) -jvm\<rightarrow> (None,h,(calling_to_scalled f)#frs,sh)"
apply(simp add: exec_all_def1, rule r_into_rtrancl, rule exec_1I)
apply(cases f)
apply(erule_tac P = "i = Done" in disjE)
 apply simp_all
done

lemma jvm_InitError:
 "sh C = \<lfloor>(sfs,Error)\<rfloor>
  \<Longrightarrow> P \<turnstile> (None,h,(vs,ls,C\<^sub>0,M,pc,Calling C Cs)#frs,sh)
   -jvm\<rightarrow> (None,h,(vs,ls,C\<^sub>0,M,pc,Throwing Cs (addr_of_sys_xcpt NoClassDefFoundError))#frs,sh)"
 by(clarsimp simp: exec_all_def1 intro!: r_into_rtrancl exec_1I)

lemma exec_ErrorThrowing:
 "sh C = \<lfloor>(sfs,Error)\<rfloor>
  \<Longrightarrow> exec (P, (None,h,calling_to_throwing (stk,loc,D,M,pc,Calling C Cs) a#frs,sh))
   = Some (None,h,calling_to_sthrowing (stk,loc,D,M,pc,Calling C Cs) a #frs,sh)"
 by(clarsimp simp: exec_all_def1 fun_upd_idem_iff intro!: r_into_rtrancl exec_1I)

lemma jvm_InitObj:
 "\<lbrakk> sh C = Some(sfs,Prepared);
     C = Object;
     sh' = sh(C \<mapsto> (sfs,Processing)) \<rbrakk>
\<Longrightarrow> P \<turnstile> (None, h, (vs,ls,C\<^sub>0,M,pc,Calling C Cs)#frs, sh) -jvm\<rightarrow>
    (None, h, (vs,ls,C\<^sub>0,M,pc,Called (C#Cs))#frs,sh')"
apply(simp add: exec_all_def1, rule r_into_rtrancl, rule exec_1I)
apply(case_tac "method P C clinit", simp)
done

lemma jvm_InitNonObj:
 "\<lbrakk> sh C = Some(sfs,Prepared);
     C \<noteq> Object;
     class P C = Some (D,r);
     sh' = sh(C \<mapsto> (sfs,Processing)) \<rbrakk>
\<Longrightarrow> P \<turnstile> (None, h, (vs,ls,C\<^sub>0,M,pc,Calling C Cs)#frs, sh) -jvm\<rightarrow>
    (None, h, (vs,ls,C\<^sub>0,M,pc,Calling D (C#Cs))#frs, sh')"
apply(simp add: exec_all_def1, rule r_into_rtrancl, rule exec_1I)
apply(case_tac "method P C clinit", simp)
done

lemma jvm_RInit_throw:
 "P \<turnstile> (None,h,(vs,l,C,M,pc,Throwing [] xa) # frs,sh)
        -jvm\<rightarrow> handle P C M xa h vs l pc No_ics frs sh"
apply(simp add: exec_all_def1, rule r_into_rtrancl, rule exec_1I)
apply(simp add: handle_def split: bool.splits)
done

lemma jvm_RInit_throw':
 "P \<turnstile> (None,h,(vs,l,C,M,pc,Throwing [C'] xa) # frs,sh)
        -jvm\<rightarrow> handle P C M xa h vs l pc No_ics frs (sh(C':=Some(fst(the(sh C')), Error)))"
apply(simp add: exec_all_def1)
apply(rule_tac y = "(None,h,(vs,l,C,M,pc,Throwing [] xa) # frs,sh(C':=Some(fst(the(sh C')), Error)))" in rtrancl_trans)
 apply(rule r_into_rtrancl, rule exec_1I)
 apply(simp add: handle_def)
apply(cut_tac jvm_RInit_throw)
apply(simp add: exec_all_def1)
done

lemma jvm_Called:
 "P \<turnstile> (None, h, (vs, l, C, M, pc, Called (C\<^sub>0 # Cs)) # frs, sh) -jvm\<rightarrow>
    (None, h, create_init_frame P C\<^sub>0 # (vs, l, C, M, pc, Called Cs) # frs, sh)"
 by(simp add: exec_all_def1 r_into_rtrancl exec_1I)

lemma jvm_Throwing:
 "P \<turnstile> (None, h, (vs, l, C, M, pc, Throwing (C\<^sub>0#Cs) xa') # frs, sh) -jvm\<rightarrow>
    (None, h, (vs, l, C, M, pc, Throwing Cs xa') # frs, sh(C\<^sub>0 \<mapsto> (fst (the (sh C\<^sub>0)), Error)))"
 by(simp add: exec_all_def1 r_into_rtrancl exec_1I)

subsubsection "Other lemmas for correctness proof"

lemma assumes wf:"wf_prog wf_md P"
 and ex: "class P C = Some a"
shows create_init_frame_wf_eq: "create_init_frame (compP\<^sub>2 P) C = (stk,loc,D,M,pc,ics) \<Longrightarrow> D=C"
using wf_sees_clinit[OF wf ex] by(cases "method P C clinit", auto)

lemma beforex_try:
 "\<lbrakk> {pc..<pc+size(compE\<^sub>2(try e\<^sub>1 catch(Ci i) e\<^sub>2))} \<subseteq> I;
    P,C,M \<rhd> compxE\<^sub>2 (try e\<^sub>1 catch(Ci i) e\<^sub>2) pc (size vs) / I,size vs \<rbrakk>
   \<Longrightarrow> P,C,M \<rhd> compxE\<^sub>2 e\<^sub>1 pc (size vs) / {pc..<pc + length (compE\<^sub>2 e\<^sub>1)},size vs"
apply(clarsimp simp:beforex_def split:if_split_asm)
apply(rename_tac xt\<^sub>0 xt\<^sub>1) apply(rule_tac x=xt\<^sub>0 in exI)
apply(auto simp: pcs_subset(1))
using atLeastLessThan_iff by blast

\<comment> \<open> Evaluation of initialization expressions \<close>

(* --needs J1 and EConform; version for eval found in Equivalence *)
lemma
shows eval\<^sub>1_init_return: "P \<turnstile>\<^sub>1 \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>
  \<Longrightarrow> iconf (shp\<^sub>1 s) e
  \<Longrightarrow> (\<exists>Cs b. e = INIT C' (Cs,b) \<leftarrow> unit) \<or> (\<exists>C e\<^sub>0 Cs e\<^sub>i. e = RI(C,e\<^sub>0);Cs@[C'] \<leftarrow> unit)
     \<or> (\<exists>e\<^sub>0. e = RI(C',e\<^sub>0);Nil \<leftarrow> unit)
  \<Longrightarrow> (val_of e' = Some v \<longrightarrow> (\<exists>sfs i. shp\<^sub>1 s' C' = \<lfloor>(sfs,i)\<rfloor> \<and> (i = Done \<or> i = Processing)))
   \<and> (throw_of e' = Some a \<longrightarrow> (\<exists>sfs i. shp\<^sub>1 s' C' = \<lfloor>(sfs,Error)\<rfloor>))"
and "P \<turnstile>\<^sub>1 \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow> True"
proof(induct rule: eval\<^sub>1_evals\<^sub>1.inducts)
  case (InitFinal\<^sub>1 e s e' s' C b) then show ?case
    by(auto simp: initPD_def dest: eval\<^sub>1_final_same)
next
  case (InitDone\<^sub>1 sh C sfs C' Cs e h l e' s')
  then have "final e'" using eval\<^sub>1_final by simp
  then show ?case
  proof(rule finalE)
    fix v assume e': "e' = Val v" then show ?thesis using InitDone\<^sub>1 initPD_def
    proof(cases Cs) qed(auto)
  next
    fix a assume e': "e' = throw a" then show ?thesis using InitDone\<^sub>1 initPD_def
    proof(cases Cs) qed(auto)
  qed
next
  case (InitProcessing\<^sub>1 sh C sfs C' Cs e h l e' s')
  then have "final e'" using eval\<^sub>1_final by simp
  then show ?case
  proof(rule finalE)
    fix v assume e': "e' = Val v" then show ?thesis using InitProcessing\<^sub>1 initPD_def
    proof(cases Cs) qed(auto)
  next
    fix a assume e': "e' = throw a" then show ?thesis using InitProcessing\<^sub>1 initPD_def
    proof(cases Cs) qed(auto)
  qed
next
  case (InitError\<^sub>1 sh C sfs Cs e h l e' s' C') show ?case
  proof(cases Cs)
    case Nil then show ?thesis using InitError\<^sub>1 by simp
  next
    case (Cons C2 list)
    then have "final e'" using InitError\<^sub>1 eval\<^sub>1_final by simp
    then show ?thesis
    proof(rule finalE)
      fix v assume e': "e' = Val v" show ?thesis
        using InitError\<^sub>1.hyps(2) e' rinit\<^sub>1_throwE by blast
    next
      fix a assume e': "e' = throw a"
      then show ?thesis using Cons InitError\<^sub>1 cons_to_append[of list] by clarsimp
    qed
  qed
next
  case (InitRInit\<^sub>1 C Cs h l sh e' s' C') show ?case
  proof(cases Cs)
    case Nil then show ?thesis using InitRInit\<^sub>1 by simp
  next
    case (Cons C' list) then show ?thesis
      using InitRInit\<^sub>1 Cons cons_to_append[of list] by clarsimp
  qed
next
  case (RInit\<^sub>1 e s v h' l' sh' C sfs i sh'' C' Cs e' e\<^sub>1 s\<^sub>1)
  then have final: "final e\<^sub>1" using eval\<^sub>1_final by simp
  then show ?case
  proof(cases Cs)
    case Nil show ?thesis using final
    proof(rule finalE)
      fix v assume e': "e\<^sub>1 = Val v" show ?thesis
      using RInit\<^sub>1 Nil by(clarsimp, meson fun_upd_same initPD_def)
    next
      fix a assume e': "e\<^sub>1 = throw a" show ?thesis
      using RInit\<^sub>1 Nil by(clarsimp, meson fun_upd_same initPD_def)
    qed
  next
    case (Cons a list) show ?thesis using final
    proof(rule finalE)
      fix v assume e': "e\<^sub>1 = Val v" then show ?thesis
      using RInit\<^sub>1 Cons by(clarsimp, metis last.simps last_appendR list.distinct(1))
    next
      fix a assume e': "e\<^sub>1 = throw a" then show ?thesis
      using RInit\<^sub>1 Cons by(clarsimp, metis last.simps last_appendR list.distinct(1))
    qed
  qed
next
  case (RInitInitFail\<^sub>1 e s a h' l' sh' C sfs i sh'' D Cs e' e\<^sub>1 s\<^sub>1)
  then have final: "final e\<^sub>1" using eval\<^sub>1_final by simp
  then show ?case
  proof(rule finalE)
    fix v assume e': "e\<^sub>1 = Val v" then show ?thesis
    using RInitInitFail\<^sub>1 by(clarsimp, meson exp.distinct(101) rinit\<^sub>1_throwE)
  next
    fix a' assume e': "e\<^sub>1 = Throw a'"
    then have "iconf (sh'(C \<mapsto> (sfs, Error))) a"
      using RInitInitFail\<^sub>1.hyps(1) eval\<^sub>1_final by fastforce
    then show ?thesis using RInitInitFail\<^sub>1 e'
      by(clarsimp, meson Cons_eq_append_conv list.inject)
  qed
qed(auto simp: fun_upd_same)

lemma init\<^sub>1_Val_PD: "P \<turnstile>\<^sub>1 \<langle>INIT C' (Cs,b) \<leftarrow> unit,s\<rangle> \<Rightarrow> \<langle>Val v,s'\<rangle>
  \<Longrightarrow> iconf (shp\<^sub>1 s) (INIT C' (Cs,b) \<leftarrow> unit)
  \<Longrightarrow> \<exists>sfs i. shp\<^sub>1 s' C' = \<lfloor>(sfs,i)\<rfloor> \<and> (i = Done \<or> i = Processing)"
 by(drule_tac v = v in eval\<^sub>1_init_return, simp+)

lemma init\<^sub>1_throw_PD: "P \<turnstile>\<^sub>1 \<langle>INIT C' (Cs,b) \<leftarrow> unit,s\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle>
  \<Longrightarrow> iconf (shp\<^sub>1 s) (INIT C' (Cs,b) \<leftarrow> unit)
  \<Longrightarrow> \<exists>sfs i. shp\<^sub>1 s' C' = \<lfloor>(sfs,Error)\<rfloor>"
 by(drule_tac a = a in eval\<^sub>1_init_return, simp+)

lemma rinit\<^sub>1_Val_PD: "P \<turnstile>\<^sub>1 \<langle>RI(C,e\<^sub>0);Cs \<leftarrow> unit,s\<rangle> \<Rightarrow> \<langle>Val v,s'\<rangle>
  \<Longrightarrow> iconf (shp\<^sub>1 s) (RI(C,e\<^sub>0);Cs \<leftarrow> unit) \<Longrightarrow> last(C#Cs) = C'
  \<Longrightarrow> \<exists>sfs i. shp\<^sub>1 s' C' = \<lfloor>(sfs,i)\<rfloor> \<and> (i = Done \<or> i = Processing)"
apply(drule_tac C' = C' and v = v in eval\<^sub>1_init_return, simp_all)
apply (metis append_butlast_last_id)
done

lemma rinit\<^sub>1_throw_PD: "P \<turnstile>\<^sub>1 \<langle>RI(C,e\<^sub>0);Cs \<leftarrow> unit,s\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle>
  \<Longrightarrow> iconf (shp\<^sub>1 s) (RI(C,e\<^sub>0);Cs \<leftarrow> unit) \<Longrightarrow> last(C#Cs) = C'
  \<Longrightarrow> \<exists>sfs i. shp\<^sub>1 s' C' = \<lfloor>(sfs,Error)\<rfloor>"
apply(drule_tac C' = C' and a = a in eval\<^sub>1_init_return, simp_all)
apply (metis append_butlast_last_id)
done

subsubsection "The proof"

lemma fixes P\<^sub>1 defines [simp]: "P \<equiv> compP\<^sub>2 P\<^sub>1"
assumes wf: "wf_J\<^sub>1_prog P\<^sub>1"
shows Jcc: "P\<^sub>1 \<turnstile>\<^sub>1 \<langle>e,(h\<^sub>0,ls\<^sub>0,sh\<^sub>0)\<rangle> \<Rightarrow> \<langle>ef,(h\<^sub>1,ls\<^sub>1,sh\<^sub>1)\<rangle> \<Longrightarrow>
  (\<And>E C M pc ics v xa vs frs I.
     \<lbrakk> Jcc_cond P\<^sub>1 E C M vs pc ics I h\<^sub>0 sh\<^sub>0 e \<rbrakk> \<Longrightarrow>
     (ef = Val v \<longrightarrow>
         P \<turnstile> (None,h\<^sub>0,Jcc_frames P C M vs ls\<^sub>0 pc ics frs e,sh\<^sub>0)
                -jvm\<rightarrow> Jcc_rhs P\<^sub>1 E C M vs ls\<^sub>0 pc ics frs h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v e)
     \<and>
     (ef = Throw xa \<longrightarrow> Jcc_err P C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>1 ls\<^sub>1 sh\<^sub>1 xa e)
  )"
(*<*)
  (is "_ \<Longrightarrow> (\<And>E C M pc ics v xa vs frs I.
                  PROP ?P e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 ef h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics v xa vs frs I)")
(*>*)
and "P\<^sub>1 \<turnstile>\<^sub>1 \<langle>es,(h\<^sub>0,ls\<^sub>0,sh\<^sub>0)\<rangle> [\<Rightarrow>] \<langle>fs,(h\<^sub>1,ls\<^sub>1,sh\<^sub>1)\<rangle> \<Longrightarrow>
    (\<And>C M pc ics ws xa es' vs frs I.
      \<lbrakk> P,C,M,pc \<rhd> compEs\<^sub>2 es; P,C,M \<rhd> compxEs\<^sub>2 es pc (size vs)/I,size vs;
       {pc..<pc+size(compEs\<^sub>2 es)} \<subseteq> I; ics = No_ics;
       \<not>sub_RIs es \<rbrakk> \<Longrightarrow>
      (fs = map Val ws \<longrightarrow>
       P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc,ics)#frs,sh\<^sub>0) -jvm\<rightarrow>
             (None,h\<^sub>1,(rev ws @ vs,ls\<^sub>1,C,M,pc+size(compEs\<^sub>2 es),ics)#frs,sh\<^sub>1))
      \<and>
      (fs = map Val ws @ Throw xa # es' \<longrightarrow>
       (\<exists>pc\<^sub>1. pc \<le> pc\<^sub>1 \<and> pc\<^sub>1 < pc + size(compEs\<^sub>2 es) \<and>
                \<not> caught P pc\<^sub>1 h\<^sub>1 xa (compxEs\<^sub>2 es pc (size vs)) \<and>
                (\<exists>vs'. P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc,ics)#frs,sh\<^sub>0)
                                     -jvm\<rightarrow> handle P C M xa h\<^sub>1 (vs'@vs) ls\<^sub>1 pc\<^sub>1 ics frs sh\<^sub>1))))"
(*<*)
  (is "_ \<Longrightarrow> (\<And>C M pc ics ws xa es' vs frs I.
                  PROP ?Ps es h\<^sub>0 ls\<^sub>0 sh\<^sub>0 fs h\<^sub>1 ls\<^sub>1 sh\<^sub>1 C M pc ics ws xa es' vs frs I)")
proof (induct rule:eval\<^sub>1_evals\<^sub>1_inducts)
  case New\<^sub>1 thus ?case by auto
next
  case (NewFail\<^sub>1 sh C' sfs h ls)
  let ?xa = "addr_of_sys_xcpt OutOfMemory"
  have "P \<turnstile> (None,h,(vs,ls,C,M,pc,ics)#frs,sh) -jvm\<rightarrow> handle P C M ?xa h vs ls pc ics frs sh"
    using NewFail\<^sub>1 by(clarsimp simp: handle_def)
  then show ?case by(auto intro!: exI[where x="[]"])
next
  case (NewInit\<^sub>1 sh C' h ls v' h' ls' sh' a FDTs h'')
  then obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h vs ls pc ics frs sh I h' ls' sh' v xa (new C')
    = (True, frs', (None,h',(v#vs,ls',C,M,pc+size(compE\<^sub>2 (new C')),ics)#frs,sh'), err)"
    using NewInit\<^sub>1.prems(1) by clarsimp
  have "Ex (WTrt2\<^sub>1 P\<^sub>1 E h sh (INIT C' ([C'],False) \<leftarrow> unit))"
    using has_fields_is_class[OF NewInit\<^sub>1.hyps(5)] by auto
  then obtain err' where pcs':
    "Jcc_pieces P\<^sub>1 E C M h vs ls pc ics frs sh I h' ls' sh' v' xa (INIT C' ([C'],False) \<leftarrow> unit)
    = (True, (vs,ls,C,M,pc,Calling C' []) # frs, (None,h',(vs,ls,C,M,pc,Called [])#frs,sh'), err')"
    using NewInit\<^sub>1.prems(1) by auto
  have IH: "PROP ?P (INIT C' ([C'],False) \<leftarrow> unit) h ls sh (Val v')
             h' ls' sh' E C M pc ics v' xa vs frs I" by fact
  have ls: "ls = ls'" by(rule init\<^sub>1_same_loc[OF NewInit\<^sub>1.hyps(2)])
  obtain sfs i where sh': "sh' C' = Some(sfs,i)"
    using init\<^sub>1_Val_PD[OF NewInit\<^sub>1.hyps(2)] by clarsimp
  have "P \<turnstile> (None,h,(vs,ls,C,M,pc,ics)#frs,sh) -jvm\<rightarrow> (None,h,(vs,ls,C,M,pc,Calling C' [])#frs,sh)"
  proof(cases "sh C'")
    case None then show ?thesis using NewInit\<^sub>1.prems by(cases ics) auto
  next
    case (Some a)
    then obtain sfs i where "a = (sfs,i)" by(cases a)
    then show ?thesis using NewInit\<^sub>1.hyps(1) NewInit\<^sub>1.prems Some
      by(cases ics; case_tac i) auto
  qed
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None, h', (vs, ls, C, M, pc, Called []) # frs, sh')"
    using IH pcs' by auto
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None, h'', (Addr a#vs, ls, C, M, Suc pc, ics) # frs, sh')"
    using NewInit\<^sub>1.hyps(1,2,4-6) NewInit\<^sub>1.prems sh' by(cases ics) auto
  finally show ?case using pcs ls by clarsimp
next
  case (NewInitOOM\<^sub>1 sh C' h ls v' h' ls' sh')
  let ?xa = "addr_of_sys_xcpt OutOfMemory"
  obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h vs ls pc ics frs sh I h' ls' sh' v xa (new C')
    = (True, frs', (None,h',(v#vs,ls',C,M,pc+size(compE\<^sub>2 (new C')),ics)#frs,sh'), err)"
    using NewInitOOM\<^sub>1.prems(1) by clarsimp
  have "Ex (WTrt2\<^sub>1 P\<^sub>1 E h sh (INIT C' ([C'],False) \<leftarrow> unit))" using NewInitOOM\<^sub>1.hyps(5) by auto
  then obtain err' where pcs':
    "Jcc_pieces P\<^sub>1 E C M h vs ls pc ics frs sh I h' ls' sh' v' xa (INIT C' ([C'],False) \<leftarrow> unit)
    = (True, (vs,ls,C,M,pc,Calling C' []) # frs, (None,h',(vs,ls,C,M,pc,Called [])#frs,sh'), err')"
    using NewInitOOM\<^sub>1.prems(1) by auto
  have IH: "PROP ?P (INIT C' ([C'],False) \<leftarrow> unit) h ls sh (Val v')
             h' ls' sh' E C M pc ics v' xa vs frs I" by fact
  have ls: "ls = ls'" by(rule init\<^sub>1_same_loc[OF NewInitOOM\<^sub>1.hyps(2)])
  have "iconf (shp\<^sub>1 (h, ls, sh)) (INIT C' ([C'],False) \<leftarrow> unit)" by simp
  then obtain sfs i where sh': "sh' C' = Some(sfs,i)"
    using init\<^sub>1_Val_PD[OF NewInitOOM\<^sub>1.hyps(2)] by clarsimp
  have "P \<turnstile> (None,h,(vs,ls,C,M,pc,ics)#frs,sh) -jvm\<rightarrow> (None,h,(vs,ls,C,M,pc,Calling C' [])#frs,sh)"
  proof(cases "sh C'")
    case None then show ?thesis using NewInitOOM\<^sub>1.prems by(cases ics) auto
  next
    case (Some a)
    then obtain sfs i where "a = (sfs,i)" by(cases a)
    then show ?thesis using NewInitOOM\<^sub>1.hyps(1) NewInitOOM\<^sub>1.prems Some
      by(cases ics; case_tac i) auto
  qed
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None, h', (vs, ls, C, M, pc, Called []) # frs, sh')"
    using IH pcs' by auto
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M ?xa h' vs ls pc ics frs sh'"
    using NewInitOOM\<^sub>1.hyps(1,2,4,5) NewInitOOM\<^sub>1.prems sh' by(auto simp: handle_def)
  finally show ?case using pcs ls by(simp, metis (no_types) append_Nil le_refl lessI)
next
  case (NewInitThrow\<^sub>1 sh C' h ls a h' ls' sh')
  obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h vs ls pc ics frs sh I h' ls' sh' v xa (new C')
    = (True, frs', (None,h',(v#vs,ls',C,M,pc+size(compE\<^sub>2 (new C')),ics)#frs,sh'), err)"
    using NewInitThrow\<^sub>1.prems(1) by clarsimp
  obtain a' where throw: "throw a = Throw a'" using eval\<^sub>1_final[OF NewInitThrow\<^sub>1.hyps(2)] by clarsimp
  have "Ex (WTrt2\<^sub>1 P\<^sub>1 E h sh (INIT C' ([C'],False) \<leftarrow> unit))" using NewInitThrow\<^sub>1.hyps(4) by auto
  then obtain vs' where pcs':
    "Jcc_pieces P\<^sub>1 E C M h vs ls pc ics frs sh I h' ls' sh' v a' (INIT C' ([C'],False) \<leftarrow> unit)
    = (True, (vs,ls,C,M,pc,Calling C' []) # frs, (None,h',(vs,ls,C,M,pc,Called [])#frs,sh'),
        P \<turnstile> (None,h,(vs,ls,C,M,pc,Calling C' []) # frs,sh)
               -jvm\<rightarrow> handle P C M a' h' (vs'@vs) ls pc ics frs sh')"
    using NewInitThrow\<^sub>1.prems(1) by simp blast
  have IH: "PROP ?P (INIT C' ([C'],False) \<leftarrow> unit) h ls sh (throw a)
             h' ls' sh' E C M pc ics v a' vs frs I" by fact
  have ls: "ls = ls'" by(rule init\<^sub>1_same_loc[OF NewInitThrow\<^sub>1.hyps(2)])
  then have "P \<turnstile> (None,h,(vs,ls,C,M,pc,ics)#frs,sh) -jvm\<rightarrow> (None,h,(vs,ls,C,M,pc,Calling C' []) # frs,sh)"
  proof(cases "sh C'")
    case None then show ?thesis using NewInitThrow\<^sub>1.prems by(cases ics) auto
  next
    case (Some a)
    then obtain sfs i where "a = (sfs,i)" by(cases a)
    then show ?thesis using NewInitThrow\<^sub>1.hyps(1) NewInitThrow\<^sub>1.prems Some
      by(cases ics; case_tac i) auto
  qed
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M a' h' (vs'@vs) ls pc ics frs sh'" using IH pcs' throw by auto
  finally show ?case using throw ls by auto
next
  case (Cast\<^sub>1 e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 a h\<^sub>1 ls\<^sub>1 sh\<^sub>1 D fs C')
  let ?pc = "pc + length(compE\<^sub>2 e)"
  obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v xa (Cast C' e)
    = (True, frs', (None,h\<^sub>1,(v#vs,ls\<^sub>1,C,M,pc+size(compE\<^sub>2 (Cast C' e)),ics)#frs,sh\<^sub>1), err)"
    using Cast\<^sub>1.prems(1) by auto
  have IH: "PROP ?P e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (addr a) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics (Addr a) xa vs frs I" by fact
  then have "P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc,ics)#frs,sh\<^sub>0) -jvm\<rightarrow>
             (None,h\<^sub>1,(Addr a#vs,ls\<^sub>1,C,M,?pc,ics)#frs,sh\<^sub>1)"
    using Jcc_pieces_Cast[OF assms(1) pcs, of "Addr a"] Cast\<^sub>1.prems pcs by auto
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>1,(Addr a#vs,ls\<^sub>1,C,M,?pc+1,ics)#frs,sh\<^sub>1)"
    using Cast\<^sub>1 by (auto simp add:cast_ok_def)
  finally show ?case by auto
next
  case (CastNull\<^sub>1 e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 h\<^sub>1 ls\<^sub>1 sh\<^sub>1 C')
  let ?pc = "pc + length(compE\<^sub>2 e)"
  obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v xa (Cast C' e)
    = (True, frs', (None,h\<^sub>1,(v#vs,ls\<^sub>1,C,M,pc+size(compE\<^sub>2 (Cast C' e)),ics)#frs,sh\<^sub>1), err)"
    using CastNull\<^sub>1.prems(1) by clarsimp
  have IH: "PROP ?P e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 null h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics Null xa vs frs I" by fact
  then have "P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc,ics)#frs,sh\<^sub>0) -jvm\<rightarrow>
             (None,h\<^sub>1,(Null#vs,ls\<^sub>1,C,M,?pc,ics)#frs,sh\<^sub>1)"
    using Jcc_pieces_Cast[OF assms(1) pcs, of Null] CastNull\<^sub>1.prems pcs by auto
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>1,(Null#vs,ls\<^sub>1,C,M,?pc+1,ics)#frs,sh\<^sub>1)"
    using CastNull\<^sub>1 by (auto simp add:cast_ok_def)
  finally show ?case by auto
next
  case (CastFail\<^sub>1 e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 a h\<^sub>1 ls\<^sub>1 sh\<^sub>1 D fs C')
  let ?pc = "pc + length(compE\<^sub>2 e)"
  let ?xa = "addr_of_sys_xcpt ClassCast"
  obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v xa (Cast C' e)
    = (True, frs', (None,h\<^sub>1,(v#vs,ls\<^sub>1,C,M,pc+size(compE\<^sub>2 (Cast C' e)),ics)#frs,sh\<^sub>1), err)"
    using CastFail\<^sub>1.prems(1) by clarsimp
  have IH: "PROP ?P e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (addr a) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics (Addr a) xa vs frs I" by fact
  then have "P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc,ics)#frs,sh\<^sub>0) -jvm\<rightarrow>
             (None,h\<^sub>1,(Addr a#vs,ls\<^sub>1,C,M,?pc,ics)#frs,sh\<^sub>1)"
    using Jcc_pieces_Cast[OF assms(1) pcs, of "Addr a"] CastFail\<^sub>1.prems pcs by auto
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M ?xa h\<^sub>1 (Addr a#vs) ls\<^sub>1 ?pc ics frs sh\<^sub>1"
    using CastFail\<^sub>1 by (auto simp add:handle_def cast_ok_def)
  finally have exec: "P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc,ics)#frs,sh\<^sub>0) -jvm\<rightarrow> \<dots>".
  show ?case (is "?N \<and> (?eq \<longrightarrow> ?err)")
  proof
    show ?N by simp
  next
    { assume ?eq
      then have ?err using exec by (auto intro!: exI[where x="?pc"] exI[where x="[Addr a]"])
    }
    thus "?eq \<longrightarrow> ?err" by simp
  qed
next
  case (CastThrow\<^sub>1 e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 e' h\<^sub>1 ls\<^sub>1 sh\<^sub>1 C')
  obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v xa (Cast C' e)
    = (True, frs', (None,h\<^sub>1,(v#vs,ls\<^sub>1,C,M,pc+size(compE\<^sub>2 (Cast C' e)),ics)#frs,sh\<^sub>1), err)"
    using CastThrow\<^sub>1.prems(1) by clarsimp
  have IH: "PROP ?P e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (throw e') h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics v xa vs frs I" by fact
  show ?case using IH Jcc_pieces_Cast[OF assms(1) pcs, of v] CastThrow\<^sub>1.prems pcs less_SucI
   by(simp, blast)
next
  case Val\<^sub>1 thus ?case by auto
next
  case Var\<^sub>1 thus ?case by auto
next
  case (BinOp\<^sub>1 e\<^sub>1 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 v\<^sub>1 h\<^sub>1 ls\<^sub>1 sh\<^sub>1 e\<^sub>2 v\<^sub>2 h\<^sub>2 ls\<^sub>2 sh\<^sub>2 bop w)
  obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>2 ls\<^sub>2 sh\<^sub>2 v xa (e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2)
    = (True, frs', (None,h\<^sub>2,(v#vs,ls\<^sub>2,C,M,pc+size(compE\<^sub>2 (e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2)),ics)#frs,sh\<^sub>2), err)"
    using BinOp\<^sub>1.prems(1) by clarsimp
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e\<^sub>1)"
  let ?pc\<^sub>2 = "?pc\<^sub>1 + length(compE\<^sub>2 e\<^sub>2)"
  have IH\<^sub>1: "PROP ?P e\<^sub>1 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (Val v\<^sub>1) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics v\<^sub>1 xa vs frs
                     (I - pcs (compxE\<^sub>2 e\<^sub>2 (pc + length (compE\<^sub>2 e\<^sub>1)) (Suc (length vs))))" by fact
  have IH\<^sub>2: "PROP ?P e\<^sub>2 h\<^sub>1 ls\<^sub>1 sh\<^sub>1 (Val v\<^sub>2) h\<^sub>2 ls\<^sub>2 sh\<^sub>2 E C M ?pc\<^sub>1 ics v\<^sub>2 xa (v\<^sub>1#vs) frs
                     (I - pcs(compxE\<^sub>2 e\<^sub>1 pc (size vs)))" by fact
  have "P \<turnstile> (None,h\<^sub>0,frs',sh\<^sub>0) -jvm\<rightarrow> (None,h\<^sub>1,(v\<^sub>1#vs,ls\<^sub>1,C,M,?pc\<^sub>1,ics)#frs,sh\<^sub>1)"
    using IH\<^sub>1 Jcc_pieces_BinOp1[OF pcs, of h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v\<^sub>1] by simp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>2,(v\<^sub>2#v\<^sub>1#vs,ls\<^sub>2,C,M,?pc\<^sub>2,ics)#frs,sh\<^sub>2)"
    using IH\<^sub>2 Jcc_pieces_BinOp2[OF assms(1) pcs, of h\<^sub>1 v\<^sub>1 ls\<^sub>1 sh\<^sub>1 v\<^sub>2] by (simp add: add.assoc)
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>2,(w#vs,ls\<^sub>2,C,M,?pc\<^sub>2+1,ics)#frs,sh\<^sub>2)"
    using BinOp\<^sub>1 by(cases bop) auto
  finally show ?case using pcs by (auto split: bop.splits simp:add.assoc)
next
  case (BinOpThrow\<^sub>1\<^sub>1 e\<^sub>1 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 e h\<^sub>1 ls\<^sub>1 sh\<^sub>1 bop e\<^sub>2)
  obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v xa (e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2)
    = (True, frs', (None,h\<^sub>1,(v#vs,ls\<^sub>1,C,M,pc+size(compE\<^sub>2 (e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2)),ics)#frs,sh\<^sub>1), err)"
    using BinOpThrow\<^sub>1\<^sub>1.prems(1) by clarsimp
  have IH\<^sub>1: "PROP ?P e\<^sub>1 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (throw e) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics v xa vs frs
                     (I - pcs (compxE\<^sub>2 e\<^sub>2 (pc + length (compE\<^sub>2 e\<^sub>1)) (Suc (length vs))))" by fact
  show ?case using IH\<^sub>1 Jcc_pieces_BinOp1[OF pcs, of h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v] BinOpThrow\<^sub>1\<^sub>1.prems nsub_RI_Jcc_pieces
    by auto
next
  case (BinOpThrow\<^sub>2\<^sub>1 e\<^sub>1 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 v\<^sub>1 h\<^sub>1 ls\<^sub>1 sh\<^sub>1 e\<^sub>2 e h\<^sub>2 ls\<^sub>2 sh\<^sub>2 bop)
  obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>2 ls\<^sub>2 sh\<^sub>2 v xa (e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2)
    = (True, frs', (None,h\<^sub>2,(v#vs,ls\<^sub>2,C,M,pc+size(compE\<^sub>2 (e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2)),ics)#frs,sh\<^sub>2), err)"
    using BinOpThrow\<^sub>2\<^sub>1.prems(1) by clarsimp
  let ?pc = "pc + length(compE\<^sub>2 e\<^sub>1)"
  have IH\<^sub>1: "PROP ?P e\<^sub>1 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (Val v\<^sub>1) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics v\<^sub>1 xa vs frs
                     (I - pcs (compxE\<^sub>2 e\<^sub>2 (pc + length (compE\<^sub>2 e\<^sub>1)) (Suc (length vs))))" by fact
  have IH\<^sub>2: "PROP ?P e\<^sub>2 h\<^sub>1 ls\<^sub>1 sh\<^sub>1 (throw e) h\<^sub>2 ls\<^sub>2 sh\<^sub>2 E C M ?pc ics v xa (v\<^sub>1#vs) frs
                     (I - pcs(compxE\<^sub>2 e\<^sub>1 pc (size vs)))" by fact
  let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,(v\<^sub>1#vs,ls\<^sub>1,C,M,?pc,ics)#frs,sh\<^sub>1)"
  have 1: "P \<turnstile> (None,h\<^sub>0,frs',sh\<^sub>0) -jvm\<rightarrow> ?\<sigma>\<^sub>1"
    using IH\<^sub>1 Jcc_pieces_BinOp1[OF pcs, of h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v\<^sub>1] by simp
  have "(throw e = Val v \<longrightarrow>  P \<turnstile> (None, h\<^sub>0, Jcc_frames P C M vs ls\<^sub>0 pc ics frs (e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2), sh\<^sub>0) -jvm\<rightarrow>
     Jcc_rhs P\<^sub>1 E C M vs ls\<^sub>0 pc ics frs h\<^sub>2 ls\<^sub>2 sh\<^sub>2 v (e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2))
   \<and> (throw e = Throw xa \<longrightarrow> (\<exists>pc\<^sub>1. pc \<le> pc\<^sub>1 \<and> pc\<^sub>1 < pc + size(compE\<^sub>2 (e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2)) \<and>
               \<not> caught P pc\<^sub>1 h\<^sub>2 xa (compxE\<^sub>2 (e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2) pc (size vs)) \<and>
               (\<exists>vs'. P \<turnstile> (None,h\<^sub>0,frs',sh\<^sub>0) -jvm\<rightarrow> handle P C M xa h\<^sub>2 (vs'@vs) ls\<^sub>2 pc\<^sub>1 ics frs sh\<^sub>2)))"
   (is "?N \<and> (?eq \<longrightarrow> (\<exists>pc\<^sub>2. ?H pc\<^sub>2))")
  proof
    show ?N by simp
  next
    { assume ?eq
      then obtain pc\<^sub>2 vs' where
        pc\<^sub>2: "?pc \<le> pc\<^sub>2 \<and> pc\<^sub>2 < ?pc + size(compE\<^sub>2 e\<^sub>2) \<and>
              \<not> caught P pc\<^sub>2 h\<^sub>2 xa (compxE\<^sub>2 e\<^sub>2 ?pc (size vs + 1))" and
        2: "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> handle P C M xa h\<^sub>2 (vs'@v\<^sub>1#vs) ls\<^sub>2 pc\<^sub>2 ics frs sh\<^sub>2"
        using IH\<^sub>2 Jcc_pieces_BinOp2[OF assms(1) pcs, of h\<^sub>1 v\<^sub>1 ls\<^sub>1 sh\<^sub>1 v] BinOpThrow\<^sub>2\<^sub>1.prems by clarsimp
      then have "?H pc\<^sub>2" using jvm_trans[OF 1 2] by(auto intro!: exI[where x="vs'@[v\<^sub>1]"])
      hence "\<exists>pc\<^sub>2. ?H pc\<^sub>2" by iprover
    }
    thus "?eq \<longrightarrow> (\<exists>pc\<^sub>2. ?H pc\<^sub>2)" by iprover
  qed
  then show ?case using pcs by simp blast
next
  case (FAcc\<^sub>1 e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 a h\<^sub>1 ls\<^sub>1 sh\<^sub>1 C' fs F T D w)
  then obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v xa (e\<bullet>F{D})
    = (True, frs', (None,h\<^sub>1,(v#vs,ls\<^sub>1,C,M,pc+size(compE\<^sub>2 (e\<bullet>F{D})),ics)#frs,sh\<^sub>1), err)"
    using FAcc\<^sub>1.prems(1) by clarsimp
  have "P\<^sub>1 \<turnstile> D sees F,NonStatic:T in D" by(rule has_field_sees[OF has_field_idemp[OF FAcc\<^sub>1.hyps(4)]])
  then have field: "field P D F = (D,NonStatic,T)" by simp
  have IH: "PROP ?P e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (addr a) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics (Addr a) xa vs frs I" by fact
  let ?pc = "pc + length(compE\<^sub>2 e)"
  have "P \<turnstile> (None,h\<^sub>0,frs',sh\<^sub>0) -jvm\<rightarrow> (None,h\<^sub>1,(Addr a#vs,ls\<^sub>1,C,M,?pc,ics)#frs,sh\<^sub>1)"
    using IH Jcc_pieces_FAcc[OF pcs, of "Addr a"] pcs by simp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>1,(w#vs,ls\<^sub>1,C,M,?pc+1,ics)#frs,sh\<^sub>1)"
    using FAcc\<^sub>1 field by auto
  finally have "P \<turnstile> (None, h\<^sub>0, frs', sh\<^sub>0) -jvm\<rightarrow> (None,h\<^sub>1,(w#vs,ls\<^sub>1,C,M,?pc+1,ics)#frs,sh\<^sub>1)"
    by auto
  then show ?case using pcs by auto
next
  case (FAccNull\<^sub>1 e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 h\<^sub>1 ls\<^sub>1 sh\<^sub>1 F D)
  then obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v xa (e\<bullet>F{D})
    = (True, frs', (None,h\<^sub>1,(v#vs,ls\<^sub>1,C,M,pc+size(compE\<^sub>2 (e\<bullet>F{D})),ics)#frs,sh\<^sub>1), err)"
    using FAccNull\<^sub>1.prems(1) by clarsimp
  have IH: "PROP ?P e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 null h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics Null xa vs frs I" by fact
  let ?pc = "pc + length(compE\<^sub>2 e)"
  let ?xa = "addr_of_sys_xcpt NullPointer"
  have "P \<turnstile> (None,h\<^sub>0,frs',sh\<^sub>0) -jvm\<rightarrow> (None,h\<^sub>1,(Null#vs,ls\<^sub>1,C,M,?pc,ics)#frs,sh\<^sub>1)"
    using IH Jcc_pieces_FAcc[OF pcs, of Null] by simp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M ?xa h\<^sub>1 (Null#vs) ls\<^sub>1 ?pc ics frs sh\<^sub>1"
    using FAccNull\<^sub>1.prems
    by(fastforce simp:split_beta handle_def simp del: split_paired_Ex)
  finally show ?case using pcs by (auto intro!: exI[where x = ?pc] exI[where x="[Null]"])
next
  case (FAccThrow\<^sub>1 e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 e' h\<^sub>1 ls\<^sub>1 sh\<^sub>1 F D)
  then obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v xa (e\<bullet>F{D})
    = (True, frs', (None,h\<^sub>1,(v#vs,ls\<^sub>1,C,M,pc+size(compE\<^sub>2 (e\<bullet>F{D})),ics)#frs,sh\<^sub>1), err)"
    using FAccThrow\<^sub>1.prems(1) by clarsimp
  have IH: "PROP ?P e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (throw e') h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics v xa vs frs I" by fact
  show ?case using IH Jcc_pieces_FAcc[OF pcs, of v] FAccThrow\<^sub>1.prems nsub_RI_Jcc_pieces
    less_Suc_eq by auto
next
  case (FAccNone\<^sub>1 e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 a h\<^sub>1 ls\<^sub>1 sh\<^sub>1 C fs F D)
  then obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v xa (e\<bullet>F{D})
    = (True, frs', (None,h\<^sub>1,(v#vs,ls\<^sub>1,C,M,pc+size(compE\<^sub>2 (e\<bullet>F{D})),ics)#frs,sh\<^sub>1), err)"
    using FAccNone\<^sub>1.prems(1) by clarsimp
  have IH: "PROP ?P e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (addr a) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics (Addr a) xa vs frs I" by fact
  let ?pc = "pc + length(compE\<^sub>2 e)"
  let ?xa = "addr_of_sys_xcpt NoSuchFieldError"
  have "P \<turnstile> (None,h\<^sub>0,frs',sh\<^sub>0) -jvm\<rightarrow> (None,h\<^sub>1,(Addr a#vs,ls\<^sub>1,C,M,?pc,ics)#frs,sh\<^sub>1)"
    using IH Jcc_pieces_FAcc[OF pcs, of "Addr a"] by simp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M ?xa h\<^sub>1 (Addr a#vs) ls\<^sub>1 ?pc ics frs sh\<^sub>1"
    using FAccNone\<^sub>1
    by(cases ics; clarsimp simp:split_beta handle_def simp del: split_paired_Ex)
  finally show ?case using pcs by (auto intro!: exI[where x = ?pc] exI[where x="[Addr a]"])
next
  case (FAccStatic\<^sub>1 e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 a h\<^sub>1 ls\<^sub>1 sh\<^sub>1 C' fs F T D)
  then obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v xa (e\<bullet>F{D})
    = (True, frs', (None,h\<^sub>1,(v#vs,ls\<^sub>1,C,M,pc+size(compE\<^sub>2 (e\<bullet>F{D})),ics)#frs,sh\<^sub>1), err)"
    using FAccStatic\<^sub>1.prems(1) by clarsimp
  have "P\<^sub>1 \<turnstile> D sees F,Static:T in D" by(rule has_field_sees[OF has_field_idemp[OF FAccStatic\<^sub>1.hyps(4)]])
  then have field: "field P D F = (D,Static,T)" by simp
  have IH: "PROP ?P e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (addr a) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics (Addr a) xa vs frs I" by fact
  let ?pc = "pc + length(compE\<^sub>2 e)"
  let ?xa = "addr_of_sys_xcpt IncompatibleClassChangeError"
  have "P \<turnstile> (None,h\<^sub>0,frs',sh\<^sub>0) -jvm\<rightarrow> (None,h\<^sub>1,(Addr a#vs,ls\<^sub>1,C,M,?pc,ics)#frs,sh\<^sub>1)"
    using IH Jcc_pieces_FAcc[OF pcs, of "Addr a"] by simp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M ?xa h\<^sub>1 (Addr a#vs) ls\<^sub>1 ?pc ics frs sh\<^sub>1"
    using FAccStatic\<^sub>1 field by(fastforce simp:split_beta handle_def simp del: split_paired_Ex)
  finally show ?case using pcs by (auto intro!: exI[where x = ?pc] exI[where x="[Addr a]"])
next
  case (SFAcc\<^sub>1 C' F t D sh sfs v' h ls)
  have has: "P\<^sub>1 \<turnstile> D has F,Static:t in D" by(rule has_field_idemp[OF SFAcc\<^sub>1.hyps(1)])
  have "P\<^sub>1 \<turnstile> D sees F,Static:t in D" by(rule has_field_sees[OF has])
  then have field: "field P D F = (D,Static,t)" by simp
  then have "P \<turnstile> (None,h,Jcc_frames P C M vs ls pc ics frs (C'\<bullet>\<^sub>sF{D}),sh) -jvm\<rightarrow>
             (None,h,(v'#vs,ls,C,M,Suc pc,ics)#frs,sh)"
    using SFAcc\<^sub>1 has by(cases ics) auto
  then show ?case by clarsimp
next
  case (SFAccInit\<^sub>1 C' F t D sh h ls v' h' ls' sh' sfs i v'')
  then obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h vs ls pc ics frs sh I h' ls' sh' v xa (C'\<bullet>\<^sub>sF{D})
    = (True, frs', (None,h',(v#vs,ls',C,M,pc+size(compE\<^sub>2 (C'\<bullet>\<^sub>sF{D})),ics)#frs,sh'), err)"
    using SFAccInit\<^sub>1.prems(1) by clarsimp
  have "Ex (WTrt2\<^sub>1 P\<^sub>1 E h sh (INIT D ([D],False) \<leftarrow> unit))"
    using has_field_is_class'[OF SFAccInit\<^sub>1.hyps(1)] by auto
  then obtain err' where pcs':
    "Jcc_pieces P\<^sub>1 E C M h vs ls pc ics frs sh I h' ls' sh' v' xa (INIT D ([D],False) \<leftarrow> unit)
    = (True, (vs,ls,C,M,pc,Calling D []) # frs, (None,h',(vs,ls,C,M,pc,Called [])#frs,sh'), err')"
    using SFAccInit\<^sub>1.prems(1) by auto
  have IH: "PROP ?P (INIT D ([D],False) \<leftarrow> unit) h ls sh (Val v')
             h' ls' sh' E C M pc ics v' xa vs frs I" by fact
  have ls: "ls = ls'" by(rule init\<^sub>1_same_loc[OF SFAccInit\<^sub>1.hyps(3)])
  have has: "P\<^sub>1 \<turnstile> D has F,Static:t in D" by(rule has_field_idemp[OF SFAccInit\<^sub>1.hyps(1)])
  have "P\<^sub>1 \<turnstile> D sees F,Static:t in D" by(rule has_field_sees[OF has])
  then have field: "field P D F = (D,Static,t)" by simp
  have "P \<turnstile> (None,h,(vs,ls,C,M,pc,ics)#frs,sh) -jvm\<rightarrow> (None,h,(vs,ls,C,M,pc,Calling D [])#frs,sh)"
  proof(cases "sh D")
    case None then show ?thesis using SFAccInit\<^sub>1.hyps(1,2,5,6) SFAccInit\<^sub>1.prems field
      by(cases ics) auto
  next
    case (Some a)
    then obtain sfs i where "a = (sfs,i)" by(cases a)
    then show ?thesis using SFAccInit\<^sub>1.hyps(1,2,5,6) SFAccInit\<^sub>1.prems field Some
      by(cases ics; case_tac i) auto
  qed
  also have "P \<turnstile> ... -jvm\<rightarrow> (None, h', (vs, ls, C, M, pc, Called []) # frs, sh')"
    using IH pcs' by auto
  also have "P \<turnstile> ... -jvm\<rightarrow> (None, h', (v''#vs, ls, C, M, Suc pc, ics) # frs, sh')"
    using SFAccInit\<^sub>1.hyps(1,2,5,6) SFAccInit\<^sub>1.prems has field by(cases ics) auto
  finally show ?case using pcs ls by clarsimp
next
  case (SFAccInitThrow\<^sub>1 C' F t D sh h ls a h' ls' sh')
  obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h vs ls pc ics frs sh I h' ls' sh' v xa (C'\<bullet>\<^sub>sF{D})
    = (True, frs', (None,h',(v#vs,ls',C,M,pc+size(compE\<^sub>2 (C'\<bullet>\<^sub>sF{D})),ics)#frs,sh'), err)"
    using SFAccInitThrow\<^sub>1.prems(1) by clarsimp
  obtain a' where throw: "throw a = Throw a'" using eval\<^sub>1_final[OF SFAccInitThrow\<^sub>1.hyps(3)] by clarsimp
  have "Ex (WTrt2\<^sub>1 P\<^sub>1 E h sh (INIT D ([D],False) \<leftarrow> unit))"
    using has_field_is_class'[OF SFAccInitThrow\<^sub>1.hyps(1)] by auto
  then obtain vs' where pcs':
    "Jcc_pieces P\<^sub>1 E C M h vs ls pc ics frs sh I h' ls' sh' v a' (INIT D ([D],False) \<leftarrow> unit)
    = (True, (vs,ls,C,M,pc,Calling D []) # frs, (None,h',(vs,ls,C,M,pc,Called [])#frs,sh'),
        P \<turnstile> (None,h,(vs,ls,C,M,pc,Calling D []) # frs,sh)
               -jvm\<rightarrow> handle P C M a' h' (vs'@vs) ls pc ics frs sh')"
    using SFAccInitThrow\<^sub>1.prems(1) by simp blast
  have IH: "PROP ?P (INIT D ([D],False) \<leftarrow> unit) h ls sh (throw a)
             h' ls' sh' E C M pc ics v a' vs frs I" by fact
  have ls: "ls = ls'" by(rule init\<^sub>1_same_loc[OF SFAccInitThrow\<^sub>1.hyps(3)])
  have has: "P\<^sub>1 \<turnstile> D has F,Static:t in D" by(rule has_field_idemp[OF SFAccInitThrow\<^sub>1.hyps(1)])
  have "P\<^sub>1 \<turnstile> D sees F,Static:t in D" by(rule has_field_sees[OF has])
  then have field: "field P D F = (D,Static,t)" by simp
  then have "P \<turnstile> (None,h,(vs,ls,C,M,pc,ics)#frs,sh) -jvm\<rightarrow> (None,h,(vs,ls,C,M,pc,Calling D []) # frs,sh)"
  proof(cases "sh D")
    case None then show ?thesis using SFAccInitThrow\<^sub>1.hyps(1,2) SFAccInitThrow\<^sub>1.prems field
      by(cases ics) auto
  next
    case (Some a)
    then obtain sfs i where "a = (sfs,i)" by(cases a)
    then show ?thesis using SFAccInitThrow\<^sub>1.hyps(1,2) SFAccInitThrow\<^sub>1.prems field Some
      by(cases ics; case_tac i) auto
  qed
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M a' h' (vs'@vs) ls pc ics frs sh'"
    using IH pcs' throw by auto
  finally show ?case using throw ls by auto
next
  case (SFAccNone\<^sub>1 C' F D h\<^sub>1 ls\<^sub>1 sh\<^sub>1)
  then obtain frs' err where pcs:
   "Jcc_pieces P\<^sub>1 E C M h\<^sub>1 vs ls\<^sub>1 pc ics frs sh\<^sub>1 I h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v xa (C'\<bullet>\<^sub>sF{D})
    = (True, frs', (None,h\<^sub>1,(v#vs,ls\<^sub>1,C,M,pc+size(compE\<^sub>2 (C'\<bullet>\<^sub>sF{D})),ics)#frs,sh\<^sub>1), err)"
    by clarsimp
  let ?xa = "addr_of_sys_xcpt NoSuchFieldError"
  have "P \<turnstile> (None,h\<^sub>1,frs',sh\<^sub>1) -jvm\<rightarrow> handle P C M ?xa h\<^sub>1 vs ls\<^sub>1 pc ics frs sh\<^sub>1"
    using SFAccNone\<^sub>1 pcs
    by(cases ics; clarsimp simp:split_beta handle_def simp del: split_paired_Ex)
  then show ?case using pcs by(auto intro!: exI[where x = pc] exI[where x="[]"])
next
  case (SFAccNonStatic\<^sub>1 C' F t D h\<^sub>1 ls\<^sub>1 sh\<^sub>1)
  let ?frs' = "(vs, ls\<^sub>1, C, M, pc, ics) # frs"
  let ?xa = "addr_of_sys_xcpt IncompatibleClassChangeError"
  have "P\<^sub>1 \<turnstile> D sees F,NonStatic:t in D"
    by(rule has_field_sees[OF has_field_idemp[OF SFAccNonStatic\<^sub>1.hyps(1)]])
  then have field: "field P D F = (D,NonStatic,t)" by simp
  have "P \<turnstile> (None,h\<^sub>1,?frs',sh\<^sub>1) -jvm\<rightarrow> handle P C M ?xa h\<^sub>1 vs ls\<^sub>1 pc ics frs sh\<^sub>1"
    using SFAccNonStatic\<^sub>1
    proof(cases ics)
      case No_ics
      then show ?thesis using SFAccNonStatic\<^sub>1 field
       by (auto simp:split_beta handle_def simp del: split_paired_Ex)
    qed(simp_all)
  then show ?case by (auto intro!: exI[where x = pc] exI[where x="[]"])
next
  case (LAss\<^sub>1 e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 w h\<^sub>1 ls\<^sub>1 sh\<^sub>1 i ls\<^sub>2)
  let ?pc = "pc + length(compE\<^sub>2 e)"
  obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v xa (i:=e)
    = (True, frs', (None,h\<^sub>1,(v#vs,ls\<^sub>1,C,M,pc+size(compE\<^sub>2 (i:=e)),ics)#frs,sh\<^sub>1), err)"
    using LAss\<^sub>1.prems(1) by auto
  have IH: "PROP ?P e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (Val w) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics w xa vs frs I" by fact
  then have "P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc,ics)#frs,sh\<^sub>0) -jvm\<rightarrow>
             (None,h\<^sub>1,(w#vs,ls\<^sub>1,C,M,?pc,ics)#frs,sh\<^sub>1)"
    using Jcc_pieces_LAss[OF assms(1) pcs, of w] LAss\<^sub>1.prems pcs by auto
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>1,(Unit#vs,ls\<^sub>2,C,M,?pc+2,ics)#frs,sh\<^sub>1)"
    using LAss\<^sub>1 by (auto simp add:cast_ok_def)
  finally show ?case by auto
next
  case (LAssThrow\<^sub>1 e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 w h\<^sub>1 ls\<^sub>1 sh\<^sub>1 i)
  obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v xa (i:=e)
    = (True, frs', (None,h\<^sub>1,(v#vs,ls\<^sub>1,C,M,pc+size(compE\<^sub>2 (i:=e)),ics)#frs,sh\<^sub>1), err)"
    using LAssThrow\<^sub>1.prems(1) by clarsimp
  have IH: "PROP ?P e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (throw w) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics v xa vs frs I" by fact
  show ?case using IH Jcc_pieces_LAss[OF assms(1) pcs, of v] LAssThrow\<^sub>1.prems pcs less_SucI
    by(simp, blast)
next
  case (FAss\<^sub>1 e\<^sub>1 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 a h\<^sub>1 ls\<^sub>1 sh\<^sub>1 e\<^sub>2 w h\<^sub>2 ls\<^sub>2 sh\<^sub>2 C' fs F T D fs' h\<^sub>2')
  obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>2 ls\<^sub>2 sh\<^sub>2 v xa (e\<^sub>1\<bullet>F{D} := e\<^sub>2)
    = (True, frs', (None,h\<^sub>2,(v#vs,ls\<^sub>2,C,M,pc+size(compE\<^sub>2 (e\<^sub>1\<bullet>F{D} := e\<^sub>2)),ics)#frs,sh\<^sub>2), err)"
    using FAss\<^sub>1.prems(1) by clarsimp
  have "P\<^sub>1 \<turnstile> D sees F,NonStatic:T in D" by(rule has_field_sees[OF has_field_idemp[OF FAss\<^sub>1.hyps(6)]])
  then have field: "field P D F = (D,NonStatic,T)" by simp
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e\<^sub>1)"
  let ?pc\<^sub>2 = "?pc\<^sub>1 + length(compE\<^sub>2 e\<^sub>2)"
  have IH\<^sub>1: "PROP ?P e\<^sub>1 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (addr a) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics (Addr a) xa vs frs
                     (I - pcs (compxE\<^sub>2 e\<^sub>2 (pc + length (compE\<^sub>2 e\<^sub>1)) (Suc (length vs))))" by fact
  have IH\<^sub>2: "PROP ?P e\<^sub>2 h\<^sub>1 ls\<^sub>1 sh\<^sub>1 (Val w) h\<^sub>2 ls\<^sub>2 sh\<^sub>2 E C M ?pc\<^sub>1 ics w xa (Addr a#vs) frs
                     (I - pcs(compxE\<^sub>2 e\<^sub>1 pc (size vs)))" by fact
  have "P \<turnstile> (None,h\<^sub>0,frs',sh\<^sub>0) -jvm\<rightarrow> (None,h\<^sub>1,(Addr a#vs,ls\<^sub>1,C,M,?pc\<^sub>1,ics)#frs,sh\<^sub>1)"
    using IH\<^sub>1 Jcc_pieces_FAss1[OF pcs, of h\<^sub>1 ls\<^sub>1 sh\<^sub>1 "Addr a"] by simp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>2,(w#Addr a#vs,ls\<^sub>2,C,M,?pc\<^sub>2,ics)#frs,sh\<^sub>2)"
    using IH\<^sub>2 Jcc_pieces_FAss2[OF pcs, of h\<^sub>1 "Addr a" ls\<^sub>1 sh\<^sub>1 w] by (simp add: add.assoc)
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>2',(Unit#vs,ls\<^sub>2,C,M,?pc\<^sub>2+2,ics)#frs,sh\<^sub>2)"
    using FAss\<^sub>1 field by auto
  finally show ?case using pcs by (auto simp:add.assoc)
next
  case (FAssNull\<^sub>1 e\<^sub>1 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 h\<^sub>1 ls\<^sub>1 sh\<^sub>1 e\<^sub>2 w h\<^sub>2 ls\<^sub>2 sh\<^sub>2 F D)
  obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>2 ls\<^sub>2 sh\<^sub>2 v xa (e\<^sub>1\<bullet>F{D} := e\<^sub>2)
    = (True, frs', (None,h\<^sub>2,(v#vs,ls\<^sub>2,C,M,pc+size(compE\<^sub>2 (e\<^sub>1\<bullet>F{D} := e\<^sub>2)),ics)#frs,sh\<^sub>2), err)"
    using FAssNull\<^sub>1.prems(1) by clarsimp
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e\<^sub>1)"
  let ?pc\<^sub>2 = "?pc\<^sub>1 + length(compE\<^sub>2 e\<^sub>2)"
  let ?xa = "addr_of_sys_xcpt NullPointer"
  have IH\<^sub>1: "PROP ?P e\<^sub>1 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 null h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics Null xa vs frs
                     (I - pcs (compxE\<^sub>2 e\<^sub>2 (pc + length (compE\<^sub>2 e\<^sub>1)) (Suc (length vs))))" by fact
  have IH\<^sub>2: "PROP ?P e\<^sub>2 h\<^sub>1 ls\<^sub>1 sh\<^sub>1 (Val w) h\<^sub>2 ls\<^sub>2 sh\<^sub>2 E C M ?pc\<^sub>1 ics w xa (Null#vs) frs
                     (I - pcs(compxE\<^sub>2 e\<^sub>1 pc (size vs)))" by fact
  have "P \<turnstile> (None,h\<^sub>0,frs',sh\<^sub>0) -jvm\<rightarrow> (None,h\<^sub>1,(Null#vs,ls\<^sub>1,C,M,?pc\<^sub>1,ics)#frs,sh\<^sub>1)"
    using IH\<^sub>1 Jcc_pieces_FAss1[OF pcs, of h\<^sub>1 ls\<^sub>1 sh\<^sub>1 Null] by simp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>2,(w#Null#vs,ls\<^sub>2,C,M,?pc\<^sub>2,ics)#frs,sh\<^sub>2)"
    using IH\<^sub>2 Jcc_pieces_FAss2[OF pcs, of h\<^sub>1 Null ls\<^sub>1 sh\<^sub>1 w] by (simp add: add.assoc)
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M ?xa h\<^sub>2 (w#Null#vs) ls\<^sub>2 ?pc\<^sub>2 ics frs sh\<^sub>2"
    using FAssNull\<^sub>1 by(fastforce simp:split_beta handle_def simp del: split_paired_Ex)
  finally show ?case using pcs by (auto intro!: exI[where x = ?pc\<^sub>2] exI[where x="w#[Null]"])
next
  case (FAssThrow\<^sub>2\<^sub>1 e\<^sub>1 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 w h\<^sub>1 ls\<^sub>1 sh\<^sub>1 e\<^sub>2 e' h\<^sub>2 ls\<^sub>2 sh\<^sub>2 F D)
  let ?frs' = "(vs, ls\<^sub>0, C, M, pc, ics) # frs"
  obtain err where pcs: "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>2 ls\<^sub>2 sh\<^sub>2 v xa (e\<^sub>1\<bullet>F{D} := e\<^sub>2)
    = (True, ?frs', (None,h\<^sub>2,(v#vs,ls\<^sub>2,C,M,pc+size(compE\<^sub>2 (e\<^sub>1\<bullet>F{D} := e\<^sub>2)),ics)#frs,sh\<^sub>2), err)"
    using FAssThrow\<^sub>2\<^sub>1.prems(1) by clarsimp
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e\<^sub>1)"
  let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,(w#vs,ls\<^sub>1,C,M,?pc\<^sub>1,ics)#frs,sh\<^sub>1)"
  have IH\<^sub>1: "PROP ?P e\<^sub>1 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (Val w) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics w xa vs frs
                     (I - pcs (compxE\<^sub>2 e\<^sub>2 (pc + length (compE\<^sub>2 e\<^sub>1)) (Suc (length vs))))" by fact
  have IH\<^sub>2: "PROP ?P e\<^sub>2 h\<^sub>1 ls\<^sub>1 sh\<^sub>1 (throw e') h\<^sub>2 ls\<^sub>2 sh\<^sub>2 E C M ?pc\<^sub>1 ics v xa (w#vs) frs
                     (I - pcs(compxE\<^sub>2 e\<^sub>1 pc (size vs)))" by fact
  have 1: "P \<turnstile> (None,h\<^sub>0,?frs',sh\<^sub>0) -jvm\<rightarrow> ?\<sigma>\<^sub>1"
    using IH\<^sub>1 Jcc_pieces_FAss1[OF pcs, of h\<^sub>1 ls\<^sub>1 sh\<^sub>1 w] by simp
  show ?case (is "?N \<and> (?eq \<longrightarrow> ?err)")
  proof
    show ?N by simp
  next
    { assume ?eq
      moreover
      have "PROP ?P e\<^sub>2 h\<^sub>1 ls\<^sub>1 sh\<^sub>1 (throw e') h\<^sub>2 ls\<^sub>2 sh\<^sub>2 E C M ?pc\<^sub>1 ics v xa (w#vs) frs
                    (I - pcs (compxE\<^sub>2 e\<^sub>1 pc (length vs)))" by fact
      ultimately obtain pc\<^sub>2 vs' where
        pc\<^sub>2: "?pc\<^sub>1 \<le> pc\<^sub>2 \<and> pc\<^sub>2 < ?pc\<^sub>1 + size(compE\<^sub>2 e\<^sub>2) \<and>
              \<not> caught P pc\<^sub>2 h\<^sub>2 xa (compxE\<^sub>2 e\<^sub>2 ?pc\<^sub>1 (size vs + 1))" and
        2: "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> handle P C M xa h\<^sub>2 (vs'@w#vs) ls\<^sub>2 pc\<^sub>2 ics frs sh\<^sub>2"
        using FAssThrow\<^sub>2\<^sub>1.prems Jcc_pieces_FAss2[OF pcs, of h\<^sub>1 w ls\<^sub>1 sh\<^sub>1] by auto
      have ?err using Jcc_pieces_FAss2[OF pcs, of h\<^sub>1 w ls\<^sub>1 sh\<^sub>1] pc\<^sub>2 jvm_trans[OF 1 2]
        by(auto intro!: exI[where x=pc\<^sub>2] exI[where x="vs'@[w]"])
    }
    thus "?eq \<longrightarrow> ?err" by simp
  qed
next
  case (FAssThrow\<^sub>1\<^sub>1 e\<^sub>1 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 e' h\<^sub>1 ls\<^sub>1 sh\<^sub>1 F D e\<^sub>2)
  obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v xa (e\<^sub>1\<bullet>F{D} := e\<^sub>2)
    = (True, frs', (None,h\<^sub>1,(v#vs,ls\<^sub>1,C,M,pc+size(compE\<^sub>2 (e\<^sub>1\<bullet>F{D} := e\<^sub>2)),ics)#frs,sh\<^sub>1), err)"
    using FAssThrow\<^sub>1\<^sub>1.prems(1) by clarsimp
  have IH\<^sub>1: "PROP ?P e\<^sub>1 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (throw e') h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics v xa vs frs
                     (I - pcs (compxE\<^sub>2 e\<^sub>2 (pc + length (compE\<^sub>2 e\<^sub>1)) (Suc (length vs))))" by fact
  show ?case using IH\<^sub>1 Jcc_pieces_FAss1[OF pcs, of h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v] FAssThrow\<^sub>1\<^sub>1.prems nsub_RI_Jcc_pieces
    by auto
next
  case (FAssNone\<^sub>1 e\<^sub>1 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 a h\<^sub>1 ls\<^sub>1 sh\<^sub>1 e\<^sub>2 w h\<^sub>2 ls\<^sub>2 sh\<^sub>2 C' fs F D)
  obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>2 ls\<^sub>2 sh\<^sub>2 v xa (e\<^sub>1\<bullet>F{D} := e\<^sub>2)
    = (True, frs', (None,h\<^sub>2,(v#vs,ls\<^sub>2,C,M,pc+size(compE\<^sub>2 (e\<^sub>1\<bullet>F{D} := e\<^sub>2)),ics)#frs,sh\<^sub>2), err)"
    using FAssNone\<^sub>1.prems(1) by clarsimp
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e\<^sub>1)"
  let ?pc\<^sub>2 = "?pc\<^sub>1 + length(compE\<^sub>2 e\<^sub>2)"
  let ?xa = "addr_of_sys_xcpt NoSuchFieldError"
  have IH\<^sub>1: "PROP ?P e\<^sub>1 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (addr a) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics (Addr a) xa vs frs
                     (I - pcs (compxE\<^sub>2 e\<^sub>2 (pc + length (compE\<^sub>2 e\<^sub>1)) (Suc (length vs))))" by fact
  have IH\<^sub>2: "PROP ?P e\<^sub>2 h\<^sub>1 ls\<^sub>1 sh\<^sub>1 (Val w) h\<^sub>2 ls\<^sub>2 sh\<^sub>2 E C M ?pc\<^sub>1 ics w xa (Addr a#vs) frs
                     (I - pcs(compxE\<^sub>2 e\<^sub>1 pc (size vs)))" by fact
  have "P \<turnstile> (None,h\<^sub>0,frs',sh\<^sub>0) -jvm\<rightarrow> (None,h\<^sub>1,(Addr a#vs,ls\<^sub>1,C,M,?pc\<^sub>1,ics)#frs,sh\<^sub>1)"
    using IH\<^sub>1 Jcc_pieces_FAss1[OF pcs, of h\<^sub>1 ls\<^sub>1 sh\<^sub>1 "Addr a"] by simp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>2,(w#Addr a#vs,ls\<^sub>2,C,M,?pc\<^sub>2,ics)#frs,sh\<^sub>2)"
    using IH\<^sub>2 Jcc_pieces_FAss2[OF pcs, of h\<^sub>1 "Addr a" ls\<^sub>1 sh\<^sub>1 w] by (simp add: add.assoc)
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M ?xa h\<^sub>2 (w#Addr a#vs) ls\<^sub>2 ?pc\<^sub>2 ics frs sh\<^sub>2"
    using FAssNone\<^sub>1 by(fastforce simp:split_beta handle_def simp del: split_paired_Ex)
  finally show ?case using pcs by (auto intro!: exI[where x = ?pc\<^sub>2] exI[where x="w#[Addr a]"])
next
  case (FAssStatic\<^sub>1 e\<^sub>1 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 a h\<^sub>1 ls\<^sub>1 sh\<^sub>1 e\<^sub>2 w h\<^sub>2 ls\<^sub>2 sh\<^sub>2 C' fs F T D)
  obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>2 ls\<^sub>2 sh\<^sub>2 v xa (e\<^sub>1\<bullet>F{D} := e\<^sub>2)
    = (True, frs', (None,h\<^sub>2,(v#vs,ls\<^sub>2,C,M,pc+size(compE\<^sub>2 (e\<^sub>1\<bullet>F{D} := e\<^sub>2)),ics)#frs,sh\<^sub>2), err)"
    using FAssStatic\<^sub>1.prems(1) by clarsimp
  have "P\<^sub>1 \<turnstile> D sees F,Static:T in D" by(rule has_field_sees[OF has_field_idemp[OF FAssStatic\<^sub>1.hyps(6)]])
  then have field: "field P D F = (D,Static,T)" by simp
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e\<^sub>1)"
  let ?pc\<^sub>2 = "?pc\<^sub>1 + length(compE\<^sub>2 e\<^sub>2)"
  let ?xa = "addr_of_sys_xcpt IncompatibleClassChangeError"
  have IH\<^sub>1: "PROP ?P e\<^sub>1 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (addr a) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics (Addr a) xa vs frs
                     (I - pcs (compxE\<^sub>2 e\<^sub>2 (pc + length (compE\<^sub>2 e\<^sub>1)) (Suc (length vs))))" by fact
  have IH\<^sub>2: "PROP ?P e\<^sub>2 h\<^sub>1 ls\<^sub>1 sh\<^sub>1 (Val w) h\<^sub>2 ls\<^sub>2 sh\<^sub>2 E C M ?pc\<^sub>1 ics w xa (Addr a#vs) frs
                     (I - pcs(compxE\<^sub>2 e\<^sub>1 pc (size vs)))" by fact
  have "P \<turnstile> (None,h\<^sub>0,frs',sh\<^sub>0) -jvm\<rightarrow> (None,h\<^sub>1,(Addr a#vs,ls\<^sub>1,C,M,?pc\<^sub>1,ics)#frs,sh\<^sub>1)"
    using IH\<^sub>1 Jcc_pieces_FAss1[OF pcs, of h\<^sub>1 ls\<^sub>1 sh\<^sub>1 "Addr a"] by simp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>2,(w#Addr a#vs,ls\<^sub>2,C,M,?pc\<^sub>2,ics)#frs,sh\<^sub>2)"
    using IH\<^sub>2 Jcc_pieces_FAss2[OF pcs, of h\<^sub>1 "Addr a" ls\<^sub>1 sh\<^sub>1 w] by (simp add: add.assoc)
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M ?xa h\<^sub>2 (w#Addr a#vs) ls\<^sub>2 ?pc\<^sub>2 ics frs sh\<^sub>2"
    using FAssStatic\<^sub>1 field by(fastforce simp:split_beta handle_def simp del: split_paired_Ex)
  finally show ?case using pcs by (auto intro!: exI[where x = ?pc\<^sub>2] exI[where x="w#[Addr a]"])
next
  case (SFAss\<^sub>1 e\<^sub>2 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 w h\<^sub>1 ls\<^sub>1 sh\<^sub>1 C' F T D sfs sfs' sh\<^sub>1')
  then obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v xa (C'\<bullet>\<^sub>sF{D} := e\<^sub>2)
    = (True, frs', (None,h\<^sub>1,(v#vs,ls\<^sub>1,C,M,pc+size(compE\<^sub>2 (C'\<bullet>\<^sub>sF{D} := e\<^sub>2)),ics)#frs,sh\<^sub>1), err)"
    using SFAss\<^sub>1.prems(1) by clarsimp
  have "P\<^sub>1 \<turnstile> D sees F,Static:T in D" by(rule has_field_sees[OF has_field_idemp[OF SFAss\<^sub>1.hyps(3)]])
  then have field: "field P D F = (D,Static,T)" by simp
  have IH: "PROP ?P e\<^sub>2 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (Val w) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics w xa vs frs I" by fact
  let ?pc = "pc + length(compE\<^sub>2 e\<^sub>2)"
  have "P \<turnstile> (None,h\<^sub>0,frs',sh\<^sub>0) -jvm\<rightarrow> (None,h\<^sub>1,(w#vs,ls\<^sub>1,C,M,?pc,ics)#frs,sh\<^sub>1)"
    using IH Jcc_pieces_SFAss[OF pcs, where v'=w] pcs by simp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>1,(vs,ls\<^sub>1,C,M,?pc+1,ics)#frs,sh\<^sub>1')"
    using SFAss\<^sub>1.hyps(3-6) SFAss\<^sub>1.prems(1) field by auto
  also have "P \<turnstile> ... -jvm\<rightarrow> (None,h\<^sub>1,(Unit#vs,ls\<^sub>1,C,M,?pc+2,ics)#frs,sh\<^sub>1')"
    using SFAss\<^sub>1 by auto
  finally show ?case using pcs by auto
next
  case (SFAssInit\<^sub>1 e\<^sub>2 h ls sh w h\<^sub>1 ls\<^sub>1 sh\<^sub>1 C' F t D v' h' ls' sh' sfs i sfs' sh'')
  let ?pc = "pc + length(compE\<^sub>2 e\<^sub>2)"
  obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h vs ls pc ics frs sh I h' ls' sh'' v xa (C'\<bullet>\<^sub>sF{D}:=e\<^sub>2)
    = (True, frs', (None,h',(v#vs,ls',C,M,pc+size(compE\<^sub>2 (C'\<bullet>\<^sub>sF{D}:=e\<^sub>2)),ics)#frs,sh''), err)"
    using SFAssInit\<^sub>1.prems(1) by clarsimp
  have "Ex (WTrt2\<^sub>1 P\<^sub>1 E h\<^sub>1 sh\<^sub>1 (INIT D ([D],False) \<leftarrow> unit))"
    using has_field_is_class'[OF SFAssInit\<^sub>1.hyps(3)] by auto
  then obtain err' where pcs':
    "Jcc_pieces P\<^sub>1 E C M h\<^sub>1 (w#vs) ls\<^sub>1 ?pc ics frs sh\<^sub>1 I h' ls' sh' v' xa (INIT D ([D],False) \<leftarrow> unit)
    = (True, (w#vs,ls\<^sub>1,C,M,?pc,Calling D []) # frs,
       (None,h',(w#vs,ls\<^sub>1,C,M,?pc,Called [])#frs,sh'), err')"
    using SFAssInit\<^sub>1.prems(1) by simp
  have ls: "ls\<^sub>1 = ls'" by(rule init\<^sub>1_same_loc[OF SFAssInit\<^sub>1.hyps(5)])
  have has: "P\<^sub>1 \<turnstile> D has F,Static:t in D" by(rule has_field_idemp[OF SFAssInit\<^sub>1.hyps(3)])
  have "P\<^sub>1 \<turnstile> D sees F,Static:t in D" by(rule has_field_sees[OF has])
  then have field: "field P D F = (D,Static,t)" by simp
  have IH: "PROP ?P e\<^sub>2 h ls sh (Val w) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics w xa vs frs I" by fact
  have IHI: "PROP ?P (INIT D ([D],False) \<leftarrow> unit) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 (Val v')
             h' ls' sh' E C M ?pc ics v' xa (w#vs) frs I" by fact
  have "P \<turnstile> (None,h,frs',sh) -jvm\<rightarrow> (None,h\<^sub>1,(w#vs,ls\<^sub>1,C,M,?pc,ics)#frs,sh\<^sub>1)"
    using IH Jcc_pieces_SFAss[OF pcs, where v'=w] by simp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>1,(w#vs,ls\<^sub>1,C,M,?pc,Calling D [])#frs,sh\<^sub>1)"
  proof(cases "sh\<^sub>1 D")
    case None then show ?thesis using None SFAssInit\<^sub>1.hyps(1,3-5,7-9) SFAssInit\<^sub>1.prems field
      by(cases ics, auto)
  next
    case (Some a)
    then obtain sfs i where "a = (sfs,i)" by(cases a)
    then show ?thesis using SFAssInit\<^sub>1.hyps(1,3-5,7-9) SFAssInit\<^sub>1.prems field Some
      by(cases ics; case_tac i) auto
  qed
  also have "P \<turnstile> ... -jvm\<rightarrow> (None, h', (w#vs, ls\<^sub>1, C, M, ?pc, Called []) # frs, sh')"
    using IHI pcs' by clarsimp
  also have "P \<turnstile> ... -jvm\<rightarrow> (None, h', (vs, ls\<^sub>1, C, M, ?pc + 1, ics) # frs, sh'')"
    using SFAssInit\<^sub>1.hyps(1,3-5,7-9) SFAssInit\<^sub>1.prems has field by(cases ics) auto
  also have "P \<turnstile> ... -jvm\<rightarrow> (None, h', (Unit#vs, ls\<^sub>1, C, M, ?pc + 2, ics) # frs, sh'')"
    using SFAssInit\<^sub>1.hyps(1,3-5,7-9) SFAssInit\<^sub>1.prems has field by(cases ics) auto
  finally show ?case using pcs ls by simp blast
next
  case (SFAssInitThrow\<^sub>1 e\<^sub>2 h ls sh w h\<^sub>1 ls\<^sub>1 sh\<^sub>1 C' F t D a h' ls' sh')
  let ?pc = "pc + length(compE\<^sub>2 e\<^sub>2)"
  obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h vs ls pc ics frs sh I h' ls' sh' v xa (C'\<bullet>\<^sub>sF{D}:=e\<^sub>2)
    = (True, frs', (None,h',(v#vs,ls',C,M,pc+size(compE\<^sub>2 (C'\<bullet>\<^sub>sF{D}:=e\<^sub>2)),ics)#frs,sh'), err)"
    using SFAssInitThrow\<^sub>1.prems(1) by clarsimp
  obtain a' where throw: "throw a = Throw a'" using eval\<^sub>1_final[OF SFAssInitThrow\<^sub>1.hyps(5)] by clarsimp
  have "Ex (WTrt2\<^sub>1 P\<^sub>1 E h\<^sub>1 sh\<^sub>1 (INIT D ([D],False) \<leftarrow> unit))"
    using has_field_is_class'[OF SFAssInitThrow\<^sub>1.hyps(3)] by auto
  then obtain vs' where pcs':
    "Jcc_pieces P\<^sub>1 E C M h\<^sub>1 (w#vs) ls\<^sub>1 ?pc ics frs sh\<^sub>1 I h' ls' sh' v a' (INIT D ([D],False) \<leftarrow> unit)
    = (True, (w#vs,ls\<^sub>1,C,M,?pc,Calling D []) # frs, (None,h',(w#vs,ls\<^sub>1,C,M,?pc,Called [])#frs,sh'),
         P \<turnstile> (None,h\<^sub>1,(w#vs,ls\<^sub>1,C,M,?pc,Calling D []) # frs,sh\<^sub>1)
               -jvm\<rightarrow> handle P C M a' h' (vs'@w#vs) ls\<^sub>1 ?pc ics frs sh')"
    using SFAssInitThrow\<^sub>1.prems(1) by simp blast
  have ls: "ls\<^sub>1 = ls'" by(rule init\<^sub>1_same_loc[OF SFAssInitThrow\<^sub>1.hyps(5)])
  have has: "P\<^sub>1 \<turnstile> D has F,Static:t in D" by(rule has_field_idemp[OF SFAssInitThrow\<^sub>1.hyps(3)])
  have "P\<^sub>1 \<turnstile> D sees F,Static:t in D" by(rule has_field_sees[OF has])
  then have field: "field P D F = (D,Static,t)" by simp
  have IH: "PROP ?P e\<^sub>2 h ls sh (Val w) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics w xa vs frs I" by fact
  have IHI: "PROP ?P (INIT D ([D],False) \<leftarrow> unit) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 (throw a)
             h' ls' sh' E C M ?pc ics v a' (w#vs) frs I" by fact
  have "P \<turnstile> (None,h,(vs, ls, C, M, pc, ics) # frs,sh) -jvm\<rightarrow> (None,h\<^sub>1,(w#vs,ls\<^sub>1,C,M,?pc,ics)#frs,sh\<^sub>1)"
    using IH Jcc_pieces_SFAss[OF pcs, where v'=w] pcs by simp blast
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>1,(w#vs,ls\<^sub>1,C,M,?pc,Calling D [])#frs,sh\<^sub>1)"
  proof(cases "sh\<^sub>1 D")
    case None then show ?thesis using SFAssInitThrow\<^sub>1.hyps(1,3,4,5) SFAssInitThrow\<^sub>1.prems field
      by(cases ics) auto
  next
    case (Some a)
    then obtain sfs i where "a = (sfs,i)" by(cases a)
    then show ?thesis using SFAssInitThrow\<^sub>1.hyps(1,3,4,5) SFAssInitThrow\<^sub>1.prems field Some
      by(cases ics; case_tac i) auto
  qed
  also have "P \<turnstile> ... -jvm\<rightarrow> handle P C M a' h' (vs'@w#vs) ls\<^sub>1 ?pc ics frs sh'"
    using IHI pcs' throw by auto
  finally show ?case using throw ls by(auto intro!: exI[where x = ?pc] exI[where x="vs'@[w]"])
next
  case (SFAssThrow\<^sub>1 e\<^sub>2 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 e' h\<^sub>1 ls\<^sub>1 sh\<^sub>1 C' F D)
  then obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v xa (C'\<bullet>\<^sub>sF{D} := e\<^sub>2)
    = (True, frs', (None,h\<^sub>1,(v#vs,ls\<^sub>1,C,M,pc+size(compE\<^sub>2 (C'\<bullet>\<^sub>sF{D} := e\<^sub>2)),ics)#frs,sh\<^sub>1), err)"
    using SFAssThrow\<^sub>1.prems(1) by clarsimp
  have IH: "PROP ?P e\<^sub>2 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (throw e') h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics v xa vs frs I" by fact
  show ?case using IH Jcc_pieces_SFAss[OF pcs, where v'=v] SFAssThrow\<^sub>1.prems nsub_RI_Jcc_pieces
    less_Suc_eq by auto
next
  case (SFAssNone\<^sub>1 e\<^sub>2 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 w h\<^sub>1 ls\<^sub>1 sh\<^sub>1 C' F D)
  then obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v xa (C'\<bullet>\<^sub>sF{D} := e\<^sub>2)
    = (True, frs', (None,h\<^sub>1,(v#vs,ls\<^sub>1,C,M,pc+size(compE\<^sub>2 (C'\<bullet>\<^sub>sF{D} := e\<^sub>2)),ics)#frs,sh\<^sub>1), err)"
    using SFAssNone\<^sub>1.prems(1) by clarsimp
  have IH: "PROP ?P e\<^sub>2 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (Val w) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics w xa vs frs I" by fact
  let ?pc = "pc + length(compE\<^sub>2 e\<^sub>2)"
  let ?xa = "addr_of_sys_xcpt NoSuchFieldError"
  have "P \<turnstile> (None,h\<^sub>0,frs',sh\<^sub>0) -jvm\<rightarrow> (None,h\<^sub>1,(w#vs,ls\<^sub>1,C,M,?pc,ics)#frs,sh\<^sub>1)"
    using IH Jcc_pieces_SFAss[OF pcs, where v'=w] pcs by simp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M ?xa h\<^sub>1 (w#vs) ls\<^sub>1 ?pc ics frs sh\<^sub>1"
    using SFAssNone\<^sub>1 by(cases ics; clarsimp simp add: handle_def)
  finally show ?case using pcs by (auto intro!: exI[where x = ?pc] exI[where x="[w]"])
next
  case (SFAssNonStatic\<^sub>1 e\<^sub>2 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 w h\<^sub>1 ls\<^sub>1 sh\<^sub>1 C' F T D)
  then obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>1 ls\<^sub>1 sh\<^sub>1 v xa (C'\<bullet>\<^sub>sF{D} := e\<^sub>2)
    = (True, frs', (None,h\<^sub>1,(v#vs,ls\<^sub>1,C,M,pc+size(compE\<^sub>2 (C'\<bullet>\<^sub>sF{D} := e\<^sub>2)),ics)#frs,sh\<^sub>1), err)"
    using SFAssNonStatic\<^sub>1.prems(1) by clarsimp
  have IH: "PROP ?P e\<^sub>2 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (Val w) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics w xa vs frs I" by fact
  let ?pc = "pc + length(compE\<^sub>2 e\<^sub>2)"
  let ?xa = "addr_of_sys_xcpt IncompatibleClassChangeError"
  have "P\<^sub>1 \<turnstile> D sees F,NonStatic:T in D"
    by(rule has_field_sees[OF has_field_idemp[OF SFAssNonStatic\<^sub>1.hyps(3)]])
  then have field: "field P D F = (D,NonStatic,T)" by simp
  have "P \<turnstile> (None,h\<^sub>0,frs',sh\<^sub>0) -jvm\<rightarrow> (None,h\<^sub>1,(w#vs,ls\<^sub>1,C,M,?pc,ics)#frs,sh\<^sub>1)"
    using IH Jcc_pieces_SFAss[OF pcs, where v'=w] pcs by simp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M ?xa h\<^sub>1 (w#vs) ls\<^sub>1 ?pc ics frs sh\<^sub>1"
    using SFAssNonStatic\<^sub>1
    proof(cases ics)
      case No_ics
      then show ?thesis using SFAssNonStatic\<^sub>1 field
       by (auto simp:split_beta handle_def simp del: split_paired_Ex)
    qed(simp_all)
  finally show ?case using pcs by (auto intro!: exI[where x = ?pc] exI[where x="[w]"])
next
  case (Call\<^sub>1 e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 a h\<^sub>1 ls\<^sub>1 sh\<^sub>1 es pvs h\<^sub>2 ls\<^sub>2 sh\<^sub>2 Ca fs M' Ts T body D ls\<^sub>2' f h\<^sub>3 ls\<^sub>3 sh\<^sub>3)
  let ?frs\<^sub>0 = "(vs, ls\<^sub>0, C,M,pc,ics)#frs"
  let ?\<sigma>\<^sub>0 = "(None,h\<^sub>0,?frs\<^sub>0,sh\<^sub>0)"
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e)"
  let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,(Addr a#vs, ls\<^sub>1, C,M,?pc\<^sub>1,ics)#frs,sh\<^sub>1)"
  let ?pc\<^sub>2 = "?pc\<^sub>1 + length(compEs\<^sub>2 es)"
  let ?frs\<^sub>2 = "(rev pvs @ Addr a # vs, ls\<^sub>2, C,M,?pc\<^sub>2,ics)#frs"
  let ?\<sigma>\<^sub>2 = "(None,h\<^sub>2,?frs\<^sub>2,sh\<^sub>2)"
  let ?frs\<^sub>2' = "([], ls\<^sub>2', D,M',0,No_ics) # ?frs\<^sub>2"
  let ?\<sigma>\<^sub>2' = "(None, h\<^sub>2, ?frs\<^sub>2', sh\<^sub>2)"
  have nclinit: "M' \<noteq> clinit" using wf_sees_clinit1[OF wf] visible_method_exists[OF Call\<^sub>1.hyps(6)]
    sees_method_idemp[OF Call\<^sub>1.hyps(6)] by fastforce
  have "P\<^sub>1 \<turnstile>\<^sub>1 \<langle>es,(h\<^sub>1, ls\<^sub>1, sh\<^sub>1)\<rangle> [\<Rightarrow>] \<langle>map Val pvs,(h\<^sub>2, ls\<^sub>2, sh\<^sub>2)\<rangle>" by fact
  hence [simp]: "length es = length pvs" by(auto dest:evals\<^sub>1_preserves_elen)
  have invoke: "P,C,M,?pc\<^sub>2 \<triangleright> Invoke M' (length Ts)"
    using Call\<^sub>1.hyps(7) Call\<^sub>1.prems(1) by clarsimp
  have nsub: "\<not> sub_RI body" by(rule sees_wf\<^sub>1_nsub_RI[OF wf Call\<^sub>1.hyps(6)])
  obtain err where pcs:
    "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>3 ls\<^sub>2 sh\<^sub>3 v xa (e\<bullet>M'(es)) =
    (True, ?frs\<^sub>0, (None, h\<^sub>3, (v#vs, ls\<^sub>2, C,M,?pc\<^sub>2+1,ics)#frs,sh\<^sub>3), err)"
   using Call\<^sub>1.prems(1) by clarsimp
  have IH: "PROP ?P e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (addr a) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics (Addr a) xa vs frs
    (I - pcs (compxEs\<^sub>2 es (pc + length (compE\<^sub>2 e)) (Suc (length vs))))" by fact
  have IH_es: "PROP ?Ps es h\<^sub>1 ls\<^sub>1 sh\<^sub>1 (map Val pvs) h\<^sub>2 ls\<^sub>2 sh\<^sub>2 C M ?pc\<^sub>1 ics pvs xa
                    (map Val pvs) (Addr a#vs) frs (I - pcs(compxE\<^sub>2 e pc (size vs)))" by fact
  have "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>1" using Jcc_pieces_Call1[OF pcs] IH by clarsimp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^sub>2" using IH_es Call\<^sub>1.prems by fastforce
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^sub>2'"
    using jvm_Invoke[OF assms(1) invoke _ Call\<^sub>1.hyps(6-8)] Call\<^sub>1.hyps(5) Call\<^sub>1.prems(1) by simp
  finally have 1: "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>2'".
  have "P\<^sub>1 \<turnstile> Ca sees M',NonStatic: Ts\<rightarrow>T = body in D" by fact
  then have M'_in_D: "P\<^sub>1 \<turnstile> D sees M',NonStatic: Ts\<rightarrow>T = body in D"
    by(rule sees_method_idemp) 
  have M'_code: "compP\<^sub>2 P\<^sub>1,D,M',0 \<rhd> compE\<^sub>2 body @ [Return]" using beforeM M'_in_D by simp
  have M'_xtab: "compP\<^sub>2 P\<^sub>1,D,M' \<rhd> compxE\<^sub>2 body 0 0/{..<size(compE\<^sub>2 body)},0"
    using M'_in_D by(rule beforexM)
  have IH_body: "PROP ?P body h\<^sub>2 ls\<^sub>2' sh\<^sub>2 f h\<^sub>3 ls\<^sub>3 sh\<^sub>3 (Class D # Ts) D M' 0 No_ics v xa [] ?frs\<^sub>2
    ({..<size(compE\<^sub>2 body)})" by fact
  have cond: "Jcc_cond P\<^sub>1 (Class D # Ts) D M' [] 0 No_ics {..<length (compE\<^sub>2 body)} h\<^sub>2 sh\<^sub>2 body"
    using nsub_RI_Jcc_pieces[OF assms(1) nsub] M'_code M'_xtab by clarsimp
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm (is "?val \<longrightarrow> ?trans")
    proof
      assume val: ?val
      note 1
      also have "P \<turnstile> ?\<sigma>\<^sub>2' -jvm\<rightarrow> (None,h\<^sub>3,([v],ls\<^sub>3,D,M',size(compE\<^sub>2 body),No_ics)#?frs\<^sub>2,sh\<^sub>3)"
        using val IH_body Call\<^sub>1.prems M'_code cond nsub_RI_Jcc_pieces nsub by auto
      also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None, h\<^sub>3, (v#vs, ls\<^sub>2, C,M,?pc\<^sub>2+1,ics)#frs,sh\<^sub>3)"
        using Call\<^sub>1.hyps(7) M'_code M'_in_D nclinit by(cases T, auto)
      finally show ?trans by(simp add:add.assoc)
    qed
  next
    show ?Err (is "?throw \<longrightarrow> ?err")
    proof
      assume throw: ?throw
      with IH_body obtain pc\<^sub>2 vs' where
        pc\<^sub>2: "0 \<le> pc\<^sub>2 \<and> pc\<^sub>2 < size(compE\<^sub>2 body) \<and>
              \<not> caught P pc\<^sub>2 h\<^sub>3 xa (compxE\<^sub>2 body 0 0)" and
        2: "P \<turnstile> ?\<sigma>\<^sub>2' -jvm\<rightarrow> handle P D M' xa h\<^sub>3 vs' ls\<^sub>3 pc\<^sub>2 No_ics ?frs\<^sub>2 sh\<^sub>3"
        using Call\<^sub>1.prems M'_code M'_xtab cond nsub_RI_Jcc_pieces nsub
         by (auto simp del:split_paired_Ex)
      have "handle P D M' xa h\<^sub>3 vs' ls\<^sub>3 pc\<^sub>2 No_ics ?frs\<^sub>2 sh\<^sub>3 =
            handle P C M xa h\<^sub>3 (rev pvs @ Addr a # vs) ls\<^sub>2 ?pc\<^sub>2 ics frs sh\<^sub>3"
        using pc\<^sub>2 M'_in_D nclinit by(auto simp add:handle_def)
      then show "?err" using pc\<^sub>2 jvm_trans[OF 1 2]
       by(auto intro!:exI[where x="?pc\<^sub>2"] exI[where x="rev pvs@[Addr a]"])
    qed
  qed
next
  case (CallParamsThrow\<^sub>1 e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 w h\<^sub>1 ls\<^sub>1 sh\<^sub>1 es es' h\<^sub>2 ls\<^sub>2 sh\<^sub>2 pvs ex es'' M')
  let ?frs\<^sub>0 = "(vs, ls\<^sub>0, C,M,pc,ics)#frs"
  let ?\<sigma>\<^sub>0 = "(None,h\<^sub>0,(vs, ls\<^sub>0, C,M,pc,ics)#frs,sh\<^sub>0)"
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e)"
  let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,(w # vs, ls\<^sub>1, C,M,?pc\<^sub>1,ics)#frs,sh\<^sub>1)"
  let ?pc\<^sub>2 = "?pc\<^sub>1 + length(compEs\<^sub>2 es)"
  obtain err where pcs:
    "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>2 ls\<^sub>2 sh\<^sub>2 v xa (e\<bullet>M'(es)) =
    (True, ?frs\<^sub>0, (None, h\<^sub>2, (v#vs, ls\<^sub>2, C,M,?pc\<^sub>2+1,ics)#frs,sh\<^sub>2), err)"
   using CallParamsThrow\<^sub>1.prems(1) by clarsimp
  have IH: "PROP ?P e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (Val w) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics w xa vs frs
    (I - pcs (compxEs\<^sub>2 es (pc + length (compE\<^sub>2 e)) (Suc (length vs))))" by fact
  have 1: "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>1" using Jcc_pieces_Call1[OF pcs] IH by clarsimp
  have Isubs: "{?pc\<^sub>1..<?pc\<^sub>2} \<subseteq> I - pcs (compxE\<^sub>2 e pc (length vs))"
    using CallParamsThrow\<^sub>1.prems by clarsimp
  show ?case (is "?N \<and> (?eq \<longrightarrow> ?err)")
  proof
    show ?N by simp
  next
    { assume ?eq
      moreover
      have "PROP ?Ps es h\<^sub>1 ls\<^sub>1 sh\<^sub>1 es' h\<^sub>2 ls\<^sub>2 sh\<^sub>2 C M ?pc\<^sub>1 ics pvs xa es'' (w#vs) frs
        (I - pcs (compxE\<^sub>2 e pc (length vs)))" by fact
      ultimately obtain vs' where "\<exists>pc\<^sub>2.
        (?pc\<^sub>1 \<le> pc\<^sub>2 \<and> pc\<^sub>2 < ?pc\<^sub>1 + size(compEs\<^sub>2 es) \<and>
         \<not> caught P pc\<^sub>2 h\<^sub>2 xa (compxEs\<^sub>2 es ?pc\<^sub>1 (size vs + 1))) \<and>
        P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> handle P C M xa h\<^sub>2 (vs'@w#vs) ls\<^sub>2 pc\<^sub>2 ics frs sh\<^sub>2"
        (is "\<exists>pc\<^sub>2. ?PC pc\<^sub>2 \<and> ?Exec pc\<^sub>2")
        using CallParamsThrow\<^sub>1 Isubs by auto
      then obtain pc\<^sub>2 where pc\<^sub>2: "?PC pc\<^sub>2" and 2: "?Exec pc\<^sub>2" by iprover
      then have "?err" using pc\<^sub>2 jvm_trans[OF 1 2]
       by(auto intro!: exI[where x="pc\<^sub>2"] exI[where x="vs'@[w]"])
    }
    thus "?eq \<longrightarrow> ?err" by simp
  qed
next
  case (CallNull\<^sub>1 e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 h\<^sub>1 ls\<^sub>1 sh\<^sub>1 es pvs h\<^sub>2 ls\<^sub>2 sh\<^sub>2 M')
  have "P\<^sub>1 \<turnstile>\<^sub>1 \<langle>es,(h\<^sub>1, ls\<^sub>1, sh\<^sub>1)\<rangle> [\<Rightarrow>] \<langle>map Val pvs,(h\<^sub>2, ls\<^sub>2, sh\<^sub>2)\<rangle>" by fact
  hence [simp]: "length es = length pvs" by(auto dest:evals\<^sub>1_preserves_elen)
  let ?frs\<^sub>0 = "(vs, ls\<^sub>0, C,M,pc,ics)#frs"
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e)"
  let ?pc\<^sub>2 = "?pc\<^sub>1 + length(compEs\<^sub>2 es)"
  let ?xa = "addr_of_sys_xcpt NullPointer"
  obtain err where pcs:
    "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>2 ls\<^sub>2 sh\<^sub>2 v xa (e\<bullet>M'(es)) =
    (True, ?frs\<^sub>0, (None, h\<^sub>2, (v#vs, ls\<^sub>2, C,M,?pc\<^sub>2+1,ics)#frs,sh\<^sub>2), err)"
   using CallNull\<^sub>1.prems(1) by clarsimp
  have IH: "PROP ?P e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 null h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics Null xa vs frs
    (I - pcs (compxEs\<^sub>2 es (pc + length (compE\<^sub>2 e)) (Suc (length vs))))" by fact
  have IH_es: "PROP ?Ps es h\<^sub>1 ls\<^sub>1 sh\<^sub>1 (map Val pvs) h\<^sub>2 ls\<^sub>2 sh\<^sub>2 C M ?pc\<^sub>1 ics pvs xa
                    (map Val pvs) (Null#vs) frs (I - pcs(compxE\<^sub>2 e pc (size vs)))" by fact
  have Isubs: "{pc + length (compE\<^sub>2 e)..<pc + length (compE\<^sub>2 e) + length (compEs\<^sub>2 es)}
     \<subseteq> I - pcs (compxE\<^sub>2 e pc (length vs))" using CallNull\<^sub>1.prems by clarsimp
  have "P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc,ics)#frs,sh\<^sub>0) -jvm\<rightarrow>
             (None,h\<^sub>1,(Null#vs,ls\<^sub>1,C,M,?pc\<^sub>1,ics)#frs,sh\<^sub>1)"
    using Jcc_pieces_Call1[OF pcs] IH by clarsimp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>2,(rev pvs@Null#vs,ls\<^sub>2,C,M,?pc\<^sub>2,ics)#frs,sh\<^sub>2)"
    using CallNull\<^sub>1 IH_es Isubs by auto
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M ?xa h\<^sub>2 (rev pvs@Null#vs) ls\<^sub>2 ?pc\<^sub>2 ics frs sh\<^sub>2"
    using CallNull\<^sub>1.prems
    by(auto simp:split_beta handle_def nth_append simp del: split_paired_Ex)
  finally show ?case by (auto intro!: exI[where x = ?pc\<^sub>2] exI[where x="rev pvs@[Null]"])
next
  case (CallObjThrow\<^sub>1 e h ls sh e' h' ls' sh' M' es)
  obtain err where pcs:
    "Jcc_pieces P\<^sub>1 E C M h vs ls pc ics frs sh I h' ls' sh' v xa (e\<bullet>M'(es)) =
    (True, (vs, ls, C,M,pc,ics)#frs,
       (None, h', (v#vs, ls', C,M,pc+size(compE\<^sub>2 (e\<bullet>M'(es))),ics)#frs,sh'), err)"
   using CallObjThrow\<^sub>1.prems(1) by clarsimp
  obtain a' where throw: "throw e' = Throw a'"
    using eval\<^sub>1_final[OF CallObjThrow\<^sub>1.hyps(1)] by clarsimp
  have IH: "PROP ?P e h ls sh (throw e') h' ls' sh' E C M pc ics v a' vs frs
    (I - pcs (compxEs\<^sub>2 es (pc + length (compE\<^sub>2 e)) (Suc (length vs))))" by fact
  show ?case using IH Jcc_pieces_Call1[OF pcs] throw CallObjThrow\<^sub>1.prems nsub_RI_Jcc_pieces
    by auto
next
  case (CallNone\<^sub>1 e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 a h\<^sub>1 ls\<^sub>1 sh\<^sub>1 es pvs h\<^sub>2 ls\<^sub>2 sh\<^sub>2 C' fs M')
  let ?frs\<^sub>0 = "(vs, ls\<^sub>0, C,M,pc,ics)#frs"
  let ?\<sigma>\<^sub>0 = "(None,h\<^sub>0,?frs\<^sub>0,sh\<^sub>0)"
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e)"
  let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,(Addr a#vs, ls\<^sub>1, C,M,?pc\<^sub>1,ics)#frs,sh\<^sub>1)"
  let ?pc\<^sub>2 = "?pc\<^sub>1 + length(compEs\<^sub>2 es)"
  let ?frs\<^sub>2 = "(rev pvs @ Addr a # vs, ls\<^sub>2, C,M,?pc\<^sub>2,ics)#frs"
  let ?\<sigma>\<^sub>2 = "(None,h\<^sub>2,?frs\<^sub>2,sh\<^sub>2)"
  let ?xa = "addr_of_sys_xcpt NoSuchMethodError"
  have "P\<^sub>1 \<turnstile>\<^sub>1 \<langle>es,(h\<^sub>1, ls\<^sub>1, sh\<^sub>1)\<rangle> [\<Rightarrow>] \<langle>map Val pvs,(h\<^sub>2, ls\<^sub>2, sh\<^sub>2)\<rangle>" by fact
  hence [simp]: "length es = length pvs" by(auto dest:evals\<^sub>1_preserves_elen)
  have aux: "(rev pvs @ Addr a # vs) ! length pvs = Addr a"
    by (metis length_rev nth_append_length)
  have nmeth: "\<not>(\<exists>b Ts T body D. P \<turnstile> C' sees M', b :  Ts\<rightarrow>T = body in D)"
    using sees_method_compPD CallNone\<^sub>1.hyps(6) by fastforce
  obtain err where pcs:
    "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>2 ls\<^sub>2 sh\<^sub>2 v xa (e\<bullet>M'(es)) =
    (True, ?frs\<^sub>0, (None, h\<^sub>2, (v#vs, ls\<^sub>2, C,M,?pc\<^sub>2+1,ics)#frs,sh\<^sub>2), err)"
   using CallNone\<^sub>1.prems(1) by clarsimp
  have IH: "PROP ?P e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (addr a) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics (Addr a) xa vs frs
    (I - pcs (compxEs\<^sub>2 es (pc + length (compE\<^sub>2 e)) (Suc (length vs))))" by fact
  have IH_es: "PROP ?Ps es h\<^sub>1 ls\<^sub>1 sh\<^sub>1 (map Val pvs) h\<^sub>2 ls\<^sub>2 sh\<^sub>2 C M ?pc\<^sub>1 ics pvs xa
                    (map Val pvs) (Addr a#vs) frs (I - pcs(compxE\<^sub>2 e pc (size vs)))" by fact
  have "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>1" using Jcc_pieces_Call1[OF pcs] IH by clarsimp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^sub>2" using IH_es CallNone\<^sub>1.prems by fastforce
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M ?xa h\<^sub>2 (rev pvs@Addr a#vs) ls\<^sub>2 ?pc\<^sub>2 ics frs sh\<^sub>2"
    using CallNone\<^sub>1.hyps(5) CallNone\<^sub>1.prems aux nmeth
     by(cases "method P C' M'", cases "find_handler P ?xa h\<^sub>2 frs sh\<^sub>2", auto simp: handle_def)
  finally show ?case using pcs by (auto intro!: exI[where x = ?pc\<^sub>2] exI[where x="rev pvs@[Addr a]"])
next
  case (CallStatic\<^sub>1 e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 a h\<^sub>1 ls\<^sub>1 sh\<^sub>1 es pvs h\<^sub>2 ls\<^sub>2 sh\<^sub>2 C' fs M' Ts T body D)
  let ?frs\<^sub>0 = "(vs, ls\<^sub>0, C,M,pc,ics)#frs"
  let ?\<sigma>\<^sub>0 = "(None,h\<^sub>0,?frs\<^sub>0,sh\<^sub>0)"
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e)"
  let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,(Addr a#vs, ls\<^sub>1, C,M,?pc\<^sub>1,ics)#frs,sh\<^sub>1)"
  let ?pc\<^sub>2 = "?pc\<^sub>1 + length(compEs\<^sub>2 es)"
  let ?frs\<^sub>2 = "(rev pvs @ Addr a # vs, ls\<^sub>2, C,M,?pc\<^sub>2,ics)#frs"
  let ?\<sigma>\<^sub>2 = "(None,h\<^sub>2,?frs\<^sub>2,sh\<^sub>2)"
  let ?xa = "addr_of_sys_xcpt IncompatibleClassChangeError"
  have "P\<^sub>1 \<turnstile>\<^sub>1 \<langle>es,(h\<^sub>1, ls\<^sub>1, sh\<^sub>1)\<rangle> [\<Rightarrow>] \<langle>map Val pvs,(h\<^sub>2, ls\<^sub>2, sh\<^sub>2)\<rangle>" by fact
  hence [simp]: "length es = length pvs" by(auto dest:evals\<^sub>1_preserves_elen)
  have aux: "(rev pvs @ Addr a # vs) ! length pvs = Addr a"
    by (metis length_rev nth_append_length)
  obtain body' where method: "P \<turnstile> C' sees M', Static :  Ts\<rightarrow>T = body' in D"
    by (metis CallStatic\<^sub>1.hyps(6) P_def compP\<^sub>2_def sees_method_compP)
  obtain err where pcs:
    "Jcc_pieces P\<^sub>1 E C M h\<^sub>0 vs ls\<^sub>0 pc ics frs sh\<^sub>0 I h\<^sub>2 ls\<^sub>2 sh\<^sub>2 v xa (e\<bullet>M'(es)) =
    (True, ?frs\<^sub>0, (None, h\<^sub>2, (v#vs, ls\<^sub>2, C,M,?pc\<^sub>2+1,ics)#frs,sh\<^sub>2), err)"
   using CallStatic\<^sub>1.prems(1) by clarsimp
  have IH: "PROP ?P e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (addr a) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics (Addr a) xa vs frs
    (I - pcs (compxEs\<^sub>2 es (pc + length (compE\<^sub>2 e)) (Suc (length vs))))" by fact
  have IH_es: "PROP ?Ps es h\<^sub>1 ls\<^sub>1 sh\<^sub>1 (map Val pvs) h\<^sub>2 ls\<^sub>2 sh\<^sub>2 C M ?pc\<^sub>1 ics pvs xa
                    (map Val pvs) (Addr a#vs) frs (I - pcs(compxE\<^sub>2 e pc (size vs)))" by fact
  have "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>1" using Jcc_pieces_Call1[OF pcs] IH by clarsimp
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^sub>2" using IH_es CallStatic\<^sub>1.prems by fastforce
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M ?xa h\<^sub>2 (rev pvs@Addr a#vs) ls\<^sub>2 ?pc\<^sub>2 ics frs sh\<^sub>2"
    using CallStatic\<^sub>1.hyps(5) CallStatic\<^sub>1.prems aux method
     by(cases "method P C' M'", cases "find_handler P ?xa h\<^sub>2 frs sh\<^sub>2")
       (auto simp: handle_def; meson frames_of.cases)
  finally show ?case using pcs by (auto intro!: exI[where x = ?pc\<^sub>2] exI[where x="rev pvs@[Addr a]"])
next
  case (SCallParamsThrow\<^sub>1 es h\<^sub>1 ls\<^sub>1 sh\<^sub>1 es' h\<^sub>2 ls\<^sub>2 sh\<^sub>2 pvs ex es'' C' M')
  show ?case
  proof(cases "M' = clinit \<and> es = []")
    case clinit: True then show ?thesis
      using SCallParamsThrow\<^sub>1.hyps(1,3) evals\<^sub>1_cases(1) by fastforce
  next
    case nclinit: False
    let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,(vs, ls\<^sub>1, C,M,pc,ics)#frs,sh\<^sub>1)"
    let ?pc\<^sub>2 = "pc + length(compEs\<^sub>2 es)"
    have Isubs: "{pc..<pc + length (compEs\<^sub>2 es)} \<subseteq> I" using SCallParamsThrow\<^sub>1.prems nclinit by clarsimp
    show ?thesis (is "?N \<and> (?eq \<longrightarrow> ?err)")
    proof
      show ?N by simp
    next
      { assume ?eq
        moreover
        have "PROP ?Ps es h\<^sub>1 ls\<^sub>1 sh\<^sub>1 es' h\<^sub>2 ls\<^sub>2 sh\<^sub>2 C M pc ics pvs xa es'' vs frs I" by fact
        ultimately have "\<exists>pc\<^sub>2.
          (pc \<le> pc\<^sub>2 \<and> pc\<^sub>2 < pc + size(compEs\<^sub>2 es) \<and>
           \<not> caught P pc\<^sub>2 h\<^sub>2 xa (compxEs\<^sub>2 es pc (size vs))) \<and>
          (\<exists>vs'. P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> handle P C M xa h\<^sub>2 (vs'@vs) ls\<^sub>2 pc\<^sub>2 ics frs sh\<^sub>2)"
          (is "\<exists>pc\<^sub>2. ?PC pc\<^sub>2 \<and> ?Exec pc\<^sub>2")
          using SCallParamsThrow\<^sub>1 Isubs nclinit by auto
        then obtain pc\<^sub>2 where pc\<^sub>2: "?PC pc\<^sub>2" and 2: "?Exec pc\<^sub>2" by iprover
        then have "?err" using pc\<^sub>2 2 by(auto intro: exI[where x="pc\<^sub>2"])
      }
      thus "?eq \<longrightarrow> ?err" by iprover
    qed
  qed
next
  case (SCallNone\<^sub>1 es h\<^sub>1 ls\<^sub>1 sh\<^sub>1 pvs h\<^sub>2 ls\<^sub>2 sh\<^sub>2 C' M')
  show ?case
  proof(cases "M' = clinit \<and> es = []")
    case clinit: True then show ?thesis using SCallNone\<^sub>1.hyps(3) SCallNone\<^sub>1.prems by auto
  next
    case nclinit: False
    let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,(vs, ls\<^sub>1, C,M,pc,ics)#frs,sh\<^sub>1)"
    let ?pc\<^sub>2 = "pc + length(compEs\<^sub>2 es)"
    let ?frs\<^sub>2 = "(rev pvs @ vs, ls\<^sub>2, C,M,?pc\<^sub>2,ics)#frs"
    let ?\<sigma>\<^sub>2 = "(None,h\<^sub>2,?frs\<^sub>2,sh\<^sub>2)"
    let ?xa = "addr_of_sys_xcpt NoSuchMethodError"
    have "P\<^sub>1 \<turnstile>\<^sub>1 \<langle>es,(h\<^sub>1, ls\<^sub>1, sh\<^sub>1)\<rangle> [\<Rightarrow>] \<langle>map Val pvs,(h\<^sub>2, ls\<^sub>2, sh\<^sub>2)\<rangle>" by fact
    hence [simp]: "length es = length pvs" by(auto dest:evals\<^sub>1_preserves_elen)
    have nmeth: "\<not>(\<exists>b Ts T body D. P \<turnstile> C' sees M', b :  Ts\<rightarrow>T = body in D)"
      using sees_method_compPD SCallNone\<^sub>1.hyps(3) by fastforce
    have IH_es: "PROP ?Ps es h\<^sub>1 ls\<^sub>1 sh\<^sub>1 (map Val pvs) h\<^sub>2 ls\<^sub>2 sh\<^sub>2 C M pc ics pvs xa
                      (map Val pvs) vs frs I" by fact
    have "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> ?\<sigma>\<^sub>2" using IH_es SCallNone\<^sub>1.prems nclinit by auto fastforce+
    also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M ?xa h\<^sub>2 (rev pvs@vs) ls\<^sub>2 ?pc\<^sub>2 ics frs sh\<^sub>2"
      using SCallNone\<^sub>1.prems nmeth nclinit
       by(cases "method P C' M'", cases "find_handler P ?xa h\<^sub>2 frs sh\<^sub>2", auto simp: handle_def)
    finally show ?thesis using nclinit by (auto intro: exI[where x = ?pc\<^sub>2])
  qed
next
  case (SCallNonStatic\<^sub>1 es h\<^sub>1 ls\<^sub>1 sh\<^sub>1 pvs h\<^sub>2 ls\<^sub>2 sh\<^sub>2 C' M' Ts T body D)
  show ?case
  proof(cases "M' = clinit \<and> es = []")
    case clinit: True then show ?thesis
      using SCallNonStatic\<^sub>1.hyps(3) SCallNonStatic\<^sub>1.prems sees_method_fun by fastforce
  next
    case nclinit: False
    let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,(vs, ls\<^sub>1, C,M,pc,ics)#frs,sh\<^sub>1)"
    let ?pc\<^sub>2 = "pc + length(compEs\<^sub>2 es)"
    let ?frs\<^sub>2 = "(rev pvs @ vs, ls\<^sub>2, C,M,?pc\<^sub>2,ics)#frs"
    let ?\<sigma>\<^sub>2 = "(None,h\<^sub>2,?frs\<^sub>2,sh\<^sub>2)"
    let ?xa = "addr_of_sys_xcpt IncompatibleClassChangeError"
    have "P\<^sub>1 \<turnstile>\<^sub>1 \<langle>es,(h\<^sub>1, ls\<^sub>1, sh\<^sub>1)\<rangle> [\<Rightarrow>] \<langle>map Val pvs,(h\<^sub>2, ls\<^sub>2, sh\<^sub>2)\<rangle>" by fact
    hence [simp]: "length es = length pvs" by(auto dest:evals\<^sub>1_preserves_elen)
    obtain body' where method: "P \<turnstile> C' sees M', NonStatic :  Ts\<rightarrow>T = body' in D"
      by (metis SCallNonStatic\<^sub>1.hyps(3) P_def compP\<^sub>2_def sees_method_compP)
    have IH_es: "PROP ?Ps es h\<^sub>1 ls\<^sub>1 sh\<^sub>1 (map Val pvs) h\<^sub>2 ls\<^sub>2 sh\<^sub>2 C M pc ics pvs xa
                      (map Val pvs) vs frs I" by fact
    have "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> ?\<sigma>\<^sub>2" using IH_es SCallNonStatic\<^sub>1.prems nclinit by auto fastforce+
    also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M ?xa h\<^sub>2 (rev pvs@vs) ls\<^sub>2 ?pc\<^sub>2 ics frs sh\<^sub>2"
      using SCallNonStatic\<^sub>1.prems method nclinit
       by(cases "method P C' M'", cases "find_handler P ?xa h\<^sub>2 frs sh\<^sub>2")
         (auto simp: handle_def; meson frames_of.cases)
    finally show ?thesis using nclinit by (auto intro: exI[where x = ?pc\<^sub>2])
  qed
next
  case (SCallInitThrow\<^sub>1 es h\<^sub>0 ls\<^sub>0 sh\<^sub>0 pvs h\<^sub>1 ls\<^sub>1 sh\<^sub>1 C' M' Ts T body D a h\<^sub>2 ls\<^sub>2 sh\<^sub>2)
  show ?case
  proof(cases "M' = clinit \<and> es = []")
    case clinit: True then show ?thesis using SCallInitThrow\<^sub>1 by simp
  next
    case nclinit: False
    let ?\<sigma>\<^sub>0 = "(None,h\<^sub>0,(vs, ls\<^sub>0, C,M,pc,ics)#frs,sh\<^sub>0)"
    let ?pc\<^sub>1 = "pc + length(compEs\<^sub>2 es)"
    let ?frs\<^sub>1 = "(rev pvs @ vs, ls\<^sub>1, C,M,?pc\<^sub>1,ics)#frs"
    let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,?frs\<^sub>1,sh\<^sub>1)"
    let ?frs\<^sub>1' = "(rev pvs@vs,ls\<^sub>1,C,M,?pc\<^sub>1,Calling D [])#frs"
    let ?\<sigma>\<^sub>1' = "(None,h\<^sub>1,?frs\<^sub>1',sh\<^sub>1)"
    let ?frs\<^sub>2 = "(rev pvs@vs,ls\<^sub>1,C,M,?pc\<^sub>1,Called [])#frs"
    let ?\<sigma>\<^sub>2 = "(None,h\<^sub>2,?frs\<^sub>2,sh\<^sub>2)"
    have ls: "ls\<^sub>1 = ls\<^sub>2" by(rule init\<^sub>1_same_loc[OF SCallInitThrow\<^sub>1.hyps(6)])
    have method: "\<exists>m'. P \<turnstile> C' sees M',Static:Ts\<rightarrow>T = m' in D" using SCallInitThrow\<^sub>1.hyps(3)
      by (metis P_def compP\<^sub>2_def sees_method_compP)
    obtain a' where throw: "throw a = Throw a'" using eval\<^sub>1_final[OF SCallInitThrow\<^sub>1.hyps(6)] by clarsimp
    have "Ex (WTrt2\<^sub>1 P\<^sub>1 E h\<^sub>1 sh\<^sub>1 (INIT D ([D],False) \<leftarrow> unit))"
      using sees_method_is_class'[OF SCallInitThrow\<^sub>1.hyps(3)] by auto
    then obtain err' where pcs':
      "Jcc_pieces P\<^sub>1 E C M h\<^sub>1 (rev pvs@vs) ls\<^sub>1 ?pc\<^sub>1 ics frs sh\<^sub>1 I h\<^sub>2 ls\<^sub>2 sh\<^sub>2 v xa (INIT D ([D],False) \<leftarrow> unit)
      = (True, ?frs\<^sub>1', (None,h\<^sub>2,?frs\<^sub>2,sh\<^sub>2), err')"
      using SCallInitThrow\<^sub>1.prems(1) nclinit by auto
    have IHI: "PROP ?P (INIT D ([D],False) \<leftarrow> unit) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 (throw a)
               h\<^sub>2 ls\<^sub>2 sh\<^sub>2 E C M ?pc\<^sub>1 ics v a' (rev pvs@vs) frs I" by fact
    have IH_es: "PROP ?Ps es h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (map Val pvs) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 C M pc ics pvs xa
                      (map Val pvs) vs frs I" by fact
    have "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>1" using IH_es SCallInitThrow\<^sub>1.prems nclinit by auto fastforce+
    also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^sub>1'"
    proof(cases "sh\<^sub>1 D")
      case None then show ?thesis using SCallInitThrow\<^sub>1.hyps(1,3-6) SCallInitThrow\<^sub>1.prems method
        by(cases ics) auto
    next
      case (Some a)
      then obtain sfs i where "a = (sfs,i)" by(cases a)
      then show ?thesis using SCallInitThrow\<^sub>1.hyps(1,3-6) SCallInitThrow\<^sub>1.prems method Some
        by(cases ics; case_tac i, auto)
    qed
    also obtain vs' where "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M a' h\<^sub>2 (vs'@rev pvs@vs) ls\<^sub>1 ?pc\<^sub>1 ics frs sh\<^sub>2"
      using IHI pcs' throw by auto
    finally show ?thesis using nclinit throw ls
     by(auto intro!: exI[where x="?pc\<^sub>1"] exI[where x="vs'@rev pvs"])
  qed
next
  case (SCallInit\<^sub>1 es h\<^sub>0 ls\<^sub>0 sh\<^sub>0 pvs h\<^sub>1 ls\<^sub>1 sh\<^sub>1 C' M' Ts T body D v' h\<^sub>2 ls\<^sub>2 sh\<^sub>2 ls\<^sub>2' e' h\<^sub>3 ls\<^sub>3 sh\<^sub>3)
  show ?case
  proof(cases "M' = clinit \<and> es = []")
    case clinit: True then show ?thesis using SCallInit\<^sub>1 by simp
  next
    case nclinit: False
    let ?\<sigma>\<^sub>0 = "(None,h\<^sub>0,(vs, ls\<^sub>0, C,M,pc,ics)#frs,sh\<^sub>0)"
    let ?pc\<^sub>1 = "pc + length(compEs\<^sub>2 es)"
    let ?frs\<^sub>1 = "(rev pvs @ vs, ls\<^sub>1, C,M,?pc\<^sub>1,ics)#frs"
    let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,?frs\<^sub>1,sh\<^sub>1)"
    let ?frs\<^sub>1' = "(rev pvs@vs,ls\<^sub>1,C,M,?pc\<^sub>1,Calling D [])#frs"
    let ?\<sigma>\<^sub>1' = "(None,h\<^sub>1,?frs\<^sub>1',sh\<^sub>1)"
    let ?frs\<^sub>2 = "(rev pvs@vs,ls\<^sub>1,C,M,?pc\<^sub>1,Called [])#frs"
    let ?\<sigma>\<^sub>2 = "(None,h\<^sub>2,?frs\<^sub>2,sh\<^sub>2)"
    let ?frs\<^sub>2' = "([], ls\<^sub>2', D,M',0,No_ics) # ?frs\<^sub>1"
    let ?\<sigma>\<^sub>2' = "(None, h\<^sub>2, ?frs\<^sub>2', sh\<^sub>2)"
    have nclinit': "M' \<noteq> clinit" by fact
    have ics: "ics = No_ics" using SCallInit\<^sub>1.hyps(5) SCallInit\<^sub>1.prems by simp
    have "P\<^sub>1 \<turnstile>\<^sub>1 \<langle>es,(h\<^sub>0, ls\<^sub>0, sh\<^sub>0)\<rangle> [\<Rightarrow>] \<langle>map Val pvs,(h\<^sub>1, ls\<^sub>1, sh\<^sub>1)\<rangle>" by fact
    hence [simp]: "length es = length pvs" by(auto dest:evals\<^sub>1_preserves_elen)
    have invoke: "P,C,M,?pc\<^sub>1 \<triangleright> Invokestatic C' M' (length Ts)"
      using SCallInit\<^sub>1.hyps(8) SCallInit\<^sub>1.prems nclinit by(auto simp: add.assoc)
    have nsub: "\<not> sub_RI body" by(rule sees_wf\<^sub>1_nsub_RI[OF wf SCallInit\<^sub>1.hyps(3)])
    have ls: "ls\<^sub>1 = ls\<^sub>2" by(rule init\<^sub>1_same_loc[OF SCallInit\<^sub>1.hyps(6)])
    obtain sfs i where sh\<^sub>2: "sh\<^sub>2 D = Some(sfs,i)"
      using init\<^sub>1_Val_PD[OF SCallInit\<^sub>1.hyps(6)] by clarsimp
    have method: "\<exists>m'. P \<turnstile> C' sees M',Static:Ts\<rightarrow>T = m' in D" using SCallInit\<^sub>1.hyps(3)
      by (metis P_def compP\<^sub>2_def sees_method_compP)
    have "Ex (WTrt2\<^sub>1 P\<^sub>1 E h\<^sub>1 sh\<^sub>1 (INIT D ([D],False) \<leftarrow> unit))"
      using sees_method_is_class'[OF SCallInit\<^sub>1.hyps(3)] by auto
    then obtain err' where pcs':
      "Jcc_pieces P\<^sub>1 E C M h\<^sub>1 (rev pvs@vs) ls\<^sub>1 ?pc\<^sub>1 ics frs sh\<^sub>1 I h\<^sub>2 ls\<^sub>2 sh\<^sub>2 v' xa (INIT D ([D],False) \<leftarrow> unit)
      = (True, ?frs\<^sub>1', (None,h\<^sub>2,?frs\<^sub>2,sh\<^sub>2), err')"
      using SCallInit\<^sub>1.prems(1) nclinit by auto
    have IHI: "PROP ?P (INIT D ([D],False) \<leftarrow> unit) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 (Val v')
               h\<^sub>2 ls\<^sub>2 sh\<^sub>2 E C M ?pc\<^sub>1 ics v' xa (rev pvs@vs) frs I" by fact
    have IH_es: "PROP ?Ps es h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (map Val pvs) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 C M pc ics pvs xa
                      (map Val pvs) vs frs I" by fact
    have "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>1" using IH_es SCallInit\<^sub>1.prems nclinit by auto fastforce+
    also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^sub>1'"
    proof(cases "sh\<^sub>1 D")
      case None then show ?thesis using SCallInit\<^sub>1.hyps(1,3-6,8-10) SCallInit\<^sub>1.prems method
        by(cases ics) auto
    next
      case (Some a)
      then obtain sfs i where "a = (sfs,i)" by(cases a)
      then show ?thesis using SCallInit\<^sub>1.hyps(1,3-6,8-10) SCallInit\<^sub>1.prems method Some
        by(cases ics; case_tac i, auto)
    qed
    also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^sub>2" using IHI pcs' by auto
    also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^sub>2'"
      using jvm_Invokestatic_Called[OF assms(1) invoke _ SCallInit\<^sub>1.hyps(3,8,9)] sh\<^sub>2 ics by auto
    finally have 1: "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>2'".
    have "P\<^sub>1 \<turnstile> C' sees M',Static: Ts\<rightarrow>T = body in D" by fact
    then have M'_in_D: "P\<^sub>1 \<turnstile> D sees M',Static: Ts\<rightarrow>T = body in D"
      by(rule sees_method_idemp) 
    have M'_code: "compP\<^sub>2 P\<^sub>1,D,M',0 \<rhd> compE\<^sub>2 body @ [Return]" using beforeM M'_in_D by simp
    have M'_xtab: "compP\<^sub>2 P\<^sub>1,D,M' \<rhd> compxE\<^sub>2 body 0 0/{..<size(compE\<^sub>2 body)},0"
      using M'_in_D by(rule beforexM)
    have IH_body: "PROP ?P body h\<^sub>2 ls\<^sub>2' sh\<^sub>2 e' h\<^sub>3 ls\<^sub>3 sh\<^sub>3 (Class D # Ts) D M' 0 No_ics v xa [] ?frs\<^sub>1
      ({..<size(compE\<^sub>2 body)})" by fact
    have cond: "Jcc_cond P\<^sub>1 (Class D # Ts) D M' [] 0 No_ics {..<length (compE\<^sub>2 body)} h\<^sub>2 sh\<^sub>2 body"
      using nsub_RI_Jcc_pieces[OF assms(1) nsub] M'_code M'_xtab by clarsimp
    show ?thesis (is "?Norm \<and> ?Err")
    proof
      show ?Norm (is "?val \<longrightarrow> ?trans")
      proof
        assume val: ?val
        note 1
        also have "P \<turnstile> ?\<sigma>\<^sub>2' -jvm\<rightarrow> (None,h\<^sub>3,([v],ls\<^sub>3,D,M',size(compE\<^sub>2 body),No_ics)#?frs\<^sub>1,sh\<^sub>3)"
          using val IH_body SCallInit\<^sub>1.prems M'_code cond nsub_RI_Jcc_pieces nsub by auto
        also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None, h\<^sub>3, (v#vs, ls\<^sub>2, C,M,?pc\<^sub>1+1,ics)#frs,sh\<^sub>3)"
          using SCallInit\<^sub>1.hyps(8) M'_code M'_in_D ls nclinit' by(cases T, auto)
        finally show ?trans using nclinit by(auto simp:add.assoc)
      qed
    next
      show ?Err (is "?throw \<longrightarrow> ?err")
      proof
        assume throw: ?throw
        with IH_body obtain pc\<^sub>2 vs' where
          pc\<^sub>2: "0 \<le> pc\<^sub>2 \<and> pc\<^sub>2 < size(compE\<^sub>2 body) \<and>
                \<not> caught P pc\<^sub>2 h\<^sub>3 xa (compxE\<^sub>2 body 0 0)" and
          2: "P \<turnstile> ?\<sigma>\<^sub>2' -jvm\<rightarrow> handle P D M' xa h\<^sub>3 vs' ls\<^sub>3 pc\<^sub>2 No_ics ?frs\<^sub>1 sh\<^sub>3"
          using SCallInit\<^sub>1.prems M'_code M'_xtab cond nsub_RI_Jcc_pieces nsub
           by (auto simp del:split_paired_Ex)
        have "handle P D M' xa h\<^sub>3 vs' ls\<^sub>3 pc\<^sub>2 No_ics ?frs\<^sub>1 sh\<^sub>3 =
              handle P C M xa h\<^sub>3 (rev pvs @ vs) ls\<^sub>2 ?pc\<^sub>1 ics frs sh\<^sub>3"
          using pc\<^sub>2 M'_in_D ls nclinit' by(auto simp add:handle_def)
        then show "?err" using pc\<^sub>2 jvm_trans[OF 1 2] nclinit
         by(auto intro!:exI[where x="?pc\<^sub>1"] exI[where x="rev pvs"])
      qed
    qed
  qed
next
  case (SCall\<^sub>1 es h\<^sub>1 ls\<^sub>1 sh\<^sub>1 pvs h\<^sub>2 ls\<^sub>2 sh\<^sub>2 C' M' Ts T body D sfs ls\<^sub>2' e' h\<^sub>3 ls\<^sub>3 sh\<^sub>3)
  show ?case
  proof(cases "M' = clinit \<and> es = []")
    case clinit: True
    then have s1: "pvs = []" "h\<^sub>1 = h\<^sub>2" "ls\<^sub>1 = ls\<^sub>2" "sh\<^sub>1 = sh\<^sub>2"
      using SCall\<^sub>1.hyps(1) evals\<^sub>1_cases(1) by blast+
    then have ls\<^sub>2': "ls\<^sub>2' = replicate (max_vars body) undefined" using SCall\<^sub>1.hyps(6) clinit by simp
    let ?frs = "create_init_frame P C' # (vs, ls\<^sub>1, C,M,pc,ics)#frs"
    let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,?frs,sh\<^sub>1)"
    have method: "P\<^sub>1 \<turnstile> C' sees clinit,Static: []\<rightarrow>Void = body in C'"
      using SCall\<^sub>1.hyps(3) clinit s1(1) wf_sees_clinit[OF wf]
        by (metis is_class_def option.collapse sees_method_fun sees_method_is_class)
    then have M_code: "compP\<^sub>2 P\<^sub>1,C',clinit,0 \<rhd> compE\<^sub>2 body @ [Return]" by(rule beforeM)
    have pcs: "Jcc_pieces P\<^sub>1 E C M h\<^sub>1 vs ls\<^sub>1 pc ics frs sh\<^sub>1 I h\<^sub>3 ls\<^sub>2 sh\<^sub>3 v xa (C'\<bullet>\<^sub>sclinit([]))
         = (True, ?frs, (None, h\<^sub>3, tl ?frs, sh\<^sub>3(C'\<mapsto>(fst(the(sh\<^sub>3 C')),Done))),
        P \<turnstile> (None, h\<^sub>1, ?frs, sh\<^sub>1) -jvm\<rightarrow>
        (case ics of
     Called Cs \<Rightarrow> (None, h\<^sub>3, (vs, ls\<^sub>1, C, M, pc, Throwing Cs xa) # frs, sh\<^sub>3(C' \<mapsto> (fst (the (sh\<^sub>3 C')), Error)))))"
      using Jcc_pieces_clinit[OF assms(1),of E C M vs pc ics I h\<^sub>1 sh\<^sub>1 C' ls\<^sub>1 frs h\<^sub>3 ls\<^sub>2 sh\<^sub>3 v xa]
         SCall\<^sub>1.prems(1) clinit s1(1) by clarsimp
    have IH_body: "PROP ?P body h\<^sub>2 ls\<^sub>2' sh\<^sub>2 e' h\<^sub>3 ls\<^sub>3 sh\<^sub>3 [] C' clinit 0 No_ics v xa [] (tl ?frs)
     ({..<size(compE\<^sub>2 body)})" by fact
    show ?thesis (is "?Norm \<and> ?Err")
    proof
      show ?Norm (is "?val \<longrightarrow> ?trans")
      proof
        assume val: ?val
        then have "P \<turnstile> ?\<sigma>\<^sub>1
           -jvm\<rightarrow> (None, h\<^sub>3, ([v], ls\<^sub>3, C', clinit, size(compE\<^sub>2 body), No_ics) # tl ?frs,sh\<^sub>3)"
          using IH_body Jcc_pieces_SCall_clinit_body[OF assms(1) wf pcs method] s1 ls\<^sub>2' by clarsimp
        also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None, h\<^sub>3, tl ?frs, sh\<^sub>3(C'\<mapsto>(fst(the(sh\<^sub>3 C')),Done)))"
          using jvm_Return_Init[OF M_code] by simp
        finally show ?trans using pcs s1 clinit by simp
      qed
    next
      show ?Err (is "?throw \<longrightarrow> ?err")
      proof
        assume throw: ?throw
        with IH_body obtain pc\<^sub>2 vs2 where
          pc\<^sub>2: "0 \<le> pc\<^sub>2 \<and> pc\<^sub>2 < size(compE\<^sub>2 body) \<and>
                \<not> caught P pc\<^sub>2 h\<^sub>3 xa (compxE\<^sub>2 body 0 0)" and
          2: "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> handle P C' clinit xa h\<^sub>3 vs2 ls\<^sub>3 pc\<^sub>2 No_ics (tl ?frs) sh\<^sub>3"
          using SCall\<^sub>1.prems Jcc_pieces_SCall_clinit_body[OF assms(1) wf pcs method] s1 ls\<^sub>2' by clarsimp
        show ?err using SCall\<^sub>1.prems(1) clinit
        proof(cases ics)
          case (Called Cs)
          note 2
          also have "handle P C' clinit xa h\<^sub>3 vs2 ls\<^sub>3 pc\<^sub>2 No_ics (tl ?frs) sh\<^sub>3
             = (None, h\<^sub>3, (vs, ls\<^sub>1, C, M, pc, Throwing (C'#Cs) xa) # frs, sh\<^sub>3)"
            using Called pc\<^sub>2 method by(simp add: handle_def)
          also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None, h\<^sub>3, (vs, ls\<^sub>1, C, M, pc, Throwing Cs xa) # frs,
             sh\<^sub>3(C' \<mapsto> (fst (the (sh\<^sub>3 C')), Error)))" using Called jvm_Throwing by simp
          finally show ?thesis using pcs clinit Called by(clarsimp intro!: exI[where x="[]"])
        qed(auto)
      qed
    qed
  next
    case nclinit: False
    let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,(vs, ls\<^sub>1, C,M,pc,ics)#frs,sh\<^sub>1)"
    let ?pc\<^sub>2 = "pc + length(compEs\<^sub>2 es)"
    let ?frs\<^sub>2 = "(rev pvs @ vs, ls\<^sub>2, C,M,?pc\<^sub>2,ics)#frs"
    let ?\<sigma>\<^sub>2 = "(None,h\<^sub>2,?frs\<^sub>2,sh\<^sub>2)"
    let ?frs\<^sub>2' = "([], ls\<^sub>2', D,M',0,No_ics) # ?frs\<^sub>2"
    let ?\<sigma>\<^sub>2' = "(None, h\<^sub>2, ?frs\<^sub>2', sh\<^sub>2)"
    have nclinit': "M' \<noteq> clinit"
     using wf_sees_clinit1[OF wf] visible_method_exists[OF SCall\<^sub>1.hyps(3)]
       sees_method_idemp[OF SCall\<^sub>1.hyps(3)] nclinit SCall\<^sub>1.hyps(5)
       evals\<^sub>1_preserves_elen[OF SCall\<^sub>1.hyps(1)] by fastforce
    have "P\<^sub>1 \<turnstile>\<^sub>1 \<langle>es,(h\<^sub>1, ls\<^sub>1, sh\<^sub>1)\<rangle> [\<Rightarrow>] \<langle>map Val pvs,(h\<^sub>2, ls\<^sub>2, sh\<^sub>2)\<rangle>" by fact
    hence [simp]: "length es = length pvs" by(auto dest:evals\<^sub>1_preserves_elen)
    have invoke: "P,C,M,?pc\<^sub>2 \<triangleright> Invokestatic C' M' (length Ts)"
      using SCall\<^sub>1.hyps(5) SCall\<^sub>1.prems nclinit by(auto simp: add.assoc)
    have nsub: "\<not> sub_RI body" by(rule sees_wf\<^sub>1_nsub_RI[OF wf SCall\<^sub>1.hyps(3)])
    have IH_es: "PROP ?Ps es h\<^sub>1 ls\<^sub>1 sh\<^sub>1 (map Val pvs) h\<^sub>2 ls\<^sub>2 sh\<^sub>2 C M pc ics pvs xa
                      (map Val pvs) vs frs I" by fact
    have "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> ?\<sigma>\<^sub>2" using IH_es SCall\<^sub>1.prems nclinit by auto fastforce+
    also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^sub>2'" using jvm_Invokestatic[OF assms(1) invoke _ SCall\<^sub>1.hyps(3,5,6)]
         SCall\<^sub>1.hyps(4) SCall\<^sub>1.prems nclinit by auto
    finally have 1: "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> ?\<sigma>\<^sub>2'".
    have "P\<^sub>1 \<turnstile> C' sees M',Static: Ts\<rightarrow>T = body in D" by fact
    then have M'_in_D: "P\<^sub>1 \<turnstile> D sees M',Static: Ts\<rightarrow>T = body in D"
      by(rule sees_method_idemp) 
    have M'_code: "compP\<^sub>2 P\<^sub>1,D,M',0 \<rhd> compE\<^sub>2 body @ [Return]" using beforeM M'_in_D by simp
    have M'_xtab: "compP\<^sub>2 P\<^sub>1,D,M' \<rhd> compxE\<^sub>2 body 0 0/{..<size(compE\<^sub>2 body)},0"
      using M'_in_D by(rule beforexM)
    have IH_body: "PROP ?P body h\<^sub>2 ls\<^sub>2' sh\<^sub>2 e' h\<^sub>3 ls\<^sub>3 sh\<^sub>3 (Class D # Ts) D M' 0 No_ics v xa [] ?frs\<^sub>2
      ({..<size(compE\<^sub>2 body)})" by fact
    have cond: "Jcc_cond P\<^sub>1 (Class D # Ts) D M' [] 0 No_ics {..<length (compE\<^sub>2 body)} h\<^sub>2 sh\<^sub>2 body"
      using nsub_RI_Jcc_pieces[OF assms(1) nsub] M'_code M'_xtab by clarsimp
    show ?thesis (is "?Norm \<and> ?Err")
    proof
      show ?Norm (is "?val \<longrightarrow> ?trans")
      proof
        assume val: ?val
        note 1
        also have "P \<turnstile> ?\<sigma>\<^sub>2' -jvm\<rightarrow> (None,h\<^sub>3,([v],ls\<^sub>3,D,M',size(compE\<^sub>2 body),No_ics)#?frs\<^sub>2,sh\<^sub>3)"
          using val IH_body SCall\<^sub>1.prems M'_code cond nsub_RI_Jcc_pieces nsub by auto
        also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None, h\<^sub>3, (v#vs, ls\<^sub>2, C,M,?pc\<^sub>2+1,ics)#frs,sh\<^sub>3)"
          using SCall\<^sub>1.hyps(5) M'_code M'_in_D nclinit' by(cases T, auto)
        finally show ?trans using nclinit by(auto simp:add.assoc)
      qed
    next
      show ?Err (is "?throw \<longrightarrow> ?err")
      proof
        assume throw: ?throw
        with IH_body obtain pc\<^sub>2 vs' where
          pc\<^sub>2: "0 \<le> pc\<^sub>2 \<and> pc\<^sub>2 < size(compE\<^sub>2 body) \<and>
                \<not> caught P pc\<^sub>2 h\<^sub>3 xa (compxE\<^sub>2 body 0 0)" and
          2: "P \<turnstile> ?\<sigma>\<^sub>2' -jvm\<rightarrow> handle P D M' xa h\<^sub>3 vs' ls\<^sub>3 pc\<^sub>2 No_ics ?frs\<^sub>2 sh\<^sub>3"
          using SCall\<^sub>1.prems M'_code M'_xtab cond nsub_RI_Jcc_pieces nsub
           by (auto simp del:split_paired_Ex)
        have "handle P D M' xa h\<^sub>3 vs' ls\<^sub>3 pc\<^sub>2 No_ics ?frs\<^sub>2 sh\<^sub>3 =
              handle P C M xa h\<^sub>3 (rev pvs @ vs) ls\<^sub>2 ?pc\<^sub>2 ics frs sh\<^sub>3"
          using pc\<^sub>2 M'_in_D nclinit' by(auto simp add:handle_def)
        then show "?err" using pc\<^sub>2 jvm_trans[OF 1 2] nclinit by(auto intro:exI[where x="?pc\<^sub>2"])
      qed
    qed
  qed
next
  case Block\<^sub>1 then show ?case using nsub_RI_Jcc_pieces by auto
next
  case (Seq\<^sub>1 e\<^sub>1 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 w h\<^sub>1 ls\<^sub>1 sh\<^sub>1 e\<^sub>2 e\<^sub>2' h\<^sub>2 ls\<^sub>2 sh\<^sub>2)
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e\<^sub>1)"
  let ?\<sigma>\<^sub>0 = "(None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc,ics)#frs,sh\<^sub>0)"
  let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,(vs,ls\<^sub>1,C,M,?pc\<^sub>1+1,ics)#frs,sh\<^sub>1)"
  let ?I = "I - pcs (compxE\<^sub>2 e\<^sub>2 (Suc ?pc\<^sub>1) (length vs))"
  have Isub: "{pc..<pc + length (compE\<^sub>2 e\<^sub>1)} \<subseteq> ?I" using Seq\<^sub>1.prems by clarsimp
  have IH: "PROP ?P e\<^sub>1 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (Val w) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics w xa vs frs ?I" by fact
  have "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> (None,h\<^sub>1,(w#vs,ls\<^sub>1,C,M,?pc\<^sub>1,ics)#frs,sh\<^sub>1)"
    using Seq\<^sub>1.prems nsub_RI_Jcc_pieces IH Isub by auto
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^sub>1" using Seq\<^sub>1 by auto
  finally have eval\<^sub>1: "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>1".
  let ?pc\<^sub>2 = "?pc\<^sub>1 + 1 + length(compE\<^sub>2 e\<^sub>2)"
  let ?I' = "I - pcs(compxE\<^sub>2 e\<^sub>1 pc (size vs))"
  have IH\<^sub>2: "PROP ?P e\<^sub>2 h\<^sub>1 ls\<^sub>1 sh\<^sub>1 e\<^sub>2' h\<^sub>2 ls\<^sub>2 sh\<^sub>2 E C M (?pc\<^sub>1+1) ics v xa vs frs
                     ?I'" by fact
  have Isub2: "{Suc (pc + length (compE\<^sub>2 e\<^sub>1))..<Suc (pc + length (compE\<^sub>2 e\<^sub>1) + length (compE\<^sub>2 e\<^sub>2))}
     \<subseteq> ?I'" using Seq\<^sub>1.prems by clarsimp
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm (is "?val \<longrightarrow> ?trans")
    proof
      assume val: ?val
      note eval\<^sub>1
      also have "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> (None,h\<^sub>2,(v#vs,ls\<^sub>2,C,M,?pc\<^sub>2,ics)#frs,sh\<^sub>2)"
        using val Seq\<^sub>1.prems nsub_RI_Jcc_pieces IH\<^sub>2 Isub2 by auto
      finally show ?trans by(simp add:add.assoc)
    qed
  next
    show ?Err (is "?throw \<longrightarrow> ?err")
    proof
      assume throw: ?throw
      then obtain pc\<^sub>2 vs' where
        pc\<^sub>2: "?pc\<^sub>1+1 \<le> pc\<^sub>2 \<and> pc\<^sub>2 < ?pc\<^sub>2 \<and>
              \<not> caught P pc\<^sub>2 h\<^sub>2 xa (compxE\<^sub>2 e\<^sub>2 (?pc\<^sub>1+1) (size vs))" and
        eval\<^sub>2: "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> handle P C M xa h\<^sub>2 (vs'@vs) ls\<^sub>2 pc\<^sub>2 ics frs sh\<^sub>2"
        using IH\<^sub>2 Seq\<^sub>1.prems nsub_RI_Jcc_pieces Isub2 by auto
      show "?err" using pc\<^sub>2 jvm_trans[OF eval\<^sub>1 eval\<^sub>2] by(auto intro: exI[where x=pc\<^sub>2])
    qed
  qed
next
  case (SeqThrow\<^sub>1 e\<^sub>0 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 e h\<^sub>1 ls\<^sub>1 sh\<^sub>1 e\<^sub>1)
  let ?I = "I - pcs (compxE\<^sub>2 e\<^sub>1 (Suc (pc + length (compE\<^sub>2 e\<^sub>0))) (length vs))"
  obtain a' where throw: "throw e = Throw a'" using eval\<^sub>1_final[OF SeqThrow\<^sub>1.hyps(1)] by clarsimp
  have Isub: "{pc..<pc + length (compE\<^sub>2 e\<^sub>0)} \<subseteq> ?I" using SeqThrow\<^sub>1.prems by clarsimp
  have "PROP ?P e\<^sub>0 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (throw e) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics v a' vs frs ?I" by fact
  then show ?case using SeqThrow\<^sub>1.prems throw nsub_RI_Jcc_pieces Isub by auto
next
  case (CondT\<^sub>1 e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 h\<^sub>1 ls\<^sub>1 sh\<^sub>1 e\<^sub>1 e' h\<^sub>2 ls\<^sub>2 sh\<^sub>2 e\<^sub>2)
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e)"
  let ?\<sigma>\<^sub>0 = "(None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc,ics)#frs,sh\<^sub>0)"
  let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,(vs,ls\<^sub>1,C,M,?pc\<^sub>1+1,ics)#frs,sh\<^sub>1)"
  let ?d = "size vs"
  let ?xt\<^sub>1 = "compxE\<^sub>2 e\<^sub>1 (pc+size(compE\<^sub>2 e)+1) ?d"
  let ?xt\<^sub>2 = "compxE\<^sub>2 e\<^sub>2 (pc+size(compE\<^sub>2 e)+size(compE\<^sub>2 e\<^sub>1)+2) ?d"
  let ?I = "I - (pcs ?xt\<^sub>1 \<union> pcs ?xt\<^sub>2)"
  have Isub: "{pc..<pc + length (compE\<^sub>2 e)} \<subseteq> ?I" using CondT\<^sub>1.prems by clarsimp
  have IH: "PROP ?P e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 true h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics (Bool True) xa vs frs ?I" by fact
  have "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> (None,h\<^sub>1,(Bool(True)#vs,ls\<^sub>1,C,M,?pc\<^sub>1,ics)#frs,sh\<^sub>1)"
    using CondT\<^sub>1.prems nsub_RI_Jcc_pieces IH Isub by(auto simp: Int_Un_distrib)
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^sub>1" using CondT\<^sub>1 by auto
  finally have eval\<^sub>1: "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>1".
  let ?pc\<^sub>1' = "?pc\<^sub>1 + 1 + length(compE\<^sub>2 e\<^sub>1)"
  let ?pc\<^sub>2' = "?pc\<^sub>1' + 1 + length(compE\<^sub>2 e\<^sub>2)"
  let ?I' = "I - pcs(compxE\<^sub>2 e pc ?d) - pcs(compxE\<^sub>2 e\<^sub>2 (?pc\<^sub>1'+1) ?d)"
  have IH2: "PROP ?P e\<^sub>1 h\<^sub>1 ls\<^sub>1 sh\<^sub>1 e' h\<^sub>2 ls\<^sub>2 sh\<^sub>2 E C M (?pc\<^sub>1+1) ics v xa vs frs ?I'" by fact
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm (is "?val \<longrightarrow> ?trans")
    proof
      assume val: ?val
      note eval\<^sub>1
      also have "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> (None,h\<^sub>2,(v#vs,ls\<^sub>2,C,M,?pc\<^sub>1',ics)#frs,sh\<^sub>2)"
        using val CondT\<^sub>1.prems nsub_RI_Jcc_pieces IH2 by(fastforce simp:Int_Un_distrib)
      also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>2,(v#vs,ls\<^sub>2,C,M,?pc\<^sub>2',ics)#frs,sh\<^sub>2)"
        using CondT\<^sub>1 nsub_RI_Jcc_pieces by(auto simp:add.assoc)
      finally show ?trans by(simp add:add.assoc)
    qed
  next
    show ?Err (is "?throw \<longrightarrow> ?err")
    proof
      assume throw: ?throw
      moreover
      note IH2
      ultimately obtain pc\<^sub>2 vs' where
        pc\<^sub>2: "?pc\<^sub>1+1 \<le> pc\<^sub>2 \<and> pc\<^sub>2 < ?pc\<^sub>1' \<and>
              \<not> caught P pc\<^sub>2 h\<^sub>2 xa (compxE\<^sub>2 e\<^sub>1 (?pc\<^sub>1+1) (size vs))" and
        eval\<^sub>2: "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> handle P C M xa h\<^sub>2 (vs'@vs) ls\<^sub>2 pc\<^sub>2 ics frs sh\<^sub>2"
        using CondT\<^sub>1.prems nsub_RI_Jcc_pieces by (fastforce simp:Int_Un_distrib)
      show "?err" using pc\<^sub>2 jvm_trans[OF eval\<^sub>1 eval\<^sub>2] by(auto intro: exI[where x=pc\<^sub>2])
    qed
  qed
next
  case (CondF\<^sub>1 e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 h\<^sub>1 ls\<^sub>1 sh\<^sub>1 e\<^sub>2 e' h\<^sub>2 ls\<^sub>2 sh\<^sub>2 e\<^sub>1)
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e)"
  let ?pc\<^sub>2 = "?pc\<^sub>1 + 1 + length(compE\<^sub>2 e\<^sub>1)+ 1"
  let ?pc\<^sub>2' = "?pc\<^sub>2 + length(compE\<^sub>2 e\<^sub>2)"
  let ?\<sigma>\<^sub>0 = "(None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc,ics)#frs,sh\<^sub>0)"
  let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,(vs,ls\<^sub>1,C,M,?pc\<^sub>2,ics)#frs,sh\<^sub>1)"
  let ?d = "size vs"
  let ?xt\<^sub>1 = "compxE\<^sub>2 e\<^sub>1 (pc+size(compE\<^sub>2 e)+1) ?d"
  let ?xt\<^sub>2 = "compxE\<^sub>2 e\<^sub>2 (pc+size(compE\<^sub>2 e)+size(compE\<^sub>2 e\<^sub>1)+2) ?d"
  let ?I = "I - (pcs ?xt\<^sub>1 \<union> pcs ?xt\<^sub>2)"
  let ?I' = "I - pcs(compxE\<^sub>2 e pc ?d) - pcs(compxE\<^sub>2 e\<^sub>1 (?pc\<^sub>1+1) ?d)"
  have pcs: "pcs(compxE\<^sub>2 e pc ?d) \<inter> pcs(?xt\<^sub>1 @ ?xt\<^sub>2) = {}"
    using CondF\<^sub>1.prems by (simp add:Int_Un_distrib)
  have Isub: "{pc..<pc + length (compE\<^sub>2 e)} \<subseteq> ?I" using CondF\<^sub>1.prems by clarsimp
  have IH: "PROP ?P e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 false h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics (Bool False) xa vs frs ?I" by fact
  have IH2: "PROP ?P e\<^sub>2 h\<^sub>1 ls\<^sub>1 sh\<^sub>1 e' h\<^sub>2 ls\<^sub>2 sh\<^sub>2 E C M ?pc\<^sub>2 ics v xa vs frs ?I'" by fact
  have "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> (None,h\<^sub>1,(Bool(False)#vs,ls\<^sub>1,C,M,?pc\<^sub>1,ics)#frs,sh\<^sub>1)"
    using CondF\<^sub>1.prems nsub_RI_Jcc_pieces IH Isub pcs by auto
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^sub>1" using CondF\<^sub>1 by auto
  finally have eval\<^sub>1: "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>1".
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm (is "?val \<longrightarrow> ?trans")
    proof
      assume val: ?val
      note eval\<^sub>1
      also have "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> (None,h\<^sub>2,(v#vs,ls\<^sub>2,C,M,?pc\<^sub>2',ics)#frs,sh\<^sub>2)"
        using val CondF\<^sub>1.prems nsub_RI_Jcc_pieces IH2 by(fastforce simp:Int_Un_distrib)
      finally show ?trans by(simp add:add.assoc)
    qed
  next
    show ?Err (is "?throw \<longrightarrow> ?err")
    proof
      let ?I' = "I - pcs(compxE\<^sub>2 e pc ?d) - pcs(compxE\<^sub>2 e\<^sub>1 (?pc\<^sub>1+1) ?d)"
      assume throw: ?throw
      then obtain pc\<^sub>2 vs' where
        pc\<^sub>2: "?pc\<^sub>2 \<le> pc\<^sub>2 \<and> pc\<^sub>2 < ?pc\<^sub>2' \<and>
              \<not> caught P pc\<^sub>2 h\<^sub>2 xa (compxE\<^sub>2 e\<^sub>2 ?pc\<^sub>2 ?d)" and
        eval\<^sub>2: "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> handle P C M xa h\<^sub>2 (vs'@vs) ls\<^sub>2 pc\<^sub>2 ics frs sh\<^sub>2"
        using CondF\<^sub>1.prems nsub_RI_Jcc_pieces IH2 by(fastforce simp:Int_Un_distrib)
      show "?err" using pc\<^sub>2 jvm_trans[OF eval\<^sub>1 eval\<^sub>2] by(auto intro: exI[where x=pc\<^sub>2])
    qed
  qed
next
  case (CondThrow\<^sub>1 e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 f h\<^sub>1 ls\<^sub>1 sh\<^sub>1 e\<^sub>1 e\<^sub>2)
  let ?d = "size vs"
  let ?xt\<^sub>1 = "compxE\<^sub>2 e\<^sub>1 (pc+size(compE\<^sub>2 e)+1) ?d"
  let ?xt\<^sub>2 = "compxE\<^sub>2 e\<^sub>2 (pc+size(compE\<^sub>2 e)+size(compE\<^sub>2 e\<^sub>1)+2) ?d"
  let ?I = "I - (pcs ?xt\<^sub>1 \<union> pcs ?xt\<^sub>2)"
  have Isub: "{pc..<pc + length (compE\<^sub>2 e)} \<subseteq> ?I" using CondThrow\<^sub>1.prems by clarsimp
  have "pcs(compxE\<^sub>2 e pc ?d) \<inter> pcs(?xt\<^sub>1 @ ?xt\<^sub>2) = {}"
    using CondThrow\<^sub>1.prems by (simp add:Int_Un_distrib)
  moreover have "PROP ?P e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (throw f) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics v xa vs frs ?I" by fact
  ultimately show ?case using CondThrow\<^sub>1.prems nsub_RI_Jcc_pieces Isub by auto
next
  case (WhileF\<^sub>1 e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 h\<^sub>1 ls\<^sub>1 sh\<^sub>1 c)
  let ?pc = "pc + length(compE\<^sub>2 e)"
  let ?pc' = "?pc + length(compE\<^sub>2 c) + 3"
  have Isub: "{pc..<pc + length (compE\<^sub>2 e)} \<subseteq> I - pcs (compxE\<^sub>2 c (Suc (pc + length (compE\<^sub>2 e))) (length vs))"
    using WhileF\<^sub>1.prems by clarsimp
  have Isub2: "{Suc (pc + length (compE\<^sub>2 e))..<Suc (pc + length (compE\<^sub>2 e) + length (compE\<^sub>2 c))}
     \<subseteq> I - pcs (compxE\<^sub>2 e pc (length vs))" using WhileF\<^sub>1.prems by clarsimp
  have IH: "PROP ?P e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 false h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics (Bool False) xa vs frs
    (I - pcs (compxE\<^sub>2 c (Suc (pc + length (compE\<^sub>2 e))) (length vs)))" by fact
  have "P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc,ics)#frs,sh\<^sub>0) -jvm\<rightarrow>
            (None,h\<^sub>1,(Bool False#vs,ls\<^sub>1,C,M,?pc,ics)#frs,sh\<^sub>1)"
    using WhileF\<^sub>1.prems nsub_RI_Jcc_pieces IH Isub by auto
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>1,(vs,ls\<^sub>1,C,M,?pc',ics)#frs,sh\<^sub>1)"
    using WhileF\<^sub>1 by (auto simp:add.assoc)
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>1,(Unit#vs,ls\<^sub>1,C,M,?pc'+1,ics)#frs,sh\<^sub>1)"
    using WhileF\<^sub>1.prems by (auto simp:eval_nat_numeral)
  finally show ?case by (simp add:add.assoc eval_nat_numeral)
next
  case (WhileT\<^sub>1 e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 h\<^sub>1 ls\<^sub>1 sh\<^sub>1 c v\<^sub>1 h\<^sub>2 ls\<^sub>2 sh\<^sub>2 e\<^sub>3 h\<^sub>3 ls\<^sub>3 sh\<^sub>3)
  let ?pc = "pc + length(compE\<^sub>2 e)"
  let ?pc' = "?pc + length(compE\<^sub>2 c) + 1"
  let ?\<sigma>\<^sub>0 = "(None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc,ics)#frs,sh\<^sub>0)"
  let ?\<sigma>\<^sub>2 = "(None,h\<^sub>2,(vs,ls\<^sub>2,C,M,pc,ics)#frs,sh\<^sub>2)"
  have Isub: "{pc..<pc + length (compE\<^sub>2 e)} \<subseteq> I - pcs (compxE\<^sub>2 c (Suc (pc + length (compE\<^sub>2 e))) (length vs))"
    using WhileT\<^sub>1.prems by clarsimp
  have Isub2: "{Suc (pc + length (compE\<^sub>2 e))..<Suc (pc + length (compE\<^sub>2 e) + length (compE\<^sub>2 c))}
     \<subseteq> I - pcs (compxE\<^sub>2 e pc (length vs))" using WhileT\<^sub>1.prems by clarsimp
  have IH: "PROP ?P e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 true h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics (Bool True) xa vs frs
    (I - pcs (compxE\<^sub>2 c (Suc (pc + length (compE\<^sub>2 e))) (length vs)))" by fact
  have IH2: "PROP ?P c h\<^sub>1 ls\<^sub>1 sh\<^sub>1 (Val v\<^sub>1) h\<^sub>2 ls\<^sub>2 sh\<^sub>2 E C M (Suc ?pc) ics v\<^sub>1 xa vs frs
    (I - pcs (compxE\<^sub>2 e pc (length vs)))" by fact
  have "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> (None,h\<^sub>1,(Bool True#vs,ls\<^sub>1,C,M,?pc,ics)#frs,sh\<^sub>1)"
    using WhileT\<^sub>1.prems nsub_RI_Jcc_pieces IH Isub by auto
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>1,(vs,ls\<^sub>1,C,M,?pc+1,ics)#frs,sh\<^sub>1)"
    using WhileT\<^sub>1.prems by auto
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>2,(v\<^sub>1#vs,ls\<^sub>2,C,M,?pc',ics)#frs,sh\<^sub>2)"
    using WhileT\<^sub>1.prems nsub_RI_Jcc_pieces IH2 Isub2 by auto
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^sub>2" using WhileT\<^sub>1.prems by auto
  finally have 1: "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>2".
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm (is "?val \<longrightarrow> ?trans")
    proof
      assume val: ?val
      note 1
      also have "P \<turnstile> ?\<sigma>\<^sub>2 -jvm\<rightarrow> (None,h\<^sub>3,(v#vs,ls\<^sub>3,C,M,?pc'+3,ics)#frs,sh\<^sub>3)"
        using val WhileT\<^sub>1 by (auto simp add:add.assoc eval_nat_numeral)
      finally show ?trans by(simp add:add.assoc eval_nat_numeral)
    qed
  next
    show ?Err (is "?throw \<longrightarrow> ?err")
    proof
      assume throw: ?throw
      moreover
      have "PROP ?P (while (e) c) h\<^sub>2 ls\<^sub>2 sh\<^sub>2 e\<^sub>3 h\<^sub>3 ls\<^sub>3 sh\<^sub>3 E C M pc ics v xa vs frs I" by fact
      ultimately obtain pc\<^sub>2 vs' where
        pc\<^sub>2: "pc \<le> pc\<^sub>2 \<and> pc\<^sub>2 < ?pc'+3 \<and>
              \<not> caught P pc\<^sub>2 h\<^sub>3 xa (compxE\<^sub>2 (while (e) c) pc (size vs))" and
        2: "P \<turnstile> ?\<sigma>\<^sub>2 -jvm\<rightarrow> handle P C M xa h\<^sub>3 (vs'@vs) ls\<^sub>3 pc\<^sub>2 ics frs sh\<^sub>3"
        using WhileT\<^sub>1.prems by (auto simp:add.assoc eval_nat_numeral)
      show "?err" using pc\<^sub>2 jvm_trans[OF 1 2] by(auto intro: exI[where x=pc\<^sub>2])
    qed
  qed
next
  case (WhileCondThrow\<^sub>1 e h ls sh e' h' ls' sh' c)
  let ?I = "I - pcs (compxE\<^sub>2 c (Suc (pc + length (compE\<^sub>2 e))) (length vs))"
  obtain a' where throw: "throw e' = Throw a'" using eval\<^sub>1_final[OF WhileCondThrow\<^sub>1.hyps(1)] by clarsimp
  have Isub: "{pc..<pc + length (compE\<^sub>2 e)} \<subseteq> ?I" using WhileCondThrow\<^sub>1.prems by clarsimp
  have "PROP ?P e h ls sh (throw e') h' ls' sh' E C M pc ics v a' vs frs ?I" by fact
  then show ?case using WhileCondThrow\<^sub>1.prems throw nsub_RI_Jcc_pieces Isub by auto
next
  case (WhileBodyThrow\<^sub>1 e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 h\<^sub>1 ls\<^sub>1 sh\<^sub>1 c e' h\<^sub>2 ls\<^sub>2 sh\<^sub>2)
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e)"
  let ?\<sigma>\<^sub>0 = "(None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc,ics)#frs,sh\<^sub>0)"
  let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,(vs,ls\<^sub>1,C,M,?pc\<^sub>1+1,ics)#frs,sh\<^sub>1)"
  let ?I = "I - pcs (compxE\<^sub>2 c (Suc (pc + length (compE\<^sub>2 e))) (length vs))"
  have Isub: "{pc..<pc + length (compE\<^sub>2 e)} \<subseteq> ?I"
    using WhileBodyThrow\<^sub>1.prems by clarsimp
  have IH: "PROP ?P e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 true h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics (Bool True) xa vs frs ?I" by fact
  then have "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> (None,h\<^sub>1,(Bool(True)#vs,ls\<^sub>1,C,M,?pc\<^sub>1,ics)#frs,sh\<^sub>1)"
    using WhileBodyThrow\<^sub>1.prems nsub_RI_Jcc_pieces Isub by auto
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^sub>1" using  WhileBodyThrow\<^sub>1 by auto
  finally have eval\<^sub>1: "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>1".
  let ?pc\<^sub>1' = "?pc\<^sub>1 + 1 + length(compE\<^sub>2 c)"
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm by simp
  next
    show ?Err (is "?throw \<longrightarrow> ?err")
    proof
      assume throw: ?throw
      moreover
      have "PROP ?P c h\<^sub>1 ls\<^sub>1 sh\<^sub>1 (throw e') h\<^sub>2 ls\<^sub>2 sh\<^sub>2 E C M (?pc\<^sub>1+1) ics v xa vs frs
                    (I - pcs (compxE\<^sub>2 e pc (size vs)))" by fact
      ultimately obtain pc\<^sub>2 vs' where
        pc\<^sub>2: "?pc\<^sub>1+1 \<le> pc\<^sub>2 \<and> pc\<^sub>2 < ?pc\<^sub>1' \<and>
              \<not> caught P pc\<^sub>2 h\<^sub>2 xa (compxE\<^sub>2 c (?pc\<^sub>1+1) (size vs))" and
        eval\<^sub>2: "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> handle P C M xa h\<^sub>2 (vs'@vs) ls\<^sub>2 pc\<^sub>2 ics frs sh\<^sub>2"
        using WhileBodyThrow\<^sub>1.prems nsub_RI_Jcc_pieces by (fastforce simp:Int_Un_distrib)
      show "?err" using pc\<^sub>2 jvm_trans[OF eval\<^sub>1 eval\<^sub>2] by(auto intro: exI[where x=pc\<^sub>2])
    qed
  qed
next
  case (Throw\<^sub>1 e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 a h\<^sub>1 ls\<^sub>1 sh\<^sub>1)
  let ?pc = "pc + size(compE\<^sub>2 e)"
  have Isub: "{pc..<pc + length (compE\<^sub>2 e)} \<subseteq> I" using Throw\<^sub>1.prems by clarsimp
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm by simp
  next
    show ?Err (is "?throw \<longrightarrow> ?err")
    proof
      assume throw:?throw
      have "PROP ?P e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (addr a) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics (Addr a) a vs frs I" by fact
      then have "P \<turnstile> (None, h\<^sub>0, (vs, ls\<^sub>0, C, M, pc, ics) # frs, sh\<^sub>0) -jvm\<rightarrow>
                 (None, h\<^sub>1, (Addr xa#vs, ls\<^sub>1, C, M, ?pc, ics) # frs, sh\<^sub>1)"
        using Throw\<^sub>1 nsub_RI_Jcc_pieces Isub throw by auto
      also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M xa h\<^sub>1 (Addr xa#vs) ls\<^sub>1 ?pc ics frs sh\<^sub>1"
        using Throw\<^sub>1.prems by(auto simp add:handle_def)
      finally show "?err" by(auto intro!: exI[where x="?pc"] exI[where x="[Addr xa]"])
    qed
  qed
next
  case (ThrowNull\<^sub>1 e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 h\<^sub>1 ls\<^sub>1 sh\<^sub>1)
  let ?pc = "pc + size(compE\<^sub>2 e)"
  let ?xa = "addr_of_sys_xcpt NullPointer"
  have Isub: "{pc..<pc + length (compE\<^sub>2 e)} \<subseteq> I" using ThrowNull\<^sub>1.prems by clarsimp
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm by simp
  next
    show ?Err (is "?throw \<longrightarrow> ?err")
    proof
      assume throw: ?throw
      have "PROP ?P e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 null h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics Null xa vs frs I" by fact
      then have "P \<turnstile> (None, h\<^sub>0, (vs, ls\<^sub>0, C, M, pc, ics) # frs, sh\<^sub>0) -jvm\<rightarrow>
                 (None, h\<^sub>1, (Null#vs, ls\<^sub>1, C, M, ?pc, ics) # frs, sh\<^sub>1)"
        using ThrowNull\<^sub>1.prems nsub_RI_Jcc_pieces Isub by auto
      also have "P \<turnstile> \<dots> -jvm\<rightarrow>  handle P C M ?xa h\<^sub>1 (Null#vs) ls\<^sub>1 ?pc ics frs sh\<^sub>1"
        using ThrowNull\<^sub>1.prems by(auto simp add:handle_def)
      finally show "?err" using throw by(auto intro!: exI[where x="?pc"] exI[where x="[Null]"])
    qed
  qed
next
  case (ThrowThrow\<^sub>1 e h ls sh e' h' ls' sh')
  obtain a' where throw: "throw e' = Throw a'" using eval\<^sub>1_final[OF ThrowThrow\<^sub>1.hyps(1)] by clarsimp
  have Isub: "{pc..<pc + length (compE\<^sub>2 e)} \<subseteq> I" using ThrowThrow\<^sub>1.prems by clarsimp
  have "PROP ?P e h ls sh (throw e') h' ls' sh' E C M pc ics v a' vs frs I" by fact
  then show ?case using ThrowThrow\<^sub>1.prems throw nsub_RI_Jcc_pieces Isub by auto
next
  case (Try\<^sub>1 e\<^sub>1 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 v\<^sub>1 h\<^sub>1 ls\<^sub>1 sh\<^sub>1 Ci i e\<^sub>2)
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e\<^sub>1)"
  let ?pc\<^sub>1' = "?pc\<^sub>1 + 2 + length(compE\<^sub>2 e\<^sub>2)"
  have "{pc..<pc+size(compE\<^sub>2 (try e\<^sub>1 catch(Ci i) e\<^sub>2))} \<subseteq> I" using Try\<^sub>1.prems by simp
  also have "P,C,M \<rhd> compxE\<^sub>2 (try e\<^sub>1 catch(Ci i) e\<^sub>2) pc (size vs) / I,size vs"
    using Try\<^sub>1.prems by simp
  ultimately have "P,C,M \<rhd> compxE\<^sub>2 e\<^sub>1 pc (size vs) / {pc..<pc + length (compE\<^sub>2 e\<^sub>1)},size vs"
    by(rule beforex_try)
  hence "P \<turnstile> (None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc,ics)#frs,sh\<^sub>0) -jvm\<rightarrow>
             (None,h\<^sub>1,(v\<^sub>1#vs,ls\<^sub>1,C,M,?pc\<^sub>1,ics)#frs,sh\<^sub>1)"
    using Try\<^sub>1 nsub_RI_Jcc_pieces by auto blast
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h\<^sub>1,(v\<^sub>1#vs,ls\<^sub>1,C,M,?pc\<^sub>1',ics)#frs,sh\<^sub>1)"
    using Try\<^sub>1.prems by auto
  finally show ?case by (auto simp:add.assoc)
next
  case (TryCatch\<^sub>1 e\<^sub>1 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 a h\<^sub>1 ls\<^sub>1 sh\<^sub>1 D fs Ci i e\<^sub>2 e\<^sub>2' h\<^sub>2 ls\<^sub>2 sh\<^sub>2)
  let ?e = "try e\<^sub>1 catch(Ci i) e\<^sub>2"
  let ?xt = "compxE\<^sub>2 ?e pc (size vs)"
  let ?\<sigma>\<^sub>0 = "(None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc,ics)#frs,sh\<^sub>0)"
  let ?ls\<^sub>1 = "ls\<^sub>1[i := Addr a]"
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e\<^sub>1)"
  let ?pc\<^sub>1' = "?pc\<^sub>1 + 2"
  let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,(vs,?ls\<^sub>1,C,M, ?pc\<^sub>1',ics) # frs,sh\<^sub>1)"
  have I: "{pc..<pc + length (compE\<^sub>2 (try e\<^sub>1 catch(Ci i) e\<^sub>2))} \<subseteq> I"
   and beforex: "P,C,M \<rhd> ?xt/I,size vs" using TryCatch\<^sub>1.prems by simp+
  have "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> (None,h\<^sub>1,((Addr a)#vs,ls\<^sub>1,C,M, ?pc\<^sub>1+1,ics) # frs,sh\<^sub>1)"
  proof -
    have ics: "ics = No_ics" using TryCatch\<^sub>1.prems by auto
    have "PROP ?P e\<^sub>1 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (Throw a) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics v a vs frs {pc..<pc + length (compE\<^sub>2 e\<^sub>1)}"
      by fact
    moreover have "P,C,M \<rhd> compxE\<^sub>2 e\<^sub>1 pc (size vs)/{pc..<?pc\<^sub>1},size vs"
      using beforex I pcs_subset by(force elim!: beforex_appendD1)
    ultimately have
      "\<exists>pc\<^sub>1. pc \<le> pc\<^sub>1 \<and> pc\<^sub>1 < ?pc\<^sub>1 \<and>
             \<not> caught P pc\<^sub>1 h\<^sub>1 a (compxE\<^sub>2 e\<^sub>1 pc (size vs)) \<and>
             (\<exists>vs'. P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> handle P C M a h\<^sub>1 (vs'@vs) ls\<^sub>1 pc\<^sub>1 ics frs sh\<^sub>1)"
      using  TryCatch\<^sub>1.prems nsub_RI_Jcc_pieces by auto
    then obtain pc\<^sub>1 vs' where
      pc\<^sub>1_in_e\<^sub>1: "pc \<le> pc\<^sub>1" "pc\<^sub>1 < ?pc\<^sub>1" and
      pc\<^sub>1_not_caught: "\<not> caught P pc\<^sub>1 h\<^sub>1 a (compxE\<^sub>2 e\<^sub>1 pc (size vs))" and
      0: "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> handle P C M a h\<^sub>1 (vs'@vs) ls\<^sub>1 pc\<^sub>1 ics frs sh\<^sub>1" by iprover
    from beforex obtain xt\<^sub>0 xt\<^sub>1
      where ex_tab: "ex_table_of P C M = xt\<^sub>0 @ ?xt @ xt\<^sub>1"
      and disj: "pcs xt\<^sub>0 \<inter> I = {}" by(auto simp:beforex_def)
    have hp: "h\<^sub>1 a = Some (D, fs)" "P\<^sub>1 \<turnstile> D \<preceq>\<^sup>* Ci" by fact+
    have "pc\<^sub>1 \<notin> pcs xt\<^sub>0" using pc\<^sub>1_in_e\<^sub>1 I disj by auto
    with pc\<^sub>1_in_e\<^sub>1 pc\<^sub>1_not_caught hp
    show ?thesis using ex_tab 0 ics by(simp add:handle_def matches_ex_entry_def)
  qed
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^sub>1" using TryCatch\<^sub>1 by auto
  finally have 1: "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>1" .
  let ?pc\<^sub>2 = "?pc\<^sub>1' + length(compE\<^sub>2 e\<^sub>2)"
  let ?I\<^sub>2 = "{?pc\<^sub>1' ..< ?pc\<^sub>2}"
  have "P,C,M \<rhd> compxE\<^sub>2 ?e pc (size vs) / I,size vs" by fact
  hence beforex\<^sub>2: "P,C,M \<rhd> compxE\<^sub>2 e\<^sub>2 ?pc\<^sub>1' (size vs) / ?I\<^sub>2, size vs"
    using I pcs_subset[of _ ?pc\<^sub>1'] by(auto elim!:beforex_appendD2)
  have IH\<^sub>2: "PROP ?P e\<^sub>2 h\<^sub>1 ?ls\<^sub>1 sh\<^sub>1 e\<^sub>2' h\<^sub>2 ls\<^sub>2 sh\<^sub>2 E C M ?pc\<^sub>1' ics v xa vs frs ?I\<^sub>2" by fact
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm (is "?val \<longrightarrow> ?trans")
    proof
      assume val: ?val
      note 1 also have "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> (None,h\<^sub>2,(v#vs,ls\<^sub>2,C,M,?pc\<^sub>2,ics)#frs,sh\<^sub>2)"
        using val beforex\<^sub>2 IH\<^sub>2 TryCatch\<^sub>1.prems nsub_RI_Jcc_pieces by auto
      finally show ?trans by(simp add:add.assoc)
    qed
  next
    show ?Err (is "?throw \<longrightarrow> ?err")
    proof
      assume throw: ?throw
      then obtain pc\<^sub>2 vs' where
        pc\<^sub>2: "?pc\<^sub>1+2 \<le> pc\<^sub>2 \<and> pc\<^sub>2 < ?pc\<^sub>2 \<and>
              \<not> caught P pc\<^sub>2 h\<^sub>2 xa (compxE\<^sub>2 e\<^sub>2 ?pc\<^sub>1' (size vs))" and
        2: "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> handle P C M xa h\<^sub>2 (vs'@vs) ls\<^sub>2 pc\<^sub>2 ics frs sh\<^sub>2"
        using IH\<^sub>2 beforex\<^sub>2 TryCatch\<^sub>1.prems nsub_RI_Jcc_pieces by auto
      show ?err using pc\<^sub>2 jvm_trans[OF 1 2]
       by (simp add:match_ex_entry) (auto intro: exI[where x=pc\<^sub>2])
    qed
  qed
next
  case (TryThrow\<^sub>1 e\<^sub>1 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 a h\<^sub>1 ls\<^sub>1 sh\<^sub>1 D fs Ci i e\<^sub>2)
  let ?\<sigma>\<^sub>0 = "(None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc,ics)#frs,sh\<^sub>0)"
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e\<^sub>1)"
  let ?e = "try e\<^sub>1 catch(Ci i) e\<^sub>2"
  let ?xt = "compxE\<^sub>2 ?e pc (size vs)"
  have I: "{pc..<pc + length (compE\<^sub>2 (try e\<^sub>1 catch(Ci i) e\<^sub>2))} \<subseteq> I"
   and beforex: "P,C,M \<rhd> ?xt/I,size vs" using TryThrow\<^sub>1.prems by simp+
  have "PROP ?P e\<^sub>1 h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (Throw a) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 E C M pc ics v a vs frs 
   {pc..<pc + length (compE\<^sub>2 e\<^sub>1)}" by fact
  moreover have "P,C,M \<rhd> compxE\<^sub>2 e\<^sub>1 pc (size vs)/{pc..<?pc\<^sub>1},size vs"
    using beforex I pcs_subset by(force elim!: beforex_appendD1)
    ultimately have
      "\<exists>pc\<^sub>1. pc \<le> pc\<^sub>1 \<and> pc\<^sub>1 < ?pc\<^sub>1 \<and>
             \<not> caught P pc\<^sub>1 h\<^sub>1 a (compxE\<^sub>2 e\<^sub>1 pc (size vs)) \<and>
             (\<exists>vs'. P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> handle P C M a h\<^sub>1 (vs'@vs) ls\<^sub>1 pc\<^sub>1 ics frs sh\<^sub>1)"
      using TryThrow\<^sub>1.prems nsub_RI_Jcc_pieces by auto
    then obtain pc\<^sub>1 vs' where
      pc\<^sub>1_in_e\<^sub>1: "pc \<le> pc\<^sub>1" "pc\<^sub>1 < ?pc\<^sub>1" and
      pc\<^sub>1_not_caught: "\<not> caught P pc\<^sub>1 h\<^sub>1 a (compxE\<^sub>2 e\<^sub>1 pc (size vs))" and
      0: "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> handle P C M a h\<^sub>1 (vs'@vs) ls\<^sub>1 pc\<^sub>1 ics frs sh\<^sub>1" by iprover
  show ?case (is "?N \<and> (?eq \<longrightarrow> ?err)")
  proof
    show ?N by simp
  next
    { assume ?eq
      with TryThrow\<^sub>1 pc\<^sub>1_in_e\<^sub>1 pc\<^sub>1_not_caught 0
      have "?err" by (simp add:match_ex_entry) auto
    }
    thus "?eq \<longrightarrow> ?err" by iprover
  qed
next
  case Nil\<^sub>1 thus ?case by simp
next
  case (Cons\<^sub>1 e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 v h\<^sub>1 ls\<^sub>1 sh\<^sub>1 es fs h\<^sub>2 ls\<^sub>2 sh\<^sub>2)
  let ?pc\<^sub>1 = "pc + length(compE\<^sub>2 e)"
  let ?\<sigma>\<^sub>0 = "(None,h\<^sub>0,(vs,ls\<^sub>0,C,M,pc,ics)#frs,sh\<^sub>0)"
  let ?\<sigma>\<^sub>1 = "(None,h\<^sub>1,(v#vs,ls\<^sub>1,C,M,?pc\<^sub>1,ics)#frs,sh\<^sub>1)"
  have IH: "PROP ?P e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 (Val v) h\<^sub>1 ls\<^sub>1 sh\<^sub>1 [] C M pc ics v xa vs frs
    (I - pcs (compxEs\<^sub>2 es ?pc\<^sub>1 (Suc (length vs))))" by fact
  then have 1: "P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>1" using Jcc_pieces_Cons[OF _ Cons\<^sub>1.prems(1-5)] by auto
  let ?pc\<^sub>2 = "?pc\<^sub>1 + length(compEs\<^sub>2 es)"
  have IHs: "PROP ?Ps es h\<^sub>1 ls\<^sub>1 sh\<^sub>1 fs h\<^sub>2 ls\<^sub>2 sh\<^sub>2 C M ?pc\<^sub>1 ics (tl ws) xa es' (v#vs) frs
    (I - pcs (compxE\<^sub>2 e pc (length vs)))" by fact
  show ?case (is "?Norm \<and> ?Err")
  proof
    show ?Norm (is "?val \<longrightarrow> ?trans")
    proof
      assume val: ?val
      note 1
      also have "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> (None,h\<^sub>2,(rev(ws) @ vs,ls\<^sub>2,C,M,?pc\<^sub>2,ics)#frs,sh\<^sub>2)"
        using val IHs Cons\<^sub>1.prems by fastforce
      finally show ?trans by(simp add:add.assoc)
    qed
  next
    show ?Err (is "?throw \<longrightarrow> (\<exists>pc\<^sub>2. ?H pc\<^sub>2)")
    proof
      assume throw: ?throw
      then obtain pc\<^sub>2 vs' where
        pc\<^sub>2: "?pc\<^sub>1 \<le> pc\<^sub>2 \<and> pc\<^sub>2 < ?pc\<^sub>2 \<and>
              \<not> caught P pc\<^sub>2 h\<^sub>2 xa (compxEs\<^sub>2 es ?pc\<^sub>1 (size vs + 1))" and
        2: "P \<turnstile> ?\<sigma>\<^sub>1 -jvm\<rightarrow> handle P C M xa h\<^sub>2 (vs'@v#vs) ls\<^sub>2 pc\<^sub>2 ics frs sh\<^sub>2"
        using IHs Cons\<^sub>1.prems by(fastforce simp:Cons_eq_append_conv neq_Nil_conv)
      have "?H pc\<^sub>2" using Cons\<^sub>1.prems pc\<^sub>2 jvm_trans[OF 1 2] by(auto intro!: exI[where x="vs'@[v]"])
      thus "\<exists>pc\<^sub>2. ?H pc\<^sub>2" by iprover
    qed
  qed
next
  case (ConsThrow\<^sub>1 e h\<^sub>0 ls\<^sub>0 sh\<^sub>0 a h\<^sub>1 ls\<^sub>1 sh\<^sub>1 es)
  then show ?case using Jcc_pieces_Cons[OF _ ConsThrow\<^sub>1.prems(1-5)]
    by (fastforce simp:Cons_eq_append_conv)
next
  case InitFinal\<^sub>1 then show ?case using eval\<^sub>1_final_same[OF InitFinal\<^sub>1.hyps(1)] by clarsimp
next
  case (InitNone\<^sub>1 sh C\<^sub>0 C' Cs e h l e' h' l' sh')
  then obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs sh I h' l' sh' v xa
     (INIT C' (C\<^sub>0 # Cs,False) \<leftarrow> e)
    = (True, frs', (None, h', (vs, l, C, M, pc, Called []) # frs, sh'), err)"
    using InitNone\<^sub>1.prems(1) by clarsimp
  let ?sh = "(sh(C\<^sub>0 \<mapsto> (sblank P\<^sub>1 C\<^sub>0, Prepared)))"
  obtain ics: "ics_of(hd frs') = Calling C\<^sub>0 Cs"
     and frs\<^sub>1: "frs' \<noteq> Nil" using pcs by clarsimp
  then have 1: "P \<turnstile> (None,h,frs',sh) -jvm\<rightarrow> (None,h,frs',?sh)"
    using InitNone\<^sub>1 jvm_InitNone[where P = P] by(cases frs', simp+)
  show ?case (is "(?e1 \<longrightarrow> ?jvm1) \<and> (?e2 \<longrightarrow> ?err)")
  proof(rule conjI)
    { assume val: ?e1
      note 1
      also have "P \<turnstile> (None,h,frs',?sh) -jvm\<rightarrow> (None,h',(vs,l,C,M,pc,Called [])#frs,sh')"
        using InitNone\<^sub>1.hyps(3)[of E] Jcc_pieces_InitNone[OF assms(1) pcs] InitNone\<^sub>1.prems val
         by clarsimp
      finally have ?jvm1 using pcs by simp
    }
    thus "?e1 \<longrightarrow> ?jvm1" by simp
  next
    { assume throw: ?e2
      note 1
      also obtain vs' where "P \<turnstile> (None,h,frs',?sh)
                     -jvm\<rightarrow> handle P C M xa h' (vs'@vs) l pc ics frs sh'"
        using InitNone\<^sub>1.hyps(3)[of E] Jcc_pieces_InitNone[OF assms(1) pcs] throw
         by clarsimp presburger
      finally have ?err using pcs by auto
    }
    thus "?e2 \<longrightarrow> ?err" by simp
  qed
next
  case (InitDone\<^sub>1 sh C\<^sub>0 sfs C' Cs e h l e' h' l' sh')
  then obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs sh I h' l' sh' v xa
     (INIT C' (C\<^sub>0 # Cs,False) \<leftarrow> e)
    = (True, frs', (None, h', (vs, l, C, M, pc, Called []) # frs, sh'), err)"
    using InitDone\<^sub>1.prems(1) by clarsimp
  let ?frs' = "(calling_to_scalled (hd frs'))#(tl frs')"
  have IH: "PROP ?P (INIT C' (Cs,True) \<leftarrow> e) h l sh e' h' l' sh' E C M pc ics v xa vs frs I"
    by fact
  obtain ics: "ics_of(hd frs') = Calling C\<^sub>0 Cs"
     and frs\<^sub>1: "frs' \<noteq> Nil" using pcs by clarsimp
  then have 1: "P \<turnstile> (None,h,frs',sh) -jvm\<rightarrow> (None,h,?frs',sh)"
    using InitDone\<^sub>1 jvm_InitDP[where P = P] by(cases frs', simp+)
  show ?case (is "(?e1 \<longrightarrow> ?jvm1) \<and> (?e2 \<longrightarrow> ?err)")
  proof(rule conjI)
    { assume val: ?e1
      note 1
      also have "P \<turnstile> (None,h,?frs',sh) -jvm\<rightarrow> (None,h',(vs,l,C,M,pc,Called [])#frs,sh')"
        using IH Jcc_pieces_InitDP[OF assms(1) pcs] InitDone\<^sub>1.prems val by clarsimp
      finally have ?jvm1 using pcs by simp
    }
    thus "?e1 \<longrightarrow> ?jvm1" by simp
  next
    { assume throw: ?e2
      note 1
      also obtain vs' where "P \<turnstile> (None,h,?frs',sh)
                     -jvm\<rightarrow> handle P C M xa h' (vs'@vs) l pc ics frs sh'"
        using IH Jcc_pieces_InitDP[OF assms(1) pcs] InitDone\<^sub>1.prems throw by clarsimp
      finally have ?err using pcs by auto
    }
    thus "?e2 \<longrightarrow> ?err" by simp
  qed
next
  case (InitProcessing\<^sub>1 sh C\<^sub>0 sfs C' Cs e h l e' h' l' sh')
  then obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs sh I h' l' sh' v xa
     (INIT C' (C\<^sub>0 # Cs,False) \<leftarrow> e)
    = (True, frs', (None, h', (vs, l, C, M, pc, Called []) # frs, sh'), err)"
    using InitProcessing\<^sub>1.prems(1) by clarsimp
  let ?frs' = "(calling_to_scalled (hd frs'))#(tl frs')"
  have IH: "PROP ?P (INIT C' (Cs,True) \<leftarrow> e) h l sh e' h' l' sh' E C M pc ics v xa vs frs I"
    by fact
  obtain ics: "ics_of(hd frs') = Calling C\<^sub>0 Cs"
     and frs\<^sub>1: "frs' \<noteq> Nil" using pcs by clarsimp
  then have 1: "P \<turnstile> (None,h,frs',sh) -jvm\<rightarrow> (None,h,?frs',sh)"
    using InitProcessing\<^sub>1 jvm_InitDP[where P = P] by(cases frs', simp+)
  show ?case (is "(?e1 \<longrightarrow> ?jvm1) \<and> (?e2 \<longrightarrow> ?err)")
  proof(rule conjI)
    { assume val: ?e1
      note 1
      also have "P \<turnstile> (None,h,?frs',sh) -jvm\<rightarrow> (None,h',(vs,l,C,M,pc,Called [])#frs,sh')"
        using IH Jcc_pieces_InitDP[OF assms(1) pcs] InitProcessing\<^sub>1.prems val by clarsimp
      finally have ?jvm1 using pcs by simp
    }
    thus "?e1 \<longrightarrow> ?jvm1" by simp
  next
    { assume throw: ?e2
      note 1
      also obtain vs' where "P \<turnstile> (None,h,?frs',sh)
                     -jvm\<rightarrow> handle P C M xa h' (vs'@vs) l pc ics frs sh'"
        using IH Jcc_pieces_InitDP[OF assms(1) pcs] InitProcessing\<^sub>1.prems throw by clarsimp
      finally have ?err using pcs by auto
    }
    thus "?e2 \<longrightarrow> ?err" by simp
  qed
next
  case (InitError\<^sub>1 sh C\<^sub>0 sfs Cs e h l e' h' l' sh' C')
  then obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs sh I h' l' sh' v xa
     (INIT C' (C\<^sub>0 # Cs,False) \<leftarrow> e)
    = (True, frs', (None, h', (vs, l, C, M, pc, Called []) # frs, sh'), err)"
    using InitError\<^sub>1.prems(1) by clarsimp
  let ?e\<^sub>0 = "THROW NoClassDefFoundError"
  let ?frs' = "(calling_to_sthrowing (hd frs') (addr_of_sys_xcpt NoClassDefFoundError))#(tl frs')"
  have IH: "PROP ?P (RI (C\<^sub>0,?e\<^sub>0) ; Cs \<leftarrow> e) h l sh e' h' l' sh' E C M pc ics v xa vs frs I" by fact
  obtain ics: "ics_of(hd frs') = Calling C\<^sub>0 Cs"
     and frs\<^sub>1: "frs' \<noteq> Nil"
     and tl: "tl frs' = frs" using pcs by clarsimp
  then have 1: "P \<turnstile> (None,h,frs',sh) -jvm\<rightarrow> (None,h,?frs',sh)"
  proof(cases frs')
    case (Cons a list)
    obtain vs' l' C' M' pc' ics' where a: "a = (vs',l',C',M',pc',ics')" by(cases a)
    then have "ics' = Calling C\<^sub>0 Cs" using Cons ics by simp
    then show ?thesis
     using Cons a IH InitError\<^sub>1.prems jvm_InitError[where P = P] InitError\<^sub>1.hyps(1) by simp
  qed(simp)
  show ?case (is "(?e1 \<longrightarrow> ?jvm1) \<and> (?e2 \<longrightarrow> ?err)")
  proof(rule conjI)
    { assume val: ?e1
      then have False using val rinit\<^sub>1_throw[OF InitError\<^sub>1.hyps(2)] by blast
      then have ?jvm1 using pcs by simp
    }
    thus "?e1 \<longrightarrow> ?jvm1" by simp
  next
    { assume throw: ?e2
      let ?frs = "(calling_to_throwing (hd frs') (addr_of_sys_xcpt NoClassDefFoundError))#(tl frs')"
      have exec: "exec (P, (None,h,?frs,sh)) = Some (None,h,?frs',sh)"
        using exec_ErrorThrowing[where sh=sh, OF InitError\<^sub>1.hyps(1)] ics by(cases "hd frs'", simp)
      obtain vs' where 2: "P \<turnstile> (None,h,?frs,sh) -jvm\<rightarrow> handle P C M xa h' (vs'@vs) l pc ics frs sh'"
        using IH Jcc_pieces_InitError[OF assms(1) pcs InitError\<^sub>1.hyps(1)] throw by clarsimp
      have neq: "(None, h, ?frs, sh) \<noteq> handle P C M xa h' (vs' @ vs) l pc ics frs sh'"
        using tl ics by(cases "hd frs'", simp add: handle_frs_tl_neq)

      note 1
      also have "P \<turnstile> (None,h,?frs',sh) -jvm\<rightarrow> handle P C M xa h' (vs'@vs) l pc ics frs sh'"
        using exec_1_exec_all_conf[OF exec 2] neq by simp
      finally have ?err using pcs by auto
    }
    thus "?e2 \<longrightarrow> ?err" by simp
  qed
next
  case (InitObject\<^sub>1 sh C\<^sub>0 sfs sh' C' Cs e h l e' h' l' sh'')
  then obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs sh I h' l'
    (sh(C\<^sub>0 \<mapsto> (sfs, Processing))) v xa (INIT C' (C\<^sub>0 # Cs,False) \<leftarrow> e)
    = (True, frs', (None, h', (vs, l, C, M, pc, Called []) # frs, sh'), err)"
    using InitObject\<^sub>1.prems(1) by clarsimp
  let ?frs' = "(calling_to_called (hd frs'))#(tl frs')"
  have IH: "PROP ?P (INIT C' (C\<^sub>0#Cs,True) \<leftarrow> e) h l sh' e' h' l' sh'' E C M pc ics v xa vs frs I"
    by fact
  obtain ics: "ics_of(hd frs') = Calling C\<^sub>0 Cs"
     and frs\<^sub>1: "frs' \<noteq> Nil" using pcs by clarsimp
  then have 1: "P \<turnstile> (None,h,frs',sh) -jvm\<rightarrow> (None,h,?frs',sh')"
  proof(cases frs')
    case (Cons a list)
    obtain vs' l' C' M' pc' ics' where a: "a = (vs',l',C',M',pc',ics')" by(cases a)
    then have "ics' = Calling C\<^sub>0 Cs" using Cons ics by simp
    then show ?thesis
     using Cons Nil a IH InitObject\<^sub>1 jvm_InitObj[where P = P] by simp
  qed(simp)
  show ?case (is "(?e1 \<longrightarrow> ?jvm1) \<and> (?e2 \<longrightarrow> ?err)")
  proof(rule conjI)
    { assume val: ?e1
      note 1
      also have "P \<turnstile> (None,h,?frs',sh') -jvm\<rightarrow> (None,h',(vs,l,C,M,pc,Called [])#frs,sh'')"
        using IH Jcc_pieces_InitObj[OF assms(1) pcs] InitObject\<^sub>1 val by simp
      finally have ?jvm1 using pcs by simp
    }
    thus "?e1 \<longrightarrow> ?jvm1" by simp
  next
    { assume throw: ?e2
      note 1
      also obtain vs' where "P \<turnstile> (None,h,?frs',sh')
                     -jvm\<rightarrow> handle P C M xa h' (vs'@vs) l pc ics frs sh''"
        using IH Jcc_pieces_InitObj[OF assms(1) pcs] InitObject\<^sub>1 throw by clarsimp
      finally have ?err using pcs by auto
    }
    thus "?e2 \<longrightarrow> ?err" by simp
  qed
next
  case (InitNonObject\<^sub>1 sh C\<^sub>0 sfs D a b sh' C' Cs e h l e' h' l' sh'')
  then obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs sh I h' l'
    (sh(C\<^sub>0 \<mapsto> (sfs,Processing))) v xa (INIT C' (C\<^sub>0 # Cs,False) \<leftarrow> e)
    = (True, frs', (None, h', (vs, l, C, M, pc, Called []) # frs, sh'), err)"
    using InitNonObject\<^sub>1.prems(1) by clarsimp
  let ?frs' = "(calling_to_calling (hd frs') D)#(tl frs')"
  have cls1: "is_class P\<^sub>1 D" using InitNonObject\<^sub>1.hyps(2,3) class_wf wf wf_cdecl_supD by blast
  have cls_aux: "distinct (C\<^sub>0#Cs) \<and> supercls_lst P\<^sub>1 (C\<^sub>0#Cs)" using InitNonObject\<^sub>1.prems(1) by auto
  then have cls2: "D \<notin> set (C\<^sub>0 # Cs)"
  proof -
    have "distinct (D # C\<^sub>0 # Cs)"
      using InitNonObject\<^sub>1.hyps(2,3) cls_aux wf wf_supercls_distinct_app by blast
    then show "D \<notin> set (C\<^sub>0 # Cs)"
      by (metis distinct.simps(2))
  qed
  have cls3: "\<forall>C\<in>set (C\<^sub>0 # Cs). P\<^sub>1 \<turnstile> C \<preceq>\<^sup>* D" using InitNonObject\<^sub>1.hyps(2,3) cls_aux
    by (metis r_into_rtrancl rtrancl_into_rtrancl set_ConsD subcls1.subcls1I supercls_lst.simps(1))
  have IH: "PROP ?P (INIT C' (D # C\<^sub>0 # Cs,False) \<leftarrow> e) h l sh' e' h' l' sh'' E C M pc ics v xa vs frs I"
    by fact
  obtain r where cls: "class P C\<^sub>0 = \<lfloor>(D, r)\<rfloor>" using InitNonObject\<^sub>1.hyps(3)
    by (metis assms class_compP compP\<^sub>2_def)
  obtain ics: "ics_of(hd frs') = Calling C\<^sub>0 Cs"
     and frs\<^sub>1: "frs' \<noteq> Nil" using pcs by clarsimp
  then have 1: "P \<turnstile> (None,h,frs',sh) -jvm\<rightarrow> (None,h,?frs',sh')"
  proof(cases frs')
    case (Cons a list)
    obtain vs' l' C' M' pc' ics' where a: "a = (vs',l',C',M',pc',ics')" by(cases a)
    then have "ics' = Calling C\<^sub>0 Cs" using Cons ics by simp
    then show ?thesis
     using Cons a IH InitNonObject\<^sub>1 jvm_InitNonObj[OF _ _ cls] by simp
  qed(simp)
  show ?case (is "(?e1 \<longrightarrow> ?jvm1) \<and> (?e2 \<longrightarrow> ?err)")
  proof(rule conjI)
    { assume val: ?e1
      note 1
      also have "P \<turnstile> (None,h,?frs',sh') -jvm\<rightarrow> (None,h',(vs,l,C,M,pc,Called [])#frs,sh'')"
        using IH Jcc_pieces_InitNonObj[OF assms(1) cls1 cls2 cls3 pcs] InitNonObject\<^sub>1 val by simp
      finally have ?jvm1 using pcs by simp
    }
    thus "?e1 \<longrightarrow> ?jvm1" by simp
  next
    { assume throw: ?e2
      note 1
      also obtain vs' where "P \<turnstile> (None,h,?frs',sh')
                     -jvm\<rightarrow> handle P C M xa h' (vs'@vs) l pc ics frs sh''"
        using IH Jcc_pieces_InitNonObj[OF assms(1) cls1 cls2 cls3 pcs] InitNonObject\<^sub>1 throw by clarsimp
      finally have ?err using pcs by auto
    }
    thus "?e2 \<longrightarrow> ?err" by simp
  qed
next
  case (InitRInit\<^sub>1 C\<^sub>0 Cs e h l sh e' h' l' sh' C')
  then obtain frs' err where pcs: "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs sh I h' l' sh' v xa
     (INIT C' (C\<^sub>0 # Cs,True) \<leftarrow> e)
    = (True, frs', (None, h', (vs, l, C, M, pc, Called []) # frs, sh'), err)"
    using InitRInit\<^sub>1.prems(1) by clarsimp
  have IH: "PROP ?P (RI (C\<^sub>0,C\<^sub>0\<bullet>\<^sub>sclinit([])) ; Cs \<leftarrow> e) h l sh e' h' l' sh' E C M pc ics v xa vs frs I"
    by fact
  show ?case (is "(?e1 \<longrightarrow> ?jvm1) \<and> (?e2 \<longrightarrow> ?err)")
  proof(rule conjI)
    { assume val: ?e1
      have "P \<turnstile> (None,h,frs',sh) -jvm\<rightarrow> (None,h',(vs,l,C,M,pc,Called [])#frs,sh')"
        using IH Jcc_pieces_InitRInit[OF assms(1,2) pcs] InitRInit\<^sub>1.prems val by simp
      then have ?jvm1 using pcs by simp
    }
    thus "?e1 \<longrightarrow> ?jvm1" by simp
  next
    { assume throw: ?e2
      obtain vs' where "P \<turnstile> (None,h,frs',sh)
                     -jvm\<rightarrow> handle P C M xa h' (vs'@vs) l pc ics frs sh'"
        using IH Jcc_pieces_InitRInit[OF assms(1,2) pcs] InitRInit\<^sub>1 throw by clarsimp
      then have ?err using pcs by auto
    }
    thus "?e2 \<longrightarrow> ?err" by simp
  qed
next
  case (RInit\<^sub>1 e h l sh v1 h' l' sh' C\<^sub>0 sfs i sh'' C' Cs e' e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1)
  let ?frs = "(vs,l,C,M,pc,Called (C\<^sub>0#Cs)) # frs"
  let ?frs' = "(vs,l,C,M,pc,Called Cs) # frs"
  have clinit: "e = C\<^sub>0\<bullet>\<^sub>sclinit([])" using RInit\<^sub>1
    by (metis Jcc_cond.simps(2) eval\<^sub>1_final_same exp.distinct(101) final_def)
  then obtain err where pcs: "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs sh I h\<^sub>1 l\<^sub>1 sh\<^sub>1 v xa
     (RI (C\<^sub>0,C\<^sub>0\<bullet>\<^sub>sclinit([])) ; Cs \<leftarrow> e')
    = (True, ?frs, (None, h\<^sub>1, (vs, l, C, M, pc, Called []) # frs, sh\<^sub>1), err)"
    using RInit\<^sub>1.prems(1) by simp
  have shC: "\<forall>C'\<in>set Cs. \<exists>sfs. sh C' = \<lfloor>(sfs, Processing)\<rfloor>" using RInit\<^sub>1.prems(1) clinit by clarsimp
  then have shC'': "\<forall>C'\<in>set Cs. \<exists>sfs. sh'' C' = \<lfloor>(sfs, Processing)\<rfloor>"
    using clinit\<^sub>1_proc_pres[OF wf] RInit\<^sub>1.hyps(1) clinit RInit\<^sub>1.hyps(4) RInit\<^sub>1.prems(1)
      by (auto simp: fun_upd_apply)
  have loc: "l = l'" using clinit\<^sub>1_loc_pres RInit\<^sub>1.hyps(1) clinit by simp
  have IH: "PROP ?P e h l sh (Val v1) h' l' sh' E C M pc (Called Cs) v1 xa vs (tl ?frs') I" by fact
  then have IH':
   "PROP ?P (C\<^sub>0\<bullet>\<^sub>sclinit([])) h l sh (Val v1) h' l' sh' E C M pc (Called Cs) v1 xa vs (tl ?frs') I"
    using clinit by simp
  have IH2: "PROP ?P (INIT C' (Cs,True) \<leftarrow> e') h' l' sh'' e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1 E C M
    pc ics v xa vs frs I" by fact
  have "P \<turnstile> (None,h,?frs,sh) -jvm\<rightarrow> (None,h,create_init_frame P C\<^sub>0 # ?frs',sh)" by(rule jvm_Called)
  also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h',?frs',sh'')"
     using IH' Jcc_pieces_RInit_clinit[OF assms(1-2) pcs,of h' l' sh'] RInit\<^sub>1.hyps(3,4) by simp
  finally have jvm1: "P \<turnstile> (None,h,?frs,sh) -jvm\<rightarrow> (None,h',?frs',sh'')" .
  show ?case (is "(?e1 \<longrightarrow> ?jvm1) \<and> (?e2 \<longrightarrow> ?err)")
  proof(rule conjI)
    { assume val: ?e1
      note jvm1
      also have "P \<turnstile> (None,h',?frs',sh'') -jvm\<rightarrow> (None,h\<^sub>1,(vs,l,C,M,pc,Called [])#frs,sh\<^sub>1)"
        using IH2 Jcc_pieces_RInit_Init[OF assms(1-2) shC'' pcs,of h'] RInit\<^sub>1.hyps(5) loc val by auto
      finally have ?jvm1 using pcs clinit by simp
    }
    thus "?e1 \<longrightarrow> ?jvm1" by simp
  next
    { assume throw: ?e2
      note jvm1
      also obtain vs' where "P \<turnstile> (None,h',?frs',sh'')
                     -jvm\<rightarrow> handle P C M xa h\<^sub>1 (vs'@vs) l pc ics frs sh\<^sub>1"
        using IH2 Jcc_pieces_RInit_Init[OF assms(1-2) shC'' pcs,of h'] RInit\<^sub>1.hyps(5) loc throw by auto
      finally have ?err using pcs clinit by auto
    }
    thus "?e2 \<longrightarrow> ?err" by simp
  qed
next
  case (RInitInitFail\<^sub>1 e h l sh a h' l' sh' C\<^sub>0 sfs i sh'' D Cs e' e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1)
  let ?frs = "(vs,l,C,M,pc,Called (C\<^sub>0#D#Cs)) # frs"
  let ?frs' = "(vs,l,C,M,pc,Called (D#Cs)) # frs"
  let "?frsT" = "\<lambda>xa1. (vs,l,C,M,pc,Throwing (C\<^sub>0#D#Cs) xa1) # frs"
  let "?frsT'" = "\<lambda>xa1. (vs,l,C,M,pc,Throwing (D#Cs) xa1) # frs"
  obtain xa' where xa': "throw a = Throw xa'"
    by (metis RInitInitFail\<^sub>1.hyps(1) eval\<^sub>1_final exp.distinct(101) final_def)
  have e\<^sub>1: "e\<^sub>1 = Throw xa'" using xa' rinit\<^sub>1_throw RInitInitFail\<^sub>1.hyps(5) by simp
  show ?case
  proof(cases "e = C\<^sub>0\<bullet>\<^sub>sclinit([])")
    case clinit: True
    then obtain err where pcs: "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs sh I h\<^sub>1 l\<^sub>1 sh\<^sub>1 v xa'
       (RI (C\<^sub>0,C\<^sub>0\<bullet>\<^sub>sclinit([])) ; D # Cs \<leftarrow> e')
      = (True, ?frs, (None, h\<^sub>1, (vs, l, C, M, pc, Called []) # frs, sh\<^sub>1), err)"
      using RInitInitFail\<^sub>1.prems(1) by simp
    have loc: "l = l'" using clinit\<^sub>1_loc_pres RInitInitFail\<^sub>1.hyps(1) clinit by simp
    have IH: "PROP ?P e h l sh (throw a) h' l' sh' E C M pc (Called (D#Cs)) v xa' vs frs I"
     by fact
    then have IH':
     "PROP ?P (C\<^sub>0\<bullet>\<^sub>sclinit([])) h l sh (Throw xa') h' l' sh' E C M pc (Called (D#Cs)) v xa' vs
       frs I"  using clinit xa' by simp
    have IH2: "PROP ?P (RI (D,throw a) ; Cs \<leftarrow> e') h' l' sh'' e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1 E C M
      pc ics v xa' vs frs I" by fact
    have "P \<turnstile> (None,h,?frs,sh) -jvm\<rightarrow> (None,h,create_init_frame P C\<^sub>0 # ?frs',sh)" by(rule jvm_Called)
    also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h',(vs, l, C, M, pc, Throwing (D#Cs) xa') # frs,sh'')"
      using IH' Jcc_pieces_RInit_clinit[OF assms(1-2) pcs,of h' l' sh'] RInitInitFail\<^sub>1.hyps(3,4)
        by simp
    also obtain vs'' where "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M xa' h\<^sub>1 (vs''@vs) l pc ics frs sh\<^sub>1"
      using IH2 pcs Jcc_pieces_RInit_RInit[OF assms(1) pcs] RInitInitFail\<^sub>1.hyps(3,4)
        xa' loc e\<^sub>1 xa' by clarsimp
    finally show ?thesis using pcs e\<^sub>1 clinit by auto
  next
    case throw: False
    then have eT: "e = Throw xa'" "h = h'" "l = l'" "sh = sh'" using xa' RInitInitFail\<^sub>1.prems(1)
      eval\<^sub>1_final_same[OF RInitInitFail\<^sub>1.hyps(1)] by clarsimp+
    obtain a' where "class P\<^sub>1 C\<^sub>0 = \<lfloor>a'\<rfloor>" using RInitInitFail\<^sub>1.prems by(auto simp: is_class_def)
    then obtain stk' loc' M' pc' ics' where "create_init_frame P C\<^sub>0 = (stk',loc',C\<^sub>0,M',pc',ics')"
      using create_init_frame_wf_eq[OF wf] by(cases "create_init_frame P C\<^sub>0", simp)
    then obtain rhs err where pcs: "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs sh I h' l' sh'' v xa'
       (RI (C\<^sub>0,e) ; D#Cs \<leftarrow> e') = (True, ?frsT xa', rhs, err)"
      using RInitInitFail\<^sub>1.prems(1) eT by clarsimp
    have IH2: "PROP ?P (RI (D,throw a) ; Cs \<leftarrow> e') h' l' sh'' e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1 E C M
      pc ics v xa' vs frs I" by fact
    have "P \<turnstile> (None,h,?frsT xa',sh') -jvm\<rightarrow> (None,h,?frsT' xa',sh'(C\<^sub>0 \<mapsto> (fst (the (sh' C\<^sub>0)), Error)))"
      by(rule jvm_Throwing)
    also obtain vs' where "P \<turnstile> ... -jvm\<rightarrow> handle P C M xa' h\<^sub>1 (vs'@vs) l pc ics frs sh\<^sub>1"
      using IH2 Jcc_pieces_RInit_RInit[OF assms(1) pcs] RInitInitFail\<^sub>1.hyps(3,4)
       eT e\<^sub>1 xa' by clarsimp
    finally show ?thesis using pcs e\<^sub>1 throw eT by auto
  qed
next
  case (RInitFailFinal\<^sub>1 e h l sh a h' l' sh' C\<^sub>0 sfs i sh'' e'')
  let ?frs = "(vs,l,C,M,pc,Called [C\<^sub>0]) # frs"
  let ?frs' = "(vs,l,C,M,pc,Called []) # frs"
  let "?frsT" = "\<lambda>xa1. (vs,l,C,M,pc,Throwing [C\<^sub>0] xa1) # frs"
  let "?frsT'" = "\<lambda>xa1. (vs,l,C,M,pc,Throwing [] xa1) # frs"
  obtain xa' where xa': "throw a = Throw xa'"
    by (metis RInitFailFinal\<^sub>1.hyps(1) eval\<^sub>1_final exp.distinct(101) final_def)
  show ?case
  proof(cases "e = C\<^sub>0\<bullet>\<^sub>sclinit([])")
    case clinit: True
    then obtain err where pcs: "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs sh I h' l' sh'' v xa'
       (RI (C\<^sub>0,C\<^sub>0\<bullet>\<^sub>sclinit([])) ; [] \<leftarrow> unit) = (True, ?frs, (None, h', ?frs', sh''), err)"
      using RInitFailFinal\<^sub>1.prems(1) by clarsimp
    have IH: "PROP ?P e h l sh (throw a) h' l' sh' E C M pc (Called []) v xa' vs frs I" by fact
    then have IH':
     "PROP ?P (C\<^sub>0\<bullet>\<^sub>sclinit([])) h l sh (throw a) h' l' sh' E C M pc (Called []) v xa' vs frs I"
      using clinit by simp
    have "P \<turnstile> (None,h,?frs,sh) -jvm\<rightarrow> (None,h,create_init_frame P C\<^sub>0 # ?frs',sh)"
      by(rule jvm_Called)
    also have "P \<turnstile> \<dots> -jvm\<rightarrow> (None,h',?frsT' xa',sh'')"
      using IH' Jcc_pieces_RInit_clinit[OF assms(1-2) pcs,of h' l' sh'] xa'
        RInitFailFinal\<^sub>1.hyps(3,4) by simp
    also have
       "P \<turnstile> \<dots> -jvm\<rightarrow> handle (compP compMb\<^sub>2 P\<^sub>1) C M xa' h' vs l pc No_ics frs sh''"
      using RInitFailFinal\<^sub>1.hyps(3,4) jvm_RInit_throw[where h=h' and sh=sh''] by simp
    finally show ?thesis using xa' pcs clinit by(clarsimp intro!: exI[where x="[]"])
  next
    case throw: False
    then have eT: "e = Throw xa'" "h = h'" "sh = sh'" using xa' RInitFailFinal\<^sub>1.prems(1)
      eval\<^sub>1_final_same[OF RInitFailFinal\<^sub>1.hyps(1)] by clarsimp+
    obtain a where "class P\<^sub>1 C\<^sub>0 = \<lfloor>a\<rfloor>" using RInitFailFinal\<^sub>1.prems by(auto simp: is_class_def)
    then obtain stk' loc' M' pc' ics' where "create_init_frame P C\<^sub>0 = (stk',loc',C\<^sub>0,M',pc',ics')"
      using create_init_frame_wf_eq[OF wf] by(cases "create_init_frame P C\<^sub>0", simp)
    then obtain rhs err where pcs: "Jcc_pieces P\<^sub>1 E C M h vs l pc ics frs sh I h' l' sh'' v xa'
       (RI (C\<^sub>0,e) ; [] \<leftarrow> unit) = (True, ?frsT xa', rhs, err)"
      using RInitFailFinal\<^sub>1.prems(1) eT by clarsimp
    have "P \<turnstile> (None,h,?frsT xa',sh) -jvm\<rightarrow> (None,h,?frsT' xa',sh(C\<^sub>0 \<mapsto> (fst (the (sh C\<^sub>0)), Error)))"
      by(rule jvm_Throwing)
    also have "P \<turnstile> \<dots> -jvm\<rightarrow> handle P C M xa' h' vs l pc No_ics frs sh''"
      using RInitFailFinal\<^sub>1.hyps(3,4) jvm_RInit_throw[where h=h and sh=sh''] eT by simp
    finally show ?thesis using pcs xa' by(clarsimp intro!: exI[where x="[]"])
  qed
qed
(*>*)

(*FIXME move! *)
lemma atLeast0AtMost[simp]: "{0::nat..n} = {..n}"
by auto

lemma atLeast0LessThan[simp]: "{0::nat..<n} = {..<n}"
by auto

fun exception :: "'a exp \<Rightarrow> addr option" where
  "exception (Throw a) = Some a"
| "exception e = None"

lemma comp\<^sub>2_correct:
assumes wf: "wf_J\<^sub>1_prog P\<^sub>1"
    and "method": "P\<^sub>1 \<turnstile> C sees M,b:Ts\<rightarrow>T = body in C"
    and eval:   "P\<^sub>1 \<turnstile>\<^sub>1 \<langle>body,(h,ls,sh)\<rangle> \<Rightarrow> \<langle>e',(h',ls',sh')\<rangle>"
    and nclinit: "M \<noteq> clinit"
shows "compP\<^sub>2 P\<^sub>1 \<turnstile> (None,h,[([],ls,C,M,0,No_ics)],sh) -jvm\<rightarrow> (exception e',h',[],sh')"
(*<*)
      (is "_ \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> ?\<sigma>\<^sub>1")
proof -
  let ?P = "compP\<^sub>2 P\<^sub>1"
  let ?E = "case b of Static \<Rightarrow> Ts | NonStatic \<Rightarrow> Class C#Ts"
  have nsub: "\<not>sub_RI body" using sees_wf\<^sub>1_nsub_RI[OF wf method] by simp
  have code: "?P,C,M,0 \<rhd> compE\<^sub>2 body" using beforeM[OF "method"] by auto
  have xtab: "?P,C,M \<rhd> compxE\<^sub>2 body 0 (size[])/{..<size(compE\<^sub>2 body)},size[]"
    using beforexM[OF "method"] by auto
  have cond: "Jcc_cond P\<^sub>1 ?E C M [] 0 No_ics {..<size(compE\<^sub>2 body)} h sh body"
    using nsub_RI_Jcc_pieces nsub code xtab by auto
  \<comment> \<open>Distinguish if e' is a value or an exception\<close>
  { fix v assume [simp]: "e' = Val v"
    have "?P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> (None,h',[([v],ls',C,M,size(compE\<^sub>2 body),No_ics)],sh')"
      using Jcc[OF wf eval cond] nsub_RI_Jcc_pieces[OF _ nsub] by auto
    also have "?P \<turnstile> \<dots> -jvm\<rightarrow> ?\<sigma>\<^sub>1" using beforeM[OF "method"] nclinit by auto
    finally have ?thesis .
  }
  moreover
  { fix a assume [simp]: "e' = Throw a"
    obtain pc vs' where pc: "0 \<le> pc \<and> pc < size(compE\<^sub>2 body) \<and>
          \<not> caught ?P pc h' a (compxE\<^sub>2 body 0 0)"
    and 1: "?P \<turnstile> ?\<sigma>\<^sub>0 -jvm\<rightarrow> handle ?P C M a h' vs' ls' pc No_ics [] sh'"
      using Jcc[OF wf eval cond] nsub_RI_Jcc_pieces[OF _ nsub] by auto meson
    from pc have "handle ?P C M a h' vs' ls' pc No_ics [] sh' = ?\<sigma>\<^sub>1" using xtab "method" nclinit
      by(auto simp:handle_def compMb\<^sub>2_def)
    with 1 have ?thesis by simp
  } 
  ultimately show ?thesis using eval\<^sub>1_final[OF eval] by(auto simp:final_def)
qed
(*>*)

end
