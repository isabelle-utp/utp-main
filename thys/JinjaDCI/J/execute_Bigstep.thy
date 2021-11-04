(*  Title:      Jinja/J/execute_Bigstep.thy
    Author:     Tobias Nipkow
    Copyright   2004 Technische Universitaet Muenchen
    Expanded to include statics by Susannah Mansky
    2017, UIUC
*)

section \<open> Code Generation For BigStep \<close>

theory execute_Bigstep
imports
  BigStep Examples
  "HOL-Library.Code_Target_Numeral"
begin

definition not_Done :: "cname \<Rightarrow> sheap \<Rightarrow> bool" where
"not_Done C sh \<equiv> sh C = None \<or> (\<exists>sfs i. sh C = Some(sfs,i) \<and> i \<noteq> Done)"

lemma not_Done_conv:
 "(\<nexists>sfs. sh C = Some(sfs,Done)) = (not_Done C sh)"
apply(unfold not_Done_def)
apply(case_tac "sh C", simp) apply (rename_tac sfsi)
apply(case_tac sfsi, clarsimp)
done

(* HERE: MOVE - MethodsAndFields? *)
(* HERE: to be computable, this also needs a def for when has_fields DNE:
  such a thing exists in counter-form in MaF, but uses subcls/requires
  something to be true of something above C - there are only finite things
  above C, but this still might require some work (like proving finiteness *)
definition no_field :: "J_prog \<Rightarrow> cname \<Rightarrow> vname \<Rightarrow> cname \<Rightarrow> bool" where
"no_field P C F D \<equiv> (\<forall>FDTs. \<not> P \<turnstile> C has_fields FDTs) \<or> (\<exists>FDTs. P \<turnstile> C has_fields FDTs \<and>
            ((map_of (map (\<lambda>((F,D),b,T). (F,(D,b,T))) FDTs) F = None) \<or>
             (\<exists>D' b T. D \<noteq> D' \<and> map_of (map (\<lambda>((F,D),b,T). (F,(D,b,T))) FDTs) F = Some(D',b,T))))"

lemma no_field_conv:
 "(\<not>(\<exists>b t. P \<turnstile> C sees F,b:t in D)) = no_field P C F D"
apply(unfold no_field_def sees_field_def)
apply(case_tac "\<exists>FDTs. P \<turnstile> C has_fields FDTs")
 defer apply simp
apply(rule iffI)
 apply clarsimp
 apply(erule_tac x=FDTs in allE, clarsimp) apply(rename_tac D' b' t')
 apply(erule disjE, simp)
 apply fastforce
apply clarsimp
apply(erule disjE,simp)
apply clarsimp
apply((drule (1) has_fields_fun)+, simp)
done

inductive map_val :: "expr list \<Rightarrow> val list \<Rightarrow> bool"
where
  Nil: "map_val [] []"
| Cons: "map_val xs ys \<Longrightarrow> map_val (Val y # xs) (y # ys)"

inductive map_val2 :: "expr list \<Rightarrow> val list \<Rightarrow> expr list \<Rightarrow> bool"
where
  Nil: "map_val2 [] [] []"
| Cons: "map_val2 xs ys zs \<Longrightarrow> map_val2 (Val y # xs) (y # ys) zs"
| Throw: "map_val2 (throw e # xs) [] (throw e # xs)"

theorem map_val_conv: "(xs = map Val ys) = map_val xs ys"
(*<*)
proof -
  have "\<And>ys. xs = map Val ys \<Longrightarrow> map_val xs ys"
    apply (induct xs type:list)
    apply (case_tac ys)
    apply simp
    apply (rule map_val.Nil)
    apply simp
    apply (case_tac ys)
    apply simp
    apply simp
    apply (erule conjE)
    apply (rule map_val.Cons)
    apply simp
    done
  moreover have "map_val xs ys \<Longrightarrow> xs = map Val ys"
    by (erule map_val.induct) simp+
  ultimately show ?thesis ..
qed
(*>*)

theorem map_val2_conv:
 "(xs = map Val ys @ throw e # zs) = map_val2 xs ys (throw e # zs)"
(*<*)
proof -
  have "\<And>ys. xs = map Val ys @ throw e # zs \<Longrightarrow> map_val2 xs ys (throw e # zs)"
    apply (induct xs type:list)
    apply (case_tac ys)
    apply simp
    apply simp
    apply simp
    apply (case_tac ys)
    apply simp
    apply (rule map_val2.Throw)
    apply simp
    apply (rule map_val2.Cons)
    apply simp
    done
  moreover have "map_val2 xs ys (throw e # zs) \<Longrightarrow> xs = map Val ys @ throw e # zs"
    by (erule map_val2.induct) simp+
  ultimately show ?thesis ..
qed
(*>*)

lemma NewInit2:
  "\<lbrakk> not_Done C sh; P \<turnstile> \<langle>C,(h,sh)\<rangle> \<Rightarrow>\<^sub>i \<langle>None,(h',sh')\<rangle>;
     new_Addr h' = Some a; h'' = h'(a\<mapsto>blank P C) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>new C,(h,l,sh)\<rangle> \<Rightarrow> \<langle>addr a,(h'',l,sh')\<rangle>"
apply(rule NewInit)
apply(simp add: not_Done_conv[symmetric])
apply(assumption+)
done

lemma NewInitFail2:
  "\<lbrakk> not_Done C sh; P \<turnstile> \<langle>C,(h,sh)\<rangle> \<Rightarrow>\<^sub>i \<langle>Some e',(h',sh')\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>new C,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',(h',l,sh')\<rangle>"
apply(rule NewInitFail)
apply(simp add: not_Done_conv[symmetric])
apply(assumption+)
done

lemma NewInitOOM2:
  "\<lbrakk> not_Done C sh; P \<turnstile> \<langle>C,(h,sh)\<rangle> \<Rightarrow>\<^sub>i \<langle>None,(h',sh')\<rangle>;
     new_Addr h = None \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>new C,(h,l,sh)\<rangle> \<Rightarrow> \<langle>THROW OutOfMemory,(h',l,sh')\<rangle>"
apply(rule NewInitOOM)
apply(simp add: not_Done_conv[symmetric])
apply(assumption+)
done

(*| FAccNone:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,(h,l,sh)\<rangle>; h a = Some(C,fs);
    \<not>(\<exists>b t. P \<turnstile> C sees F,b:t in D) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>F{D},s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NoSuchFieldError,(h,l,sh)\<rangle>"*)

lemma SFAccInit2:
  "\<lbrakk> P \<turnstile> C sees F,Static:t in D;
     not_Done D sh; P \<turnstile> \<langle>D,(h,sh)\<rangle> \<Rightarrow>\<^sub>i \<langle>None,(h',sh')\<rangle>;
     sh' D = Some (sfs',Done); sfs' F = Some v \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D},(h,l,sh)\<rangle> \<Rightarrow> \<langle>Val v,(h',l,sh')\<rangle>"
apply(rule SFAccInit, assumption+)
apply(simp add: not_Done_conv[symmetric])
apply(assumption+)
done

lemma SFAccInitFail2:
  "\<lbrakk> P \<turnstile> C sees F,Static:t in D;
     not_Done D sh; P \<turnstile> \<langle>D,(h,sh)\<rangle> \<Rightarrow>\<^sub>i \<langle>Some e',(h',sh')\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D},(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',(h',l,sh')\<rangle>"
apply(rule SFAccInitFail, assumption+)
apply(simp add: not_Done_conv[symmetric])
apply(assumption+)
done

(*| SFAccNone:
  "\<lbrakk> \<not>(\<exists>b t. P \<turnstile> C sees F,b:t in D) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D},s\<rangle> \<Rightarrow> \<langle>THROW NoSuchFieldError,s\<rangle>"

| FAssNone:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>;
     h\<^sub>2 a = Some(C,fs); \<not>(\<exists>b t. P \<turnstile> C sees F,b:t in D) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NoSuchFieldError,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>"*)

lemma SFAssInit2:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>1,l\<^sub>1,sh\<^sub>1)\<rangle>;
     P \<turnstile> C sees F,Static:t in D;
     not_Done D sh\<^sub>1; P \<turnstile> \<langle>D,(h\<^sub>1,sh\<^sub>1)\<rangle> \<Rightarrow>\<^sub>i \<langle>None,(h\<^sub>2,sh\<^sub>2)\<rangle>;
     sh\<^sub>2 D = Some(sfs\<^sub>2,Done); sfs\<^sub>2' = sfs\<^sub>2(F\<mapsto>v); sh\<^sub>2' = sh\<^sub>2(D\<mapsto>(sfs\<^sub>2',Done)) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>2,l\<^sub>1,sh\<^sub>2')\<rangle>"
apply(rule SFAssInit, assumption+)
apply(simp add: not_Done_conv[symmetric])
apply(assumption+)
done

lemma SFAssInitFail2:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>1,l\<^sub>1,sh\<^sub>1)\<rangle>;
     P \<turnstile> C sees F,Static:t in D;
     not_Done D sh\<^sub>1; P \<turnstile> \<langle>D,(h\<^sub>1,sh\<^sub>1)\<rangle> \<Rightarrow>\<^sub>i \<langle>Some e',(h\<^sub>2,sh\<^sub>2)\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>2,l\<^sub>1,sh\<^sub>2)\<rangle>"
apply(rule SFAssInitFail, assumption+)
apply(simp add: not_Done_conv[symmetric])
apply(assumption+)
done

(*| SFAssNone:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>;
    \<not>(\<exists>b t. P \<turnstile> C sees F,b:t in D) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NoSuchFieldError,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>"*)

lemma CallNull2:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle>;  P \<turnstile> \<langle>ps,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>evs,s\<^sub>2\<rangle>; map_val evs vs \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^sub>2\<rangle>"
apply(rule CallNull, assumption+)
apply(simp add: map_val_conv[symmetric])
done

lemma CallNone2:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^sub>1\<rangle>;  P \<turnstile> \<langle>ps,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>evs,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>; map_val evs vs;
     h\<^sub>2 a = Some(C,fs); \<not>(\<exists>b Ts T m D. P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in D) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NoSuchMethodError,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>"
apply(rule CallNone, assumption+)
apply(simp add: map_val_conv[symmetric])
apply(assumption+)
done

lemma CallStatic2:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^sub>1\<rangle>;  P \<turnstile> \<langle>ps,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>evs,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>; map_val evs vs;
     h\<^sub>2 a = Some(C,fs); P \<turnstile> C sees M,Static:Ts\<rightarrow>T = m in D \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW IncompatibleClassChangeError,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>"
apply(rule CallStatic, assumption+)
apply(simp add: map_val_conv[symmetric])
apply(assumption+)
done

lemma CallParamsThrow2:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>; P \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>evs,s\<^sub>2\<rangle>;
     map_val2 evs vs (throw ex # es'') \<rbrakk>
   \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(es),s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2\<rangle>"
apply(rule eval_evals_init_rinit.CallParamsThrow, assumption+)
apply(simp add: map_val2_conv[symmetric])
done

lemma Call2:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^sub>1\<rangle>;  P \<turnstile> \<langle>ps,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>evs,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>;
     map_val evs vs;
     h\<^sub>2 a = Some(C,fs);  P \<turnstile> C sees M,NonStatic:Ts\<rightarrow>T = (pns,body) in D;
     length vs = length pns;  l\<^sub>2' = [this\<mapsto>Addr a, pns[\<mapsto>]vs];
     P \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2',sh\<^sub>2)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>3,sh\<^sub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>2,sh\<^sub>3)\<rangle>"
apply(rule Call, assumption+)
apply(simp add: map_val_conv[symmetric])
apply assumption+
done

lemma SCallParamsThrow2:
  "\<lbrakk> P \<turnstile> \<langle>es,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>evs,s\<^sub>2\<rangle>;
     map_val2 evs vs (throw ex # es'') \<rbrakk>
   \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sM(es),s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2\<rangle>"
apply(rule SCallParamsThrow)
apply(simp add: map_val2_conv[symmetric])
done

lemma SCallNone2:
  "\<lbrakk> P \<turnstile> \<langle>ps,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>evs,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>; map_val evs vs;
     \<not>(\<exists>b Ts T m D. P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in D) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sM(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NoSuchMethodError,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>"
apply(rule SCallNone)
apply(simp add: map_val_conv[symmetric])
apply assumption+
done

lemma SCallNonStatic2:
  "\<lbrakk> P \<turnstile> \<langle>ps,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>evs,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>; map_val evs vs;
     P \<turnstile> C sees M,NonStatic:Ts\<rightarrow>T = m in D;
     sh\<^sub>2 D = Some(sfs,Done) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sM(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW IncompatibleClassChangeError,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>"
apply(rule SCallNonStatic)
apply(simp add: map_val_conv[symmetric])
apply assumption+
done

lemma SCallInit2:
  "\<lbrakk> P \<turnstile> \<langle>ps,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>evs,(h\<^sub>1,l\<^sub>1,sh\<^sub>1)\<rangle>; map_val evs vs;
     P \<turnstile> C sees M,Static:Ts\<rightarrow>T = (pns,body) in D;
     not_Done D sh\<^sub>1;
     P \<turnstile> \<langle>D,(h\<^sub>1,sh\<^sub>1)\<rangle> \<Rightarrow>\<^sub>i \<langle>None,(h\<^sub>2,sh\<^sub>2)\<rangle>;
     length vs = length pns;  l\<^sub>2' = [pns[\<mapsto>]vs];
     P \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2',sh\<^sub>2)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>3,sh\<^sub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sM(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>1,sh\<^sub>3)\<rangle>"
apply(rule SCallInit)
apply(simp add: map_val_conv[symmetric])
apply assumption
apply(clarsimp simp: not_Done_def)
apply assumption+
done

lemma SCallInitFail2:
  "\<lbrakk> P \<turnstile> \<langle>ps,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>evs,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>; map_val evs vs;
     P \<turnstile> C sees M,Static:Ts\<rightarrow>T = (pns,body) in D;
     not_Done D sh\<^sub>2;
     P \<turnstile> \<langle>D,(h\<^sub>2,sh\<^sub>2)\<rangle> \<Rightarrow>\<^sub>i \<langle>Some e',(h\<^sub>3,sh\<^sub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sM(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>2,sh\<^sub>3)\<rangle>"
apply(rule SCallInitFail)
apply(simp add: map_val_conv[symmetric])
apply assumption
apply(clarsimp simp: not_Done_def)
apply assumption+
done

lemma SCall2:
  "\<lbrakk> P \<turnstile> \<langle>ps,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>evs,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>;
     map_val evs vs;
     P \<turnstile> C sees M,Static:Ts\<rightarrow>T = (pns,body) in D;
     sh\<^sub>2 D = Some(sfs,Done);
     length vs = length pns;  l\<^sub>2' = [pns[\<mapsto>]vs];
     P \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2',sh\<^sub>2)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>3,sh\<^sub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sM(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>2,sh\<^sub>3)\<rangle>"
apply(rule SCall)
apply(simp add: map_val_conv[symmetric])
apply assumption+
done

declare not_Done_def [code_pred_def]

code_pred 
  (modes: i \<Rightarrow> o \<Rightarrow> bool)
  map_val 
.

code_pred
  (modes: i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)
  map_val2
.

lemmas [code_pred_intro] =
 eval_evals_init_rinit.New eval_evals_init_rinit.NewOOM
 eval_evals_init_rinit.Cast eval_evals_init_rinit.CastNull eval_evals_init_rinit.CastFail eval_evals_init_rinit.CastThrow
 eval_evals_init_rinit.Val eval_evals_init_rinit.Var
 eval_evals_init_rinit.BinOp eval_evals_init_rinit.BinOpThrow1 eval_evals_init_rinit.BinOpThrow2
 eval_evals_init_rinit.LAss eval_evals_init_rinit.LAssThrow
 eval_evals_init_rinit.FAcc eval_evals_init_rinit.FAccNull eval_evals_init_rinit.FAccThrow
 eval_evals_init_rinit.FAccNone eval_evals_init_rinit.FAccStatic
 eval_evals_init_rinit.SFAcc eval_evals_init_rinit.SFAccNone eval_evals_init_rinit.SFAccNonStatic
 eval_evals_init_rinit.FAss eval_evals_init_rinit.FAssNull
 eval_evals_init_rinit.FAssThrow1 eval_evals_init_rinit.FAssThrow2
 eval_evals_init_rinit.FAssNone eval_evals_init_rinit.FAssStatic
 eval_evals_init_rinit.SFAss eval_evals_init_rinit.SFAssNone eval_evals_init_rinit.SFAssNonStatic
 eval_evals_init_rinit.CallObjThrow

declare NewInit2 [code_pred_intro NewInit2]
declare NewInitFail2 [code_pred_intro NewInitFail2]
declare NewInitOOM2 [code_pred_intro NewInitOOM2]
declare SFAccInit2 [code_pred_intro SFAccInit2]
declare SFAccInitFail2 [code_pred_intro SFAccInitFail2]
declare SFAssInit2 [code_pred_intro SFAssInit2]
declare SFAssInitFail2 [code_pred_intro SFAssInitFail2]
declare CallNull2 [code_pred_intro CallNull2]
declare CallParamsThrow2 [code_pred_intro CallParamsThrow2]
declare CallNone2 [code_pred_intro CallNone2]
declare CallStatic2 [code_pred_intro CallStatic2]
declare Call2 [code_pred_intro Call2]
declare SCallParamsThrow2 [code_pred_intro SCallParamsThrow2]
declare SCallNone2 [code_pred_intro SCallNone2]
declare SCallNonStatic2 [code_pred_intro SCallNonStatic2]
declare SCallInit2 [code_pred_intro SCallInit2]
declare SCallInitFail2 [code_pred_intro SCallInitFail2]
declare SCall2 [code_pred_intro SCall2]

lemmas [code_pred_intro] =
 eval_evals_init_rinit.Block
 eval_evals_init_rinit.Seq eval_evals_init_rinit.SeqThrow
 eval_evals_init_rinit.CondT eval_evals_init_rinit.CondF eval_evals_init_rinit.CondThrow
 eval_evals_init_rinit.WhileF eval_evals_init_rinit.WhileT
 eval_evals_init_rinit.WhileCondThrow

declare eval_evals_init_rinit.WhileBodyThrow [code_pred_intro WhileBodyThrow2]

lemmas [code_pred_intro] =
 eval_evals_init_rinit.Throw eval_evals_init_rinit.ThrowNull
 eval_evals_init_rinit.ThrowThrow
 eval_evals_init_rinit.Try eval_evals_init_rinit.TryCatch eval_evals_init_rinit.TryThrow
 eval_evals_init_rinit.Nil eval_evals_init_rinit.Cons eval_evals_init_rinit.ConsThrow

lemmas [code_pred_intro] =
 eval_evals_init_rinit.InitNone eval_evals_init_rinit.InitDone
 eval_evals_init_rinit.InitProcessing eval_evals_init_rinit.InitError
 eval_evals_init_rinit.InitObject eval_evals_init_rinit.InitNonObject eval_evals_init_rinit.InitFail
 eval_evals_init_rinit.RInit eval_evals_init_rinit.RinitFail

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool as execute)
(* [show_steps,
  show_proof_trace,
  show_intermediate_results,
  show_mode_inference,
  show_modes,
  show_compilation,
  show_invalid_clauses]*)
  eval
proof -
  case eval
  from eval.prems show thesis
  proof(cases (no_simp))
    case NewInit thus ?thesis
      by-(rule eval.NewInit2[OF refl],simp_all add: not_Done_conv[symmetric])
  next
    case NewInitFail thus ?thesis
      by-(rule eval.NewInitFail2[OF refl],simp_all add: not_Done_conv[symmetric])
  next
    case NewInitOOM thus ?thesis
      by-(rule eval.NewInitOOM2[OF refl],simp_all add: not_Done_conv[symmetric])
  next
    case SFAccInit thus ?thesis
      using eval.SFAccInit2 not_Done_conv by auto
  next
    case SFAccInitFail thus ?thesis
      by-(rule eval.SFAccInitFail2[OF refl],simp_all add: not_Done_conv[symmetric])
  next
    case SFAssInit thus ?thesis
      using eval.SFAssInit2 not_Done_conv by auto
  next
    case SFAssInitFail thus ?thesis
      by-(rule eval.SFAssInitFail2[OF refl],simp_all add: not_Done_conv[symmetric])
  next
    case CallNull thus ?thesis
      by(rule eval.CallNull2[OF refl])(simp add: map_val_conv[symmetric])
  next
    case CallParamsThrow thus ?thesis
      by(rule eval.CallParamsThrow2[OF refl])(simp add: map_val2_conv[symmetric])
  next
    case CallNone thus ?thesis
      using eval.CallNone2[OF refl] map_val_conv[symmetric] by auto
  next
    case CallStatic thus ?thesis
      using eval.CallStatic2 map_val_conv by blast
  next
    case Call thus ?thesis
      by -(rule eval.Call2[OF refl], simp_all add: map_val_conv[symmetric])
  next
    case SCallParamsThrow thus ?thesis
      by(rule eval.SCallParamsThrow2[OF refl])(simp add: map_val2_conv[symmetric])
  next
    case SCallNone thus ?thesis
      by -(rule eval.SCallNone2[OF refl], simp_all add: map_val_conv[symmetric])
  next
    case SCallNonStatic thus ?thesis
      using eval.SCallNonStatic2 map_val_conv by blast
  next
    case SCallInit thus ?thesis
      by -(rule eval.SCallInit2[OF refl], simp_all add: map_val_conv[symmetric] not_Done_conv[symmetric])
  next
    case SCallInitFail thus ?thesis
      by -(rule eval.SCallInitFail2[OF refl], simp_all add: map_val_conv[symmetric] not_Done_conv[symmetric])
  next
    case SCall thus ?thesis
      by -(rule eval.SCall2[OF refl], simp_all add: map_val_conv[symmetric])
  next
    case WhileBodyThrow thus ?thesis by(rule eval.WhileBodyThrow2[OF refl])
  qed(assumption|erule (4) eval.that[OF refl]|erule (3) eval.that[OF refl])+
next
  case evals
  from evals.prems show thesis
    by(cases (no_simp))(assumption|erule (3) evals.that[OF refl])+
next
  case init
  from init.prems show thesis
    by(cases (no_simp))(assumption|erule (3) init.that[OF refl])+
next
  case rinit
  from rinit.prems show thesis
    by(cases (no_simp))(assumption|erule (3) rinit.that[OF refl])+
qed

notation execute ("_ \<turnstile> ((1\<langle>_,/_\<rangle>) \<Rightarrow>/ \<langle>'_, '_\<rangle>)" [51,0,0] 81)

definition "test1 = [] \<turnstile> \<langle>testExpr1,(empty,empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
definition "test2 = [] \<turnstile> \<langle>testExpr2,(empty,empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
definition "test3 = [] \<turnstile> \<langle>testExpr3,(empty,empty(''V''\<mapsto>Intg 77),empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
definition "test4 = [] \<turnstile> \<langle>testExpr4,(empty,empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
definition "test5 = [(''Object'',('''',[],[])),(''C'',(''Object'',[(''F'',NonStatic,Integer)],[]))] \<turnstile> \<langle>testExpr5,(empty,empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
definition "test6 = [(''Object'',('''',[],[])), classI] \<turnstile> \<langle>testExpr6,(empty,empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"

definition "V = ''V''"
definition "C = ''C''"
definition "F = ''F''"

(* HERE: MOVE THIS - also, don't really need *)
(*
lemma UNIV_staticb: "UNIV = {Static, NonStatic}"
  by (auto intro: staticb.exhaust)

instantiation staticb :: enum
begin

definition
  "enum_staticb = [Static, NonStatic]"

definition
  "enum_all_staticb P \<longleftrightarrow> P NonStatic \<and> P Static"

definition
  "enum_ex_staticb P \<longleftrightarrow> P NonStatic \<or> P Static"

instance proof
qed (auto simp only: enum_staticb_def enum_all_staticb_def enum_ex_staticb_def UNIV_staticb, simp_all)

end
*)

ML_val \<open>
  val SOME ((@{code Val} (@{code Intg} (@{code int_of_integer} 5)), _), _) = Predicate.yield @{code test1};
  val SOME ((@{code Val} (@{code Intg} (@{code int_of_integer} 11)), _), _) = Predicate.yield @{code test2};
  val SOME ((@{code Val} (@{code Intg} (@{code int_of_integer} 83)), _), _) = Predicate.yield @{code test3};

  val SOME ((_, (_, l, _)), _) = Predicate.yield @{code test4};
  val SOME (@{code Intg} (@{code int_of_integer} 6)) = l @{code V};

  val SOME ((_, (h, _)), _) = Predicate.yield @{code test5};
  val SOME (c, fs) = h (@{code nat_of_integer} 1);
  val SOME (obj, _) = h (@{code nat_of_integer} 0);
  val SOME (@{code Intg} i) = fs (@{code F}, @{code C});
  @{assert} (c = @{code C} andalso obj = @{code Object} andalso i = @{code int_of_integer} 42);

  val SOME ((@{code Val} (@{code Intg} (@{code int_of_integer} 160)), _), _) = Predicate.yield @{code test6};
\<close>

definition "test7 = [classObject, classL] \<turnstile> \<langle>testExpr_BuildList, (empty,empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"

definition "L = ''L''"
definition "N = ''N''"

ML_val \<open>
  val SOME ((_, (h, _)), _) = Predicate.yield @{code test7};
  val SOME (_, fs1) = h (@{code nat_of_integer} 0);
  val SOME (_, fs2) = h (@{code nat_of_integer} 1);
  val SOME (_, fs3) = h (@{code nat_of_integer} 2);
  val SOME (_, fs4) = h (@{code nat_of_integer} 3);

  val F = @{code "F"};
  val L = @{code "L"};
  val N = @{code "N"};

  @{assert} (fs1 (F, L) = SOME (@{code Intg} (@{code int_of_integer} 1)) andalso
     fs1 (N, L) = SOME (@{code Addr} (@{code nat_of_integer} 1)) andalso
     fs2 (F, L) = SOME (@{code Intg} (@{code int_of_integer} 2)) andalso
     fs2 (N, L) = SOME (@{code Addr} (@{code nat_of_integer} 2)) andalso
     fs3 (F, L) = SOME (@{code Intg} (@{code int_of_integer} 3)) andalso
     fs3 (N, L) = SOME (@{code Addr} (@{code nat_of_integer} 3)) andalso
     fs4 (F, L) = SOME (@{code Intg} (@{code int_of_integer} 4)) andalso
     fs4 (N, L) = SOME @{code Null});
\<close>

definition "test8 = [classObject, classA] \<turnstile> \<langle>testExpr_ClassA, (empty,empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
definition "i = ''int''"
definition "t = ''test''"
definition "A = ''A''"

ML_val \<open>
  val SOME ((_, (h, l)), _) = Predicate.yield @{code test8};
  val SOME (_, fs1) = h (@{code nat_of_integer} 0);
  val SOME (_, fs2) = h (@{code nat_of_integer} 1);

  val i = @{code "i"};
  val t = @{code "t"};
  val A = @{code "A"};

  @{assert} (fs1 (i, A) = SOME (@{code Intg} (@{code int_of_integer} 10)) andalso 
     fs1 (t, A) = SOME @{code Null} andalso
     fs2 (i, A) = SOME (@{code Intg} (@{code int_of_integer} 50)) andalso 
     fs2 (t, A) = SOME @{code Null});
\<close>

end

