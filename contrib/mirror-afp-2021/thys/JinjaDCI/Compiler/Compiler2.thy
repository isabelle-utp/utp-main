(*  Title:      JinjaDCI/Compiler/Compiler2.thy
    Author:     Tobias Nipkow, Susannah Mansky
    Copyright   TUM 2003, UIUC 2019-20

    Based on the Jinja theory Compiler/Compiler2.thy by Tobias Nipkow
*)

section \<open> Compilation Stage 2 \<close>

theory Compiler2
imports PCompiler J1 "../JVM/JVMExec"
begin

lemma bop_expr_length_aux [simp]:
 "length (case bop of Eq \<Rightarrow> [CmpEq] | Add \<Rightarrow> [IAdd]) = Suc 0"
 by(cases bop, simp+)

primrec compE\<^sub>2 :: "expr\<^sub>1 \<Rightarrow> instr list"
  and compEs\<^sub>2 :: "expr\<^sub>1 list \<Rightarrow> instr list" where
  "compE\<^sub>2 (new C) = [New C]"
| "compE\<^sub>2 (Cast C e) = compE\<^sub>2 e @ [Checkcast C]"
| "compE\<^sub>2 (Val v) = [Push v]"
| "compE\<^sub>2 (e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2) = compE\<^sub>2 e\<^sub>1 @ compE\<^sub>2 e\<^sub>2 @ 
  (case bop of Eq \<Rightarrow> [CmpEq]
            | Add \<Rightarrow> [IAdd])"
| "compE\<^sub>2 (Var i) = [Load i]"
| "compE\<^sub>2 (i:=e) = compE\<^sub>2 e @ [Store i, Push Unit]"
| "compE\<^sub>2 (e\<bullet>F{D}) = compE\<^sub>2 e @ [Getfield F D]"
| "compE\<^sub>2 (C\<bullet>\<^sub>sF{D}) = [Getstatic C F D]"
| "compE\<^sub>2 (e\<^sub>1\<bullet>F{D} := e\<^sub>2) =
       compE\<^sub>2 e\<^sub>1 @ compE\<^sub>2 e\<^sub>2 @ [Putfield F D, Push Unit]"
| "compE\<^sub>2 (C\<bullet>\<^sub>sF{D} := e\<^sub>2) =
       compE\<^sub>2 e\<^sub>2 @ [Putstatic C F D, Push Unit]"
| "compE\<^sub>2 (e\<bullet>M(es)) = compE\<^sub>2 e @ compEs\<^sub>2 es @ [Invoke M (size es)]"
| "compE\<^sub>2 (C\<bullet>\<^sub>sM(es)) = compEs\<^sub>2 es @ [Invokestatic C M (size es)]"
| "compE\<^sub>2 ({i:T; e}) = compE\<^sub>2 e"
| "compE\<^sub>2 (e\<^sub>1;;e\<^sub>2) = compE\<^sub>2 e\<^sub>1 @ [Pop] @ compE\<^sub>2 e\<^sub>2"
| "compE\<^sub>2 (if (e) e\<^sub>1 else e\<^sub>2) =
        (let cnd   = compE\<^sub>2 e;
             thn   = compE\<^sub>2 e\<^sub>1;
             els   = compE\<^sub>2 e\<^sub>2;
             test  = IfFalse (int(size thn + 2)); 
             thnex = Goto (int(size els + 1))
         in cnd @ [test] @ thn @ [thnex] @ els)"
| "compE\<^sub>2 (while (e) c) =
        (let cnd   = compE\<^sub>2 e;
             bdy   = compE\<^sub>2 c;
             test  = IfFalse (int(size bdy + 3)); 
             loop  = Goto (-int(size bdy + size cnd + 2))
         in cnd @ [test] @ bdy @ [Pop] @ [loop] @ [Push Unit])"
| "compE\<^sub>2 (throw e) = compE\<^sub>2 e @ [instr.Throw]"
| "compE\<^sub>2 (try e\<^sub>1 catch(C i) e\<^sub>2) =
   (let catch = compE\<^sub>2 e\<^sub>2
    in compE\<^sub>2 e\<^sub>1 @ [Goto (int(size catch)+2), Store i] @ catch)"
| "compE\<^sub>2 (INIT C (Cs,b) \<leftarrow> e) = []"
| "compE\<^sub>2 (RI(C,e);Cs \<leftarrow> e') = []"

| "compEs\<^sub>2 []     = []"
| "compEs\<^sub>2 (e#es) = compE\<^sub>2 e @ compEs\<^sub>2 es"

text\<open> Compilation of exception table. Is given start address of code
to compute absolute addresses necessary in exception table. \<close>

primrec compxE\<^sub>2  :: "expr\<^sub>1      \<Rightarrow> pc \<Rightarrow> nat \<Rightarrow> ex_table"
  and compxEs\<^sub>2 :: "expr\<^sub>1 list \<Rightarrow> pc \<Rightarrow> nat \<Rightarrow> ex_table" where
  "compxE\<^sub>2 (new C) pc d = []"
| "compxE\<^sub>2 (Cast C e) pc d = compxE\<^sub>2 e pc d"
| "compxE\<^sub>2 (Val v) pc d = []"
| "compxE\<^sub>2 (e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2) pc d =
   compxE\<^sub>2 e\<^sub>1 pc d @ compxE\<^sub>2 e\<^sub>2 (pc + size(compE\<^sub>2 e\<^sub>1)) (d+1)"
| "compxE\<^sub>2 (Var i) pc d = []"
| "compxE\<^sub>2 (i:=e) pc d = compxE\<^sub>2 e pc d"
| "compxE\<^sub>2 (e\<bullet>F{D}) pc d = compxE\<^sub>2 e pc d"
| "compxE\<^sub>2 (C\<bullet>\<^sub>sF{D}) pc d = []"
| "compxE\<^sub>2 (e\<^sub>1\<bullet>F{D} := e\<^sub>2) pc d =
   compxE\<^sub>2 e\<^sub>1 pc d @ compxE\<^sub>2 e\<^sub>2 (pc + size(compE\<^sub>2 e\<^sub>1)) (d+1)"
| "compxE\<^sub>2 (C\<bullet>\<^sub>sF{D} := e\<^sub>2) pc d = compxE\<^sub>2 e\<^sub>2 pc d"
| "compxE\<^sub>2 (e\<bullet>M(es)) pc d =
   compxE\<^sub>2 e pc d @ compxEs\<^sub>2 es (pc + size(compE\<^sub>2 e)) (d+1)"
| "compxE\<^sub>2 (C\<bullet>\<^sub>sM(es)) pc d = compxEs\<^sub>2 es pc d"
| "compxE\<^sub>2 ({i:T; e}) pc d = compxE\<^sub>2 e pc d"
| "compxE\<^sub>2 (e\<^sub>1;;e\<^sub>2) pc d =
   compxE\<^sub>2 e\<^sub>1 pc d @ compxE\<^sub>2 e\<^sub>2 (pc+size(compE\<^sub>2 e\<^sub>1)+1) d"
| "compxE\<^sub>2 (if (e) e\<^sub>1 else e\<^sub>2) pc d =
        (let pc\<^sub>1   = pc + size(compE\<^sub>2 e) + 1;
             pc\<^sub>2   = pc\<^sub>1 + size(compE\<^sub>2 e\<^sub>1) + 1
         in compxE\<^sub>2 e pc d @ compxE\<^sub>2 e\<^sub>1 pc\<^sub>1 d @ compxE\<^sub>2 e\<^sub>2 pc\<^sub>2 d)"
| "compxE\<^sub>2 (while (b) e) pc d =
   compxE\<^sub>2 b pc d @ compxE\<^sub>2 e (pc+size(compE\<^sub>2 b)+1) d"
| "compxE\<^sub>2 (throw e) pc d = compxE\<^sub>2 e pc d"
| "compxE\<^sub>2 (try e\<^sub>1 catch(C i) e\<^sub>2) pc d =
   (let pc\<^sub>1 = pc + size(compE\<^sub>2 e\<^sub>1)
    in compxE\<^sub>2 e\<^sub>1 pc d @ compxE\<^sub>2 e\<^sub>2 (pc\<^sub>1+2) d @ [(pc,pc\<^sub>1,C,pc\<^sub>1+1,d)])"
| "compxE\<^sub>2 (INIT C (Cs, b) \<leftarrow> e) pc d = []"
| "compxE\<^sub>2 (RI(C, e);Cs \<leftarrow> e') pc d = []"

| "compxEs\<^sub>2 [] pc d    = []"
| "compxEs\<^sub>2 (e#es) pc d = compxE\<^sub>2 e pc d @ compxEs\<^sub>2 es (pc+size(compE\<^sub>2 e)) (d+1)"

primrec max_stack :: "expr\<^sub>1 \<Rightarrow> nat"
  and max_stacks :: "expr\<^sub>1 list \<Rightarrow> nat" where
  "max_stack (new C) = 1"
| "max_stack (Cast C e) = max_stack e"
| "max_stack (Val v) = 1"
| "max_stack (e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2) = max (max_stack e\<^sub>1) (max_stack e\<^sub>2) + 1"
| "max_stack (Var i) = 1"
| "max_stack (i:=e) = max_stack e"
| "max_stack (e\<bullet>F{D}) = max_stack e"
| "max_stack (C\<bullet>\<^sub>sF{D}) = 1"
| "max_stack (e\<^sub>1\<bullet>F{D} := e\<^sub>2) = max (max_stack e\<^sub>1) (max_stack e\<^sub>2) + 1"
| "max_stack (C\<bullet>\<^sub>sF{D} := e\<^sub>2) = max_stack e\<^sub>2"
| "max_stack (e\<bullet>M(es)) = max (max_stack e) (max_stacks es) + 1"
| "max_stack (C\<bullet>\<^sub>sM(es)) = max_stacks es + 1"
| "max_stack ({i:T; e}) = max_stack e"
| "max_stack (e\<^sub>1;;e\<^sub>2) = max (max_stack e\<^sub>1) (max_stack e\<^sub>2)"
| "max_stack (if (e) e\<^sub>1 else e\<^sub>2) =
  max (max_stack e) (max (max_stack e\<^sub>1) (max_stack e\<^sub>2))"
| "max_stack (while (e) c) = max (max_stack e) (max_stack c)"
| "max_stack (throw e) = max_stack e"
| "max_stack (try e\<^sub>1 catch(C i) e\<^sub>2) = max (max_stack e\<^sub>1) (max_stack e\<^sub>2)"
 
| "max_stacks [] = 0"
| "max_stacks (e#es) = max (max_stack e) (1 + max_stacks es)"

lemma max_stack1': "\<not>sub_RI e \<Longrightarrow> 1 \<le> max_stack e"
(*<*)by(induct e) (simp_all add:max_def)(*>*)

lemma compE\<^sub>2_not_Nil': "\<not>sub_RI e \<Longrightarrow> compE\<^sub>2 e \<noteq> []"
(*<*)by(induct e) auto(*>*)

lemma compE\<^sub>2_nRet: "\<And>i. i \<in> set (compE\<^sub>2 e\<^sub>1) \<Longrightarrow> i \<noteq> Return"
 and "\<And>i. i \<in> set (compEs\<^sub>2 es\<^sub>1) \<Longrightarrow> i \<noteq> Return"
 by(induct rule: compE\<^sub>2.induct compEs\<^sub>2.induct, auto simp: nth_append split: bop.splits)


definition compMb\<^sub>2 :: "staticb \<Rightarrow> expr\<^sub>1 \<Rightarrow> jvm_method"
where
  "compMb\<^sub>2  \<equiv>  \<lambda>b body.
  let ins = compE\<^sub>2 body @ [Return];
      xt = compxE\<^sub>2 body 0 0
  in (max_stack body, max_vars body, ins, xt)"

definition compP\<^sub>2 :: "J\<^sub>1_prog \<Rightarrow> jvm_prog"
where
  "compP\<^sub>2  \<equiv>  compP compMb\<^sub>2"

(*<*)
declare compP\<^sub>2_def [simp]
(*>*)

lemma compMb\<^sub>2 [simp]:
  "compMb\<^sub>2 b e = (max_stack e, max_vars e,
                   compE\<^sub>2 e @ [Return], compxE\<^sub>2 e 0 0)"
(*<*)by (simp add: compMb\<^sub>2_def)(*>*)

end
