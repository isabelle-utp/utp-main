(*
(C) Copyright Andreas Viktor Hess, DTU, 2015-2020

All Rights Reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

- Redistributions of source code must retain the above copyright
  notice, this list of conditions and the following disclaimer.

- Redistributions in binary form must reproduce the above copyright
  notice, this list of conditions and the following disclaimer in the
  documentation and/or other materials provided with the distribution.

- Neither the name of the copyright holder nor the names of its
  contributors may be used to endorse or promote products
  derived from this software without specific prior written
  permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(*  Title:      Strands_and_Constraints.thy
    Author:     Andreas Viktor Hess, DTU
*)

section \<open>Strands and Symbolic Intruder Constraints\<close>
theory Strands_and_Constraints
imports Messages More_Unification Intruder_Deduction
begin

subsection \<open>Constraints, Strands and Related Definitions\<close>
datatype poscheckvariant = Assign ("assign") | Check ("check")

text \<open>
  A strand (or constraint) step is either a message transmission (either a message being sent \<open>Send\<close>
  or being received \<open>Receive\<close>) or a check on messages (a positive check \<open>Equality\<close>---which can be
  either an "assignment" or just a check---or a negative check \<open>Inequality\<close>)
\<close>
datatype (funs\<^sub>s\<^sub>t\<^sub>p: 'a, vars\<^sub>s\<^sub>t\<^sub>p: 'b) strand_step =
  Send       "('a,'b) term" ("send\<langle>_\<rangle>\<^sub>s\<^sub>t" 80)
| Receive    "('a,'b) term" ("receive\<langle>_\<rangle>\<^sub>s\<^sub>t" 80)
| Equality   poscheckvariant "('a,'b) term" "('a,'b) term" ("\<langle>_: _ \<doteq> _\<rangle>\<^sub>s\<^sub>t" [80,80])
| Inequality (bvars\<^sub>s\<^sub>t\<^sub>p: "'b list") "(('a,'b) term \<times> ('a,'b) term) list" ("\<forall>_\<langle>\<or>\<noteq>: _\<rangle>\<^sub>s\<^sub>t" [80,80])
where
  "bvars\<^sub>s\<^sub>t\<^sub>p (Send _) = []"
| "bvars\<^sub>s\<^sub>t\<^sub>p (Receive _) = []"
| "bvars\<^sub>s\<^sub>t\<^sub>p (Equality _ _ _) = []"

text \<open>
  A strand is a finite sequence of strand steps (constraints and strands share the same datatype)
\<close>
type_synonym ('a,'b) strand = "('a,'b) strand_step list"

type_synonym ('a,'b) strands = "('a,'b) strand set"

abbreviation "trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<equiv> \<Union>(t,t') \<in> set F. {t,t'}"

fun trms\<^sub>s\<^sub>t\<^sub>p::"('a,'b) strand_step \<Rightarrow> ('a,'b) terms" where
  "trms\<^sub>s\<^sub>t\<^sub>p (Send t) = {t}"
| "trms\<^sub>s\<^sub>t\<^sub>p (Receive t) = {t}"
| "trms\<^sub>s\<^sub>t\<^sub>p (Equality _ t t') = {t,t'}"
| "trms\<^sub>s\<^sub>t\<^sub>p (Inequality _ F) = trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F"

lemma vars\<^sub>s\<^sub>t\<^sub>p_unfold[simp]: "vars\<^sub>s\<^sub>t\<^sub>p x = fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t\<^sub>p x) \<union> set (bvars\<^sub>s\<^sub>t\<^sub>p x)"
by (cases x) auto

text \<open>The set of terms occurring in a strand\<close>
definition trms\<^sub>s\<^sub>t where "trms\<^sub>s\<^sub>t S \<equiv> \<Union>(trms\<^sub>s\<^sub>t\<^sub>p ` set S)"

fun trms_list\<^sub>s\<^sub>t\<^sub>p::"('a,'b) strand_step \<Rightarrow> ('a,'b) term list" where
  "trms_list\<^sub>s\<^sub>t\<^sub>p (Send t) = [t]"
| "trms_list\<^sub>s\<^sub>t\<^sub>p (Receive t) = [t]"
| "trms_list\<^sub>s\<^sub>t\<^sub>p (Equality _ t t') = [t,t']"
| "trms_list\<^sub>s\<^sub>t\<^sub>p (Inequality _ F) = concat (map (\<lambda>(t,t'). [t,t']) F)"

text \<open>The set of terms occurring in a strand (list variant)\<close>
definition trms_list\<^sub>s\<^sub>t where "trms_list\<^sub>s\<^sub>t S \<equiv> remdups (concat (map trms_list\<^sub>s\<^sub>t\<^sub>p S))"

text \<open>The set of variables occurring in a sent message\<close>
definition fv\<^sub>s\<^sub>n\<^sub>d::"('a,'b) strand_step \<Rightarrow> 'b set" where
  "fv\<^sub>s\<^sub>n\<^sub>d x \<equiv> case x of Send t \<Rightarrow> fv t | _ \<Rightarrow> {}"

text \<open>The set of variables occurring in a received message\<close>
definition fv\<^sub>r\<^sub>c\<^sub>v::"('a,'b) strand_step \<Rightarrow> 'b set" where
  "fv\<^sub>r\<^sub>c\<^sub>v x \<equiv> case x of Receive t \<Rightarrow> fv t | _ \<Rightarrow> {}"

text \<open>The set of variables occurring in an equality constraint\<close>
definition fv\<^sub>e\<^sub>q::"poscheckvariant \<Rightarrow> ('a,'b) strand_step \<Rightarrow> 'b set" where
  "fv\<^sub>e\<^sub>q ac x \<equiv> case x of Equality ac' s t \<Rightarrow> if ac = ac' then fv s \<union> fv t else {} | _ \<Rightarrow> {}"

text \<open>The set of variables occurring at the left-hand side of an equality constraint\<close>
definition fv_l\<^sub>e\<^sub>q::"poscheckvariant \<Rightarrow> ('a,'b) strand_step \<Rightarrow> 'b set" where
  "fv_l\<^sub>e\<^sub>q ac x \<equiv> case x of Equality ac' s t \<Rightarrow> if ac = ac' then fv s else {} | _ \<Rightarrow> {}"

text \<open>The set of variables occurring at the right-hand side of an equality constraint\<close>
definition fv_r\<^sub>e\<^sub>q::"poscheckvariant \<Rightarrow> ('a,'b) strand_step \<Rightarrow> 'b set" where
  "fv_r\<^sub>e\<^sub>q ac x \<equiv> case x of Equality ac' s t \<Rightarrow> if ac = ac' then fv t else {} | _ \<Rightarrow> {}"

text \<open>The free variables of inequality constraints\<close>
definition fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q::"('a,'b) strand_step \<Rightarrow> 'b set" where
  "fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q x \<equiv> case x of Inequality X F \<Rightarrow> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X | _ \<Rightarrow> {}"

fun fv\<^sub>s\<^sub>t\<^sub>p::"('a,'b) strand_step \<Rightarrow> 'b set" where
  "fv\<^sub>s\<^sub>t\<^sub>p (Send t) = fv t"
| "fv\<^sub>s\<^sub>t\<^sub>p (Receive t) = fv t"
| "fv\<^sub>s\<^sub>t\<^sub>p (Equality _ t t') = fv t \<union> fv t'"
| "fv\<^sub>s\<^sub>t\<^sub>p (Inequality X F) = (\<Union>(t,t') \<in> set F. fv t \<union> fv t') - set X"

text \<open>The set of free variables of a strand\<close>
definition fv\<^sub>s\<^sub>t::"('a,'b) strand \<Rightarrow> 'b set" where
  "fv\<^sub>s\<^sub>t S \<equiv> \<Union>(set (map fv\<^sub>s\<^sub>t\<^sub>p S))"

text \<open>The set of bound variables of a strand\<close>
definition bvars\<^sub>s\<^sub>t::"('a,'b) strand \<Rightarrow> 'b set" where
  "bvars\<^sub>s\<^sub>t S \<equiv> \<Union>(set (map (set \<circ> bvars\<^sub>s\<^sub>t\<^sub>p) S))"

text \<open>The set of all variables occurring in a strand\<close>
definition vars\<^sub>s\<^sub>t::"('a,'b) strand \<Rightarrow> 'b set" where
  "vars\<^sub>s\<^sub>t S \<equiv> \<Union>(set (map vars\<^sub>s\<^sub>t\<^sub>p S))"

abbreviation wfrestrictedvars\<^sub>s\<^sub>t\<^sub>p::"('a,'b) strand_step \<Rightarrow> 'b set" where
  "wfrestrictedvars\<^sub>s\<^sub>t\<^sub>p x \<equiv>
    case x of Inequality _ _ \<Rightarrow> {} | Equality Check _ _ \<Rightarrow> {} | _ \<Rightarrow> vars\<^sub>s\<^sub>t\<^sub>p x"

text \<open>The variables of a strand whose occurrences might be restricted by well-formedness constraints\<close>
definition wfrestrictedvars\<^sub>s\<^sub>t::"('a,'b) strand \<Rightarrow> 'b set" where
  "wfrestrictedvars\<^sub>s\<^sub>t S \<equiv> \<Union>(set (map wfrestrictedvars\<^sub>s\<^sub>t\<^sub>p S))"

abbreviation wfvarsoccs\<^sub>s\<^sub>t\<^sub>p where
  "wfvarsoccs\<^sub>s\<^sub>t\<^sub>p x \<equiv> case x of Send t \<Rightarrow> fv t | Equality Assign s t \<Rightarrow> fv s | _ \<Rightarrow> {}"

text \<open>The variables of a strand that occur in sent messages or as variables in assignments\<close>
definition wfvarsoccs\<^sub>s\<^sub>t where
  "wfvarsoccs\<^sub>s\<^sub>t S \<equiv> \<Union>(set (map wfvarsoccs\<^sub>s\<^sub>t\<^sub>p S))"

text \<open>The variables occurring at the right-hand side of assignment steps\<close>
fun assignment_rhs\<^sub>s\<^sub>t where
  "assignment_rhs\<^sub>s\<^sub>t [] = {}"
| "assignment_rhs\<^sub>s\<^sub>t (Equality Assign t t'#S) = insert t' (assignment_rhs\<^sub>s\<^sub>t S)"
| "assignment_rhs\<^sub>s\<^sub>t (x#S) = assignment_rhs\<^sub>s\<^sub>t S"

text \<open>The set function symbols occurring in a strand\<close>
definition funs\<^sub>s\<^sub>t::"('a,'b) strand \<Rightarrow> 'a set" where
  "funs\<^sub>s\<^sub>t S \<equiv> \<Union>(set (map funs\<^sub>s\<^sub>t\<^sub>p S))"

fun subst_apply_strand_step::"('a,'b) strand_step \<Rightarrow> ('a,'b) subst \<Rightarrow> ('a,'b) strand_step"
  (infix "\<cdot>\<^sub>s\<^sub>t\<^sub>p" 51) where
  "Send t \<cdot>\<^sub>s\<^sub>t\<^sub>p \<theta> = Send (t \<cdot> \<theta>)"
| "Receive t \<cdot>\<^sub>s\<^sub>t\<^sub>p \<theta> = Receive (t \<cdot> \<theta>)"
| "Equality a t t' \<cdot>\<^sub>s\<^sub>t\<^sub>p \<theta> = Equality a (t \<cdot> \<theta>) (t' \<cdot> \<theta>)"
| "Inequality X F \<cdot>\<^sub>s\<^sub>t\<^sub>p \<theta> = Inequality X (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<theta>)"

text \<open>Substitution application for strands\<close>
definition subst_apply_strand::"('a,'b) strand \<Rightarrow> ('a,'b) subst \<Rightarrow> ('a,'b) strand"
  (infix "\<cdot>\<^sub>s\<^sub>t" 51) where
  "S \<cdot>\<^sub>s\<^sub>t \<theta> \<equiv> map (\<lambda>x. x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<theta>) S"

text \<open>The semantics of inequality constraints\<close>
definition
  "ineq_model (\<I>::('a,'b) subst) X F \<equiv>
      (\<forall>\<delta>. subst_domain \<delta> = set X \<and> ground (subst_range \<delta>) \<longrightarrow> 
              list_ex (\<lambda>f. fst f \<cdot> (\<delta> \<circ>\<^sub>s \<I>) \<noteq> snd f \<cdot> (\<delta> \<circ>\<^sub>s \<I>)) F)"

fun simple\<^sub>s\<^sub>t\<^sub>p where
  "simple\<^sub>s\<^sub>t\<^sub>p (Receive t) = True"
| "simple\<^sub>s\<^sub>t\<^sub>p (Send (Var v)) = True"
| "simple\<^sub>s\<^sub>t\<^sub>p (Inequality X F) = (\<exists>\<I>. ineq_model \<I> X F)"
| "simple\<^sub>s\<^sub>t\<^sub>p _ = False"

text \<open>Simple constraints\<close>
definition simple where "simple S \<equiv> list_all simple\<^sub>s\<^sub>t\<^sub>p S"

text \<open>The intruder knowledge of a constraint\<close>
fun ik\<^sub>s\<^sub>t::"('a,'b) strand \<Rightarrow> ('a,'b) terms" where
  "ik\<^sub>s\<^sub>t [] = {}"
| "ik\<^sub>s\<^sub>t (Receive t#S) = insert t (ik\<^sub>s\<^sub>t S)"
| "ik\<^sub>s\<^sub>t (_#S) = ik\<^sub>s\<^sub>t S"

text \<open>Strand well-formedness\<close>
fun wf\<^sub>s\<^sub>t::"'b set \<Rightarrow> ('a,'b) strand \<Rightarrow> bool" where
  "wf\<^sub>s\<^sub>t V [] = True"
| "wf\<^sub>s\<^sub>t V (Receive t#S) = (fv t \<subseteq> V \<and> wf\<^sub>s\<^sub>t V S)"
| "wf\<^sub>s\<^sub>t V (Send t#S) = wf\<^sub>s\<^sub>t (V \<union> fv t) S"
| "wf\<^sub>s\<^sub>t V (Equality Assign s t#S) = (fv t \<subseteq> V \<and> wf\<^sub>s\<^sub>t (V \<union> fv s) S)"
| "wf\<^sub>s\<^sub>t V (Equality Check s t#S) = wf\<^sub>s\<^sub>t V S"
| "wf\<^sub>s\<^sub>t V (Inequality _ _#S) = wf\<^sub>s\<^sub>t V S"

text \<open>Well-formedness of constraint states\<close>
definition wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r::"('a,'b) strand \<Rightarrow> ('a,'b) subst \<Rightarrow> bool" where
  "wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S \<theta> \<equiv> (wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta> \<and> wf\<^sub>s\<^sub>t {} S \<and> subst_domain \<theta> \<inter> vars\<^sub>s\<^sub>t S = {} \<and>
                  range_vars \<theta> \<inter> bvars\<^sub>s\<^sub>t S = {} \<and> fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>s\<^sub>t S = {})"

declare trms\<^sub>s\<^sub>t_def[simp]
declare fv\<^sub>s\<^sub>n\<^sub>d_def[simp]
declare fv\<^sub>r\<^sub>c\<^sub>v_def[simp]
declare fv\<^sub>e\<^sub>q_def[simp]
declare fv_l\<^sub>e\<^sub>q_def[simp]
declare fv_r\<^sub>e\<^sub>q_def[simp]
declare fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q_def[simp]
declare fv\<^sub>s\<^sub>t_def[simp]
declare vars\<^sub>s\<^sub>t_def[simp]
declare bvars\<^sub>s\<^sub>t_def[simp]
declare wfrestrictedvars\<^sub>s\<^sub>t_def[simp]
declare wfvarsoccs\<^sub>s\<^sub>t_def[simp]

lemmas wf\<^sub>s\<^sub>t_induct = wf\<^sub>s\<^sub>t.induct[case_names Nil ConsRcv ConsSnd ConsEq ConsEq2 ConsIneq]
lemmas ik\<^sub>s\<^sub>t_induct = ik\<^sub>s\<^sub>t.induct[case_names Nil ConsRcv ConsSnd ConsEq ConsIneq]
lemmas assignment_rhs\<^sub>s\<^sub>t_induct = assignment_rhs\<^sub>s\<^sub>t.induct[case_names Nil ConsEq2 ConsSnd ConsRcv ConsEq ConsIneq]
  

subsubsection \<open>Lexicographical measure on strands\<close>
definition size\<^sub>s\<^sub>t::"('a,'b) strand \<Rightarrow> nat" where
  "size\<^sub>s\<^sub>t S \<equiv> size_list (\<lambda>x. Max (insert 0 (size ` trms\<^sub>s\<^sub>t\<^sub>p x))) S"

definition measure\<^sub>s\<^sub>t::"((('a, 'b) strand \<times> ('a,'b) subst) \<times> ('a, 'b) strand \<times> ('a,'b) subst) set"
where
  "measure\<^sub>s\<^sub>t \<equiv> measures [\<lambda>(S,\<theta>). card (fv\<^sub>s\<^sub>t S), \<lambda>(S,\<theta>). size\<^sub>s\<^sub>t S]"

lemma measure\<^sub>s\<^sub>t_alt_def:
  "((s,x),(t,y)) \<in> measure\<^sub>s\<^sub>t =
      (card (fv\<^sub>s\<^sub>t s) < card (fv\<^sub>s\<^sub>t t) \<or> (card (fv\<^sub>s\<^sub>t s) = card (fv\<^sub>s\<^sub>t t) \<and> size\<^sub>s\<^sub>t s < size\<^sub>s\<^sub>t t))"
by (simp add: measure\<^sub>s\<^sub>t_def size\<^sub>s\<^sub>t_def)

lemma measure\<^sub>s\<^sub>t_trans: "trans measure\<^sub>s\<^sub>t"
by (simp add: trans_def measure\<^sub>s\<^sub>t_def size\<^sub>s\<^sub>t_def)


subsubsection \<open>Some lemmata\<close>
lemma trms_list\<^sub>s\<^sub>t_is_trms\<^sub>s\<^sub>t: "trms\<^sub>s\<^sub>t S = set (trms_list\<^sub>s\<^sub>t S)"
unfolding trms\<^sub>s\<^sub>t_def trms_list\<^sub>s\<^sub>t_def
proof (induction S)
  case (Cons x S) thus ?case by (cases x) auto
qed simp

lemma subst_apply_strand_step_def:
  "s \<cdot>\<^sub>s\<^sub>t\<^sub>p \<theta> = (case s of
    Send t \<Rightarrow> Send (t \<cdot> \<theta>)
  | Receive t \<Rightarrow> Receive (t \<cdot> \<theta>)
  | Equality a t t' \<Rightarrow> Equality a (t \<cdot> \<theta>) (t' \<cdot> \<theta>)
  | Inequality X F \<Rightarrow> Inequality X (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<theta>))"
by (cases s) simp_all

lemma subst_apply_strand_nil[simp]: "[] \<cdot>\<^sub>s\<^sub>t \<delta> = []"
unfolding subst_apply_strand_def by simp

lemma finite_funs\<^sub>s\<^sub>t\<^sub>p[simp]: "finite (funs\<^sub>s\<^sub>t\<^sub>p x)" by (cases x) auto
lemma finite_funs\<^sub>s\<^sub>t[simp]: "finite (funs\<^sub>s\<^sub>t S)" unfolding funs\<^sub>s\<^sub>t_def by simp
lemma finite_trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s[simp]: "finite (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s x)" by (induct x) auto
lemma finite_trms\<^sub>s\<^sub>t\<^sub>p[simp]: "finite (trms\<^sub>s\<^sub>t\<^sub>p x)" by (cases x) auto
lemma finite_vars\<^sub>s\<^sub>t\<^sub>p[simp]: "finite (vars\<^sub>s\<^sub>t\<^sub>p x)" by auto
lemma finite_bvars\<^sub>s\<^sub>t\<^sub>p[simp]: "finite (set (bvars\<^sub>s\<^sub>t\<^sub>p x))" by rule
lemma finite_fv\<^sub>s\<^sub>n\<^sub>d[simp]: "finite (fv\<^sub>s\<^sub>n\<^sub>d x)" by (cases x) auto
lemma finite_fv\<^sub>r\<^sub>c\<^sub>v[simp]: "finite (fv\<^sub>r\<^sub>c\<^sub>v x)" by (cases x) auto
lemma finite_fv\<^sub>s\<^sub>t\<^sub>p[simp]: "finite (fv\<^sub>s\<^sub>t\<^sub>p x)" by (cases x) auto
lemma finite_vars\<^sub>s\<^sub>t[simp]: "finite (vars\<^sub>s\<^sub>t S)" by simp
lemma finite_bvars\<^sub>s\<^sub>t[simp]: "finite (bvars\<^sub>s\<^sub>t S)" by simp
lemma finite_fv\<^sub>s\<^sub>t[simp]: "finite (fv\<^sub>s\<^sub>t S)" by simp

lemma finite_wfrestrictedvars\<^sub>s\<^sub>t\<^sub>p[simp]: "finite (wfrestrictedvars\<^sub>s\<^sub>t\<^sub>p x)"
by (cases x) (auto split: poscheckvariant.splits)

lemma finite_wfrestrictedvars\<^sub>s\<^sub>t[simp]: "finite (wfrestrictedvars\<^sub>s\<^sub>t S)"
using finite_wfrestrictedvars\<^sub>s\<^sub>t\<^sub>p by auto

lemma finite_wfvarsoccs\<^sub>s\<^sub>t\<^sub>p[simp]: "finite (wfvarsoccs\<^sub>s\<^sub>t\<^sub>p x)"
by (cases x) (auto split: poscheckvariant.splits)

lemma finite_wfvarsoccs\<^sub>s\<^sub>t[simp]: "finite (wfvarsoccs\<^sub>s\<^sub>t S)"
using finite_wfvarsoccs\<^sub>s\<^sub>t\<^sub>p by auto

lemma finite_ik\<^sub>s\<^sub>t[simp]: "finite (ik\<^sub>s\<^sub>t S)"
by (induct S rule: ik\<^sub>s\<^sub>t.induct) simp_all

lemma finite_assignment_rhs\<^sub>s\<^sub>t[simp]: "finite (assignment_rhs\<^sub>s\<^sub>t S)"
by (induct S rule: assignment_rhs\<^sub>s\<^sub>t.induct) simp_all

lemma ik\<^sub>s\<^sub>t_is_rcv_set: "ik\<^sub>s\<^sub>t A = {t. Receive t \<in> set A}"
by (induct A rule: ik\<^sub>s\<^sub>t.induct) auto

lemma ik\<^sub>s\<^sub>tD[dest]: "t \<in> ik\<^sub>s\<^sub>t S \<Longrightarrow> Receive t \<in> set S"
by (induct S rule: ik\<^sub>s\<^sub>t.induct) auto

lemma ik\<^sub>s\<^sub>tD'[dest]: "t \<in> ik\<^sub>s\<^sub>t S \<Longrightarrow> t \<in> trms\<^sub>s\<^sub>t S"
by (induct S rule: ik\<^sub>s\<^sub>t.induct) auto

lemma ik\<^sub>s\<^sub>tD''[dest]: "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>s\<^sub>t S) \<Longrightarrow> t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t S)"
by (induct S rule: ik\<^sub>s\<^sub>t.induct) auto

lemma ik\<^sub>s\<^sub>t_subterm_exD:
  assumes "t \<in> ik\<^sub>s\<^sub>t S"
  shows "\<exists>x \<in> set S. t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t\<^sub>p x)"
using assms ik\<^sub>s\<^sub>tD by force

lemma assignment_rhs\<^sub>s\<^sub>tD[dest]: "t \<in> assignment_rhs\<^sub>s\<^sub>t S \<Longrightarrow> \<exists>t'. Equality Assign t' t \<in> set S"
by (induct S rule: assignment_rhs\<^sub>s\<^sub>t.induct) auto

lemma assignment_rhs\<^sub>s\<^sub>tD'[dest]: "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (assignment_rhs\<^sub>s\<^sub>t S) \<Longrightarrow> t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t S)"
by (induct S rule: assignment_rhs\<^sub>s\<^sub>t.induct) auto

lemma bvars\<^sub>s\<^sub>t_split: "bvars\<^sub>s\<^sub>t (S@S') = bvars\<^sub>s\<^sub>t S \<union> bvars\<^sub>s\<^sub>t S'"
unfolding bvars\<^sub>s\<^sub>t_def by auto

lemma bvars\<^sub>s\<^sub>t_singleton: "bvars\<^sub>s\<^sub>t [x] = set (bvars\<^sub>s\<^sub>t\<^sub>p x)"
unfolding bvars\<^sub>s\<^sub>t_def by auto

lemma strand_fv_bvars_disjointD:
  assumes "fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>s\<^sub>t S = {}" "Inequality X F \<in> set S"
  shows "set X \<subseteq> bvars\<^sub>s\<^sub>t S" "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X \<subseteq> fv\<^sub>s\<^sub>t S"
using assms by (induct S) fastforce+

lemma strand_fv_bvars_disjoint_unfold:
  assumes "fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>s\<^sub>t S = {}" "Inequality X F \<in> set S" "Inequality Y G \<in> set S"
  shows "set Y \<inter> (fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X) = {}"
proof -
  have "set X \<subseteq> bvars\<^sub>s\<^sub>t S" "set Y \<subseteq> bvars\<^sub>s\<^sub>t S"
       "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X \<subseteq> fv\<^sub>s\<^sub>t S" "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G - set Y \<subseteq> fv\<^sub>s\<^sub>t S"
    using strand_fv_bvars_disjointD[OF assms(1)] assms(2,3) by auto
  thus ?thesis using assms(1) by fastforce
qed

lemma strand_subst_hom[iff]:
  "(S@S') \<cdot>\<^sub>s\<^sub>t \<theta> = (S \<cdot>\<^sub>s\<^sub>t \<theta>)@(S' \<cdot>\<^sub>s\<^sub>t \<theta>)" "(x#S) \<cdot>\<^sub>s\<^sub>t \<theta> = (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<theta>)#(S \<cdot>\<^sub>s\<^sub>t \<theta>)"
unfolding subst_apply_strand_def by auto

lemma strand_subst_comp: "range_vars \<delta> \<inter> bvars\<^sub>s\<^sub>t S = {} \<Longrightarrow> S \<cdot>\<^sub>s\<^sub>t \<delta> \<circ>\<^sub>s \<theta> = ((S \<cdot>\<^sub>s\<^sub>t \<delta>) \<cdot>\<^sub>s\<^sub>t \<theta>)"
proof (induction S)
  case (Cons x S)
  have *: "range_vars \<delta> \<inter> bvars\<^sub>s\<^sub>t S = {}" "range_vars \<delta> \<inter> (set (bvars\<^sub>s\<^sub>t\<^sub>p x)) = {}"
    using Cons bvars\<^sub>s\<^sub>t_split[of "[x]" S] append_Cons inf_sup_absorb
    by (metis (no_types, lifting) Int_iff Un_commute disjoint_iff_not_equal self_append_conv2,
        metis append_self_conv2 bvars\<^sub>s\<^sub>t_singleton inf_bot_right inf_left_commute) 
  hence IH: "S \<cdot>\<^sub>s\<^sub>t \<delta> \<circ>\<^sub>s \<theta> = (S \<cdot>\<^sub>s\<^sub>t \<delta>) \<cdot>\<^sub>s\<^sub>t \<theta>" using Cons.IH by auto
  have "(x#S \<cdot>\<^sub>s\<^sub>t \<delta> \<circ>\<^sub>s \<theta>) = (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta> \<circ>\<^sub>s \<theta>)#(S \<cdot>\<^sub>s\<^sub>t \<delta> \<circ>\<^sub>s \<theta>)" by (metis strand_subst_hom(2))
  hence "... = (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta> \<circ>\<^sub>s \<theta>)#((S \<cdot>\<^sub>s\<^sub>t \<delta>) \<cdot>\<^sub>s\<^sub>t \<theta>)" by (metis IH)
  hence "... = ((x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) \<cdot>\<^sub>s\<^sub>t\<^sub>p \<theta>)#((S \<cdot>\<^sub>s\<^sub>t \<delta>) \<cdot>\<^sub>s\<^sub>t \<theta>)" using rm_vars_comp[OF *(2)]
  proof (induction x)
    case (Inequality X F) thus ?case
      by (induct F) (auto simp add: subst_apply_pairs_def subst_apply_strand_step_def)
  qed (simp_all add: subst_apply_strand_step_def)
  thus ?case using IH by auto
qed (simp add: subst_apply_strand_def)

lemma strand_substI[intro]:
  "subst_domain \<theta> \<inter> fv\<^sub>s\<^sub>t S = {} \<Longrightarrow> S \<cdot>\<^sub>s\<^sub>t \<theta> = S"
  "subst_domain \<theta> \<inter> vars\<^sub>s\<^sub>t S = {} \<Longrightarrow> S \<cdot>\<^sub>s\<^sub>t \<theta> = S"
proof -
  show "subst_domain \<theta> \<inter> vars\<^sub>s\<^sub>t S = {} \<Longrightarrow> S \<cdot>\<^sub>s\<^sub>t \<theta> = S"
  proof (induction S)
    case (Cons x S)
    hence "S \<cdot>\<^sub>s\<^sub>t \<theta> = S" by auto
    moreover have "vars\<^sub>s\<^sub>t\<^sub>p x \<inter> subst_domain \<theta> = {}" using Cons.prems by auto
    hence "x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<theta> = x"
    proof (induction x)
      case (Inequality X F) thus ?case
        by (induct F) (force simp add: subst_apply_pairs_def)+
    qed auto
    ultimately show ?case by simp
  qed (simp add: subst_apply_strand_def)

  show "subst_domain \<theta> \<inter> fv\<^sub>s\<^sub>t S = {} \<Longrightarrow> S \<cdot>\<^sub>s\<^sub>t \<theta> = S"
  proof (induction S)
    case (Cons x S)
    hence "S \<cdot>\<^sub>s\<^sub>t \<theta> = S" by auto
    moreover have "fv\<^sub>s\<^sub>t\<^sub>p x \<inter> subst_domain \<theta> = {}"
      using Cons.prems by auto
    hence "x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<theta> = x"
    proof (induction x)
      case (Inequality X F) thus ?case
        by (induct F) (force simp add: subst_apply_pairs_def)+
    qed auto
    ultimately show ?case by simp
  qed (simp add: subst_apply_strand_def)
qed

lemma strand_substI':
  "fv\<^sub>s\<^sub>t S = {} \<Longrightarrow> S \<cdot>\<^sub>s\<^sub>t \<theta> = S"
  "vars\<^sub>s\<^sub>t S = {} \<Longrightarrow> S \<cdot>\<^sub>s\<^sub>t \<theta> = S"
by (metis inf_bot_right strand_substI(1),
    metis inf_bot_right strand_substI(2))

lemma strand_subst_set: "(set (S \<cdot>\<^sub>s\<^sub>t \<theta>)) = ((\<lambda>x. x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<theta>) ` (set S))"
by (auto simp add: subst_apply_strand_def)

lemma strand_map_inv_set_snd_rcv_subst:
  assumes "finite (M::('a,'b) terms)"
  shows "set ((map Send (inv set M)) \<cdot>\<^sub>s\<^sub>t \<theta>) = Send ` (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)" (is ?A)
        "set ((map Receive (inv set M)) \<cdot>\<^sub>s\<^sub>t \<theta>) = Receive ` (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)" (is ?B)
proof -
  { fix f::"('a,'b) term \<Rightarrow> ('a,'b) strand_step" assume f: "f = Send \<or> f = Receive"
    from assms have "set ((map f (inv set M)) \<cdot>\<^sub>s\<^sub>t \<theta>) = f ` (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)"
    proof (induction rule: finite_induct)
      case empty thus ?case unfolding inv_def by auto
    next
      case (insert m M)
      have "set (map f (inv set (insert m M)) \<cdot>\<^sub>s\<^sub>t \<theta>) =
            insert (f m \<cdot>\<^sub>s\<^sub>t\<^sub>p \<theta>) (set (map f (inv set M) \<cdot>\<^sub>s\<^sub>t \<theta>))"
        by (simp add: insert.hyps(1) inv_set_fset subst_apply_strand_def)
      thus ?case using f insert.IH by auto
    qed
  }
  thus "?A" "?B" by auto
qed

lemma strand_ground_subst_vars_subset:
  assumes "ground (subst_range \<theta>)" shows "vars\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<theta>) \<subseteq> vars\<^sub>s\<^sub>t S"
proof (induction S)
  case (Cons x S)
  have "vars\<^sub>s\<^sub>t\<^sub>p (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<theta>) \<subseteq> vars\<^sub>s\<^sub>t\<^sub>p x" using ground_subst_fv_subset[OF assms] 
  proof (cases x)
    case (Inequality X F)
    let ?\<theta> = "rm_vars (set X) \<theta>"
    have "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ?\<theta>) \<subseteq> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F"
    proof (induction F)
      case (Cons f F)
      obtain t t' where f: "f = (t,t')" by (metis surj_pair)
      hence "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (f#F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ?\<theta>) = fv (t \<cdot> ?\<theta>) \<union> fv (t' \<cdot> ?\<theta>) \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ?\<theta>)"
            "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (f#F) = fv t \<union> fv t' \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F"
        by (auto simp add: subst_apply_pairs_def)
      thus ?case
        using ground_subst_fv_subset[OF ground_subset[OF rm_vars_img_subset assms, of "set X"]]
              Cons.IH
        by (metis (no_types, lifting) Un_mono)
    qed (simp add: subst_apply_pairs_def)
    moreover have
        "vars\<^sub>s\<^sub>t\<^sub>p (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<theta>) = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<theta>) \<union> set X"
        "vars\<^sub>s\<^sub>t\<^sub>p x = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> set X"
      using Inequality
      by (auto simp add: subst_apply_pairs_def)
    ultimately show ?thesis by auto
  qed auto
  thus ?case using Cons.IH by auto
qed (simp add: subst_apply_strand_def)

lemma ik_union_subset: "\<Union>(P ` ik\<^sub>s\<^sub>t S) \<subseteq> (\<Union>x \<in> (set S). \<Union>(P ` trms\<^sub>s\<^sub>t\<^sub>p x))"
by (induct S rule: ik\<^sub>s\<^sub>t.induct) auto

lemma ik_snd_empty[simp]: "ik\<^sub>s\<^sub>t (map Send X) = {}"
by (induct "map Send X" arbitrary: X rule: ik\<^sub>s\<^sub>t.induct) auto

lemma ik_snd_empty'[simp]: "ik\<^sub>s\<^sub>t [Send t] = {}" by simp

lemma ik_append[iff]: "ik\<^sub>s\<^sub>t (S@S') = ik\<^sub>s\<^sub>t S \<union> ik\<^sub>s\<^sub>t S'" by (induct S rule: ik\<^sub>s\<^sub>t.induct) auto

lemma ik_cons: "ik\<^sub>s\<^sub>t (x#S) = ik\<^sub>s\<^sub>t [x] \<union> ik\<^sub>s\<^sub>t S" using ik_append[of "[x]" S] by simp

lemma assignment_rhs_append[iff]: "assignment_rhs\<^sub>s\<^sub>t (S@S') = assignment_rhs\<^sub>s\<^sub>t S \<union> assignment_rhs\<^sub>s\<^sub>t S'"
by (induct S rule: assignment_rhs\<^sub>s\<^sub>t.induct) auto

lemma eqs_rcv_map_empty: "assignment_rhs\<^sub>s\<^sub>t (map Receive M) = {}"
by auto

lemma ik_rcv_map: assumes "t \<in> set L" shows "t \<in> ik\<^sub>s\<^sub>t (map Receive L)"
proof -
  { fix L L' 
    have "t \<in> ik\<^sub>s\<^sub>t [Receive t]" by auto
    hence "t \<in> ik\<^sub>s\<^sub>t (map Receive L@Receive t#map Receive L')" using ik_append by auto
    hence "t \<in> ik\<^sub>s\<^sub>t (map Receive (L@t#L'))" by auto
  }
  thus ?thesis using assms split_list_last by force 
qed

lemma ik_subst: "ik\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>) = ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>"
by (induct rule: ik\<^sub>s\<^sub>t_induct) auto

lemma ik_rcv_map': assumes "t \<in> ik\<^sub>s\<^sub>t (map Receive L)" shows "t \<in> set L"
using assms by force

lemma ik_append_subset[simp]: "ik\<^sub>s\<^sub>t S \<subseteq> ik\<^sub>s\<^sub>t (S@S')" "ik\<^sub>s\<^sub>t S' \<subseteq> ik\<^sub>s\<^sub>t (S@S')"
by (induct S rule: ik\<^sub>s\<^sub>t.induct) auto

lemma assignment_rhs_append_subset[simp]:
  "assignment_rhs\<^sub>s\<^sub>t S \<subseteq> assignment_rhs\<^sub>s\<^sub>t (S@S')"
  "assignment_rhs\<^sub>s\<^sub>t S' \<subseteq> assignment_rhs\<^sub>s\<^sub>t (S@S')"
by (induct S rule: assignment_rhs\<^sub>s\<^sub>t.induct) auto

lemma trms\<^sub>s\<^sub>t_cons: "trms\<^sub>s\<^sub>t (x#S) = trms\<^sub>s\<^sub>t\<^sub>p x \<union> trms\<^sub>s\<^sub>t S" by simp

lemma trm_strand_subst_cong:
  "t \<in> trms\<^sub>s\<^sub>t S \<Longrightarrow> t \<cdot> \<delta> \<in> trms\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>)
    \<or> (\<exists>X F. Inequality X F \<in> set S \<and> t \<cdot> rm_vars (set X) \<delta> \<in> trms\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>))"
    (is "t \<in> trms\<^sub>s\<^sub>t S \<Longrightarrow> ?P t \<delta> S")
  "t \<in> trms\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>) \<Longrightarrow> (\<exists>t'. t = t' \<cdot> \<delta> \<and> t' \<in> trms\<^sub>s\<^sub>t S)
    \<or> (\<exists>X F. Inequality X F \<in> set S \<and> (\<exists>t' \<in> trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F. t = t' \<cdot> rm_vars (set X) \<delta>))"
    (is "t \<in> trms\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>) \<Longrightarrow> ?Q t \<delta> S")
proof -
  show "t \<in> trms\<^sub>s\<^sub>t S \<Longrightarrow> ?P t \<delta> S"
  proof (induction S)
    case (Cons x S) show ?case
    proof (cases "t \<in> trms\<^sub>s\<^sub>t S")
      case True
      hence "?P t \<delta> S" using Cons by simp
      thus ?thesis
        by (cases x)
           (metis (no_types, lifting) Un_iff list.set_intros(2) strand_subst_hom(2) trms\<^sub>s\<^sub>t_cons)+
    next
      case False
      hence "t \<in> trms\<^sub>s\<^sub>t\<^sub>p x" using Cons.prems by auto
      thus ?thesis
      proof (induction x)
        case (Inequality X F)
        hence "t \<cdot> rm_vars (set X) \<delta> \<in> trms\<^sub>s\<^sub>t\<^sub>p (Inequality X F \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>)"
          by (induct F) (auto simp add: subst_apply_pairs_def subst_apply_strand_step_def)
        thus ?case by fastforce
      qed (auto simp add: subst_apply_strand_step_def)
    qed
  qed simp

  show "t \<in> trms\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>) \<Longrightarrow> ?Q t \<delta> S"
  proof (induction S)
    case (Cons x S) show ?case
    proof (cases "t \<in> trms\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>)")
      case True
      hence "?Q t \<delta> S" using Cons by simp
      thus ?thesis by (cases x) force+
    next
      case False
      hence "t \<in> trms\<^sub>s\<^sub>t\<^sub>p (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>)" using Cons.prems by auto
      thus ?thesis
      proof (induction x)
        case (Inequality X F)
        hence "t \<in> trms\<^sub>s\<^sub>t\<^sub>p (Inequality X F) \<cdot>\<^sub>s\<^sub>e\<^sub>t rm_vars (set X) \<delta>"
          by (induct F) (force simp add: subst_apply_pairs_def)+
        thus ?case by fastforce
      qed (auto simp add: subst_apply_strand_step_def)
    qed
  qed simp
qed


subsection \<open>Lemmata: Free Variables of Strands\<close>
lemma fv_trm_snd_rcv[simp]: "fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t\<^sub>p (Send t)) = fv t" "fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t\<^sub>p (Receive t)) = fv t"
by simp_all

lemma in_strand_fv_subset: "x \<in> set S \<Longrightarrow> vars\<^sub>s\<^sub>t\<^sub>p x \<subseteq> vars\<^sub>s\<^sub>t S" by fastforce
lemma in_strand_fv_subset_snd: "Send t \<in> set S \<Longrightarrow> fv t \<subseteq> \<Union>(set (map fv\<^sub>s\<^sub>n\<^sub>d S))" by auto
lemma in_strand_fv_subset_rcv: "Receive t \<in> set S \<Longrightarrow> fv t \<subseteq> \<Union>(set (map fv\<^sub>r\<^sub>c\<^sub>v S))" by auto

lemma fv\<^sub>s\<^sub>n\<^sub>dE:
  assumes "v \<in> \<Union>(set (map fv\<^sub>s\<^sub>n\<^sub>d S))"
  obtains t where "send\<langle>t\<rangle>\<^sub>s\<^sub>t \<in> set S" "v \<in> fv t"
proof -
  have "\<exists>t. send\<langle>t\<rangle>\<^sub>s\<^sub>t \<in> set S \<and> v \<in> fv t"
    by (metis (no_types, lifting) assms UN_E empty_iff set_map strand_step.case_eq_if
              fv\<^sub>s\<^sub>n\<^sub>d_def strand_step.collapse(1))
  thus ?thesis by (metis that)
qed

lemma fv\<^sub>r\<^sub>c\<^sub>vE:
  assumes "v \<in> \<Union>(set (map fv\<^sub>r\<^sub>c\<^sub>v S))"
  obtains t where "receive\<langle>t\<rangle>\<^sub>s\<^sub>t \<in> set S" "v \<in> fv t"
proof -
  have "\<exists>t. receive\<langle>t\<rangle>\<^sub>s\<^sub>t \<in> set S \<and> v \<in> fv t"
    by (metis (no_types, lifting) assms UN_E empty_iff set_map strand_step.case_eq_if
              fv\<^sub>r\<^sub>c\<^sub>v_def strand_step.collapse(2))
  thus ?thesis by (metis that)
qed

lemma vars\<^sub>s\<^sub>t\<^sub>pI[intro]: "x \<in> fv\<^sub>s\<^sub>t\<^sub>p s \<Longrightarrow> x \<in> vars\<^sub>s\<^sub>t\<^sub>p s"
by (induct s rule: fv\<^sub>s\<^sub>t\<^sub>p.induct) auto

lemma vars\<^sub>s\<^sub>tI[intro]: "x \<in> fv\<^sub>s\<^sub>t S \<Longrightarrow> x \<in> vars\<^sub>s\<^sub>t S" using vars\<^sub>s\<^sub>t\<^sub>pI by fastforce

lemma fv\<^sub>s\<^sub>t_subset_vars\<^sub>s\<^sub>t[simp]: "fv\<^sub>s\<^sub>t S \<subseteq> vars\<^sub>s\<^sub>t S" using vars\<^sub>s\<^sub>tI by force

lemma vars\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>t: "vars\<^sub>s\<^sub>t S = fv\<^sub>s\<^sub>t S \<union> bvars\<^sub>s\<^sub>t S"
proof (induction S)
  case (Cons x S) thus ?case
  proof (induction x)
    case (Inequality X F) thus ?case by (induct F) auto
  qed auto
qed simp

lemma fv\<^sub>s\<^sub>t\<^sub>p_is_subterm_trms\<^sub>s\<^sub>t\<^sub>p: "x \<in> fv\<^sub>s\<^sub>t\<^sub>p a \<Longrightarrow> Var x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t\<^sub>p a)" 
using var_is_subterm by (cases a) force+

lemma fv\<^sub>s\<^sub>t_is_subterm_trms\<^sub>s\<^sub>t: "x \<in> fv\<^sub>s\<^sub>t A \<Longrightarrow> Var x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t A)"
proof (induction A)
  case (Cons a A) thus ?case using fv\<^sub>s\<^sub>t\<^sub>p_is_subterm_trms\<^sub>s\<^sub>t\<^sub>p by (cases "x \<in> fv\<^sub>s\<^sub>t A") auto
qed simp

lemma vars_st_snd_map: "vars\<^sub>s\<^sub>t (map Send X) = fv (Fun f X)" by auto

lemma vars_st_rcv_map: "vars\<^sub>s\<^sub>t (map Receive X) = fv (Fun f X)" by auto

lemma vars_snd_rcv_union:
  "vars\<^sub>s\<^sub>t\<^sub>p x = fv\<^sub>s\<^sub>n\<^sub>d x \<union> fv\<^sub>r\<^sub>c\<^sub>v x \<union> fv\<^sub>e\<^sub>q assign x \<union> fv\<^sub>e\<^sub>q check x \<union> fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q x \<union> set (bvars\<^sub>s\<^sub>t\<^sub>p x)"
proof (cases x)
  case (Equality ac t t') thus ?thesis by (cases ac) auto
qed auto

lemma fv_snd_rcv_union:
  "fv\<^sub>s\<^sub>t\<^sub>p x = fv\<^sub>s\<^sub>n\<^sub>d x \<union> fv\<^sub>r\<^sub>c\<^sub>v x \<union> fv\<^sub>e\<^sub>q assign x \<union> fv\<^sub>e\<^sub>q check x \<union> fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q x"
proof (cases x)
  case (Equality ac t t') thus ?thesis by (cases ac) auto
qed auto

lemma fv_snd_rcv_empty[simp]: "fv\<^sub>s\<^sub>n\<^sub>d x = {} \<or> fv\<^sub>r\<^sub>c\<^sub>v x = {}" by (cases x) simp_all

lemma vars_snd_rcv_strand[iff]:
  "vars\<^sub>s\<^sub>t (S::('a,'b) strand) =
    (\<Union>(set (map fv\<^sub>s\<^sub>n\<^sub>d S))) \<union> (\<Union>(set (map fv\<^sub>r\<^sub>c\<^sub>v S))) \<union> (\<Union>(set (map (fv\<^sub>e\<^sub>q assign) S)))
    \<union> (\<Union>(set (map (fv\<^sub>e\<^sub>q check) S))) \<union> (\<Union>(set (map fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q S))) \<union> bvars\<^sub>s\<^sub>t S"
unfolding bvars\<^sub>s\<^sub>t_def
proof (induction S)
  case (Cons x S)
  have "\<And>s V. vars\<^sub>s\<^sub>t\<^sub>p (s::('a,'b) strand_step) \<union> V = 
                fv\<^sub>s\<^sub>n\<^sub>d s \<union> fv\<^sub>r\<^sub>c\<^sub>v s \<union> fv\<^sub>e\<^sub>q assign s \<union> fv\<^sub>e\<^sub>q check s \<union> fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q s \<union> set (bvars\<^sub>s\<^sub>t\<^sub>p s) \<union> V"
    by (metis vars_snd_rcv_union)
  thus ?case using Cons.IH by (auto simp add: sup_assoc sup_left_commute)
qed simp

lemma fv_snd_rcv_strand[iff]:
  "fv\<^sub>s\<^sub>t (S::('a,'b) strand) =
    (\<Union>(set (map fv\<^sub>s\<^sub>n\<^sub>d S))) \<union> (\<Union>(set (map fv\<^sub>r\<^sub>c\<^sub>v S))) \<union> (\<Union>(set (map (fv\<^sub>e\<^sub>q assign) S)))
    \<union> (\<Union>(set (map (fv\<^sub>e\<^sub>q check) S))) \<union> (\<Union>(set (map fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q S)))"
unfolding bvars\<^sub>s\<^sub>t_def
proof (induction S)
  case (Cons x S)
  have "\<And>s V. fv\<^sub>s\<^sub>t\<^sub>p (s::('a,'b) strand_step) \<union> V = 
                fv\<^sub>s\<^sub>n\<^sub>d s \<union> fv\<^sub>r\<^sub>c\<^sub>v s \<union> fv\<^sub>e\<^sub>q assign s \<union> fv\<^sub>e\<^sub>q check s \<union> fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q s \<union> V"
    by (metis fv_snd_rcv_union)
  thus ?case using Cons.IH by (auto simp add: sup_assoc sup_left_commute)
qed simp

lemma vars_snd_rcv_strand2[iff]:
  "wfrestrictedvars\<^sub>s\<^sub>t (S::('a,'b) strand) =
    (\<Union>(set (map fv\<^sub>s\<^sub>n\<^sub>d S))) \<union> (\<Union>(set (map fv\<^sub>r\<^sub>c\<^sub>v S))) \<union> (\<Union>(set (map (fv\<^sub>e\<^sub>q assign) S)))"
by (induct S) (auto simp add: split: strand_step.split poscheckvariant.split)

lemma fv_snd_rcv_strand_subset[simp]:
  "\<Union>(set (map fv\<^sub>s\<^sub>n\<^sub>d S)) \<subseteq> fv\<^sub>s\<^sub>t S" "\<Union>(set (map fv\<^sub>r\<^sub>c\<^sub>v S)) \<subseteq> fv\<^sub>s\<^sub>t S"
  "\<Union>(set (map (fv\<^sub>e\<^sub>q ac) S)) \<subseteq> fv\<^sub>s\<^sub>t S" "\<Union>(set (map fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q S)) \<subseteq> fv\<^sub>s\<^sub>t S"
  "wfvarsoccs\<^sub>s\<^sub>t S \<subseteq> fv\<^sub>s\<^sub>t S"
proof -
  show "\<Union>(set (map fv\<^sub>s\<^sub>n\<^sub>d S)) \<subseteq> fv\<^sub>s\<^sub>t S" "\<Union>(set (map fv\<^sub>r\<^sub>c\<^sub>v S)) \<subseteq> fv\<^sub>s\<^sub>t S" "\<Union>(set (map fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q S)) \<subseteq> fv\<^sub>s\<^sub>t S"
    using fv_snd_rcv_strand[of S] by auto
  
  show "\<Union>(set (map (fv\<^sub>e\<^sub>q ac) S)) \<subseteq> fv\<^sub>s\<^sub>t S"
    by (induct S) (auto split: strand_step.split poscheckvariant.split)

  show "wfvarsoccs\<^sub>s\<^sub>t S \<subseteq> fv\<^sub>s\<^sub>t S"
    by (induct S) (auto split: strand_step.split poscheckvariant.split)
qed

lemma vars_snd_rcv_strand_subset2[simp]:
  "\<Union>(set (map fv\<^sub>s\<^sub>n\<^sub>d S)) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S" "\<Union>(set (map fv\<^sub>r\<^sub>c\<^sub>v S)) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S"
  "\<Union>(set (map (fv\<^sub>e\<^sub>q assign) S)) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S" "wfvarsoccs\<^sub>s\<^sub>t S \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S"
by (induction S) (auto split: strand_step.split poscheckvariant.split)

lemma wfrestrictedvars\<^sub>s\<^sub>t_subset_vars\<^sub>s\<^sub>t: "wfrestrictedvars\<^sub>s\<^sub>t S \<subseteq> vars\<^sub>s\<^sub>t S"
by (induction S) (auto split: strand_step.split poscheckvariant.split)

lemma subst_sends_strand_step_fv_to_img: "fv\<^sub>s\<^sub>t\<^sub>p (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) \<subseteq> fv\<^sub>s\<^sub>t\<^sub>p x \<union> range_vars \<delta>" 
using subst_sends_fv_to_img[of _ \<delta>]
proof (cases x)
  case (Inequality X F)
  let ?\<theta> = "rm_vars (set X) \<delta>"
  have "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ?\<theta>) \<subseteq> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> range_vars ?\<theta>"
  proof (induction F)
    case (Cons f F) thus ?case
      using subst_sends_fv_to_img[of _ ?\<theta>]
      by (auto simp add: subst_apply_pairs_def)
  qed (auto simp add: subst_apply_pairs_def)
  hence "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ?\<theta>) \<subseteq> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> range_vars \<delta>"
    using rm_vars_img_subset[of "set X" \<delta>] fv_set_mono
    unfolding range_vars_alt_def by blast+
  thus ?thesis using Inequality by (auto simp add: subst_apply_strand_step_def)
qed (auto simp add: subst_apply_strand_step_def)

lemma subst_sends_strand_fv_to_img: "fv\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>) \<subseteq> fv\<^sub>s\<^sub>t S \<union> range_vars \<delta>" 
proof (induction S)
  case (Cons x S)
  have *: "fv\<^sub>s\<^sub>t (x#S \<cdot>\<^sub>s\<^sub>t \<delta>) = fv\<^sub>s\<^sub>t\<^sub>p (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) \<union> fv\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>)"
          "fv\<^sub>s\<^sub>t (x#S) \<union> range_vars \<delta> = fv\<^sub>s\<^sub>t\<^sub>p x \<union> fv\<^sub>s\<^sub>t S \<union> range_vars \<delta>"
    by auto
  thus ?case using Cons.IH subst_sends_strand_step_fv_to_img[of x \<delta>] by auto
qed simp

lemma ineq_apply_subst:
  assumes "subst_domain \<delta> \<inter> set X = {}"
  shows "(Inequality X F) \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta> = Inequality X (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>)"
using rm_vars_apply'[OF assms] by (simp add: subst_apply_strand_step_def)

lemma fv_strand_step_subst:
  assumes "P = fv\<^sub>s\<^sub>t\<^sub>p \<or> P = fv\<^sub>r\<^sub>c\<^sub>v \<or> P = fv\<^sub>s\<^sub>n\<^sub>d \<or> P = fv\<^sub>e\<^sub>q ac \<or> P = fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q"
  and "set (bvars\<^sub>s\<^sub>t\<^sub>p x) \<inter> (subst_domain \<delta> \<union> range_vars \<delta>) = {}"
  shows "fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` (P x)) = P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>)"
proof (cases x)
  case (Send t)
  hence "vars\<^sub>s\<^sub>t\<^sub>p x = fv t" "fv\<^sub>s\<^sub>n\<^sub>d x = fv t" by auto
  thus ?thesis using assms Send subst_apply_fv_unfold[of _ \<delta>] by auto
next
  case (Receive t)
  hence "vars\<^sub>s\<^sub>t\<^sub>p x = fv t" "fv\<^sub>r\<^sub>c\<^sub>v x = fv t" by auto
  thus ?thesis using assms Receive subst_apply_fv_unfold[of _ \<delta>] by auto
next
  case (Equality ac' t t') show ?thesis
  proof (cases "ac = ac'")
    case True
    hence "vars\<^sub>s\<^sub>t\<^sub>p x = fv t \<union> fv t'" "fv\<^sub>e\<^sub>q ac x = fv t \<union> fv t'"
      using Equality
      by auto
    thus ?thesis
      using assms Equality subst_apply_fv_unfold[of _ \<delta>] True
      by auto
  next
    case False
    hence "vars\<^sub>s\<^sub>t\<^sub>p x = fv t \<union> fv t'" "fv\<^sub>e\<^sub>q ac x = {}"
      using Equality
      by auto
    thus ?thesis
      using assms Equality subst_apply_fv_unfold[of _ \<delta>] False
      by auto
  qed
next
  case (Inequality X F)
  hence 1: "set X \<inter> (subst_domain \<delta> \<union> range_vars \<delta>) = {}"
           "x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta> = Inequality X (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>)"
           "rm_vars (set X) \<delta> = \<delta>"
    using assms ineq_apply_subst[of \<delta> X F] rm_vars_apply'[of \<delta> "set X"]
    unfolding range_vars_alt_def by force+

  have 2: "fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q x = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X" using Inequality by auto
  hence "fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q x) = fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) - set X"
    using fv\<^sub>s\<^sub>e\<^sub>t_subst_img_eq[OF 1(1), of "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F"] by simp
  hence 3: "fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q x) = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) - set X" by (metis fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_step_subst)
  
  have 4: "fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) - set X" using 1(2) by auto

  show ?thesis
    using assms(1) Inequality subst_apply_fv_unfold[of _ \<delta>] 1(2) 2 3 4
    unfolding fv\<^sub>e\<^sub>q_def fv\<^sub>r\<^sub>c\<^sub>v_def fv\<^sub>s\<^sub>n\<^sub>d_def
    by (metis (no_types) Sup_empty image_empty fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s.simps fv\<^sub>s\<^sub>e\<^sub>t.simps
              fv\<^sub>s\<^sub>t\<^sub>p.simps(4) strand_step.simps(20))
qed

lemma fv_strand_subst:
  assumes "P = fv\<^sub>s\<^sub>t\<^sub>p \<or> P = fv\<^sub>r\<^sub>c\<^sub>v \<or> P = fv\<^sub>s\<^sub>n\<^sub>d \<or> P = fv\<^sub>e\<^sub>q ac \<or> P = fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q"
  and "bvars\<^sub>s\<^sub>t S \<inter> (subst_domain \<delta> \<union> range_vars \<delta>) = {}"
  shows "fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` (\<Union>(set (map P S)))) = \<Union>(set (map P (S \<cdot>\<^sub>s\<^sub>t \<delta>)))"
using assms(2)
proof (induction S)
  case (Cons x S)
  hence *: "bvars\<^sub>s\<^sub>t S \<inter> (subst_domain \<delta> \<union> range_vars \<delta>) = {}"
           "set (bvars\<^sub>s\<^sub>t\<^sub>p x) \<inter> (subst_domain \<delta> \<union> range_vars \<delta>) = {}"
    unfolding bvars\<^sub>s\<^sub>t_def by force+
  hence **: "fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` P x) = P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>)" using fv_strand_step_subst[OF assms(1), of x \<delta>] by auto
  have "fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` (\<Union>(set (map P (x#S))))) = fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` P x) \<union> (\<Union>(set (map P ((S \<cdot>\<^sub>s\<^sub>t \<delta>)))))"
    using Cons unfolding range_vars_alt_def bvars\<^sub>s\<^sub>t_def by force
  hence "fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` (\<Union>(set (map P (x#S))))) = P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` (\<Union>(set (map P S))))"
    using ** by simp
  thus ?case using Cons.IH[OF *(1)] unfolding bvars\<^sub>s\<^sub>t_def by simp
qed simp

lemma fv_strand_subst2:
  assumes "bvars\<^sub>s\<^sub>t S \<inter> (subst_domain \<delta> \<union> range_vars \<delta>) = {}"
  shows "fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` (wfrestrictedvars\<^sub>s\<^sub>t S)) = wfrestrictedvars\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>)"
by (metis (no_types, lifting) assms fv\<^sub>s\<^sub>e\<^sub>t.simps vars_snd_rcv_strand2 fv_strand_subst UN_Un image_Un)

lemma fv_strand_subst':
  assumes "bvars\<^sub>s\<^sub>t S \<inter> (subst_domain \<delta> \<union> range_vars \<delta>) = {}"
  shows "fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` (fv\<^sub>s\<^sub>t S)) = fv\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>)"
by (metis assms fv_strand_subst fv\<^sub>s\<^sub>t_def)

lemma fv_trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_is_fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s:
  "fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F"
by auto

lemma fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_in_fv_trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s: "x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<Longrightarrow> x \<in> fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F)"
using fv_trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_is_fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s[of F] by blast

lemma trms\<^sub>s\<^sub>t_append: "trms\<^sub>s\<^sub>t (A@B) = trms\<^sub>s\<^sub>t A \<union> trms\<^sub>s\<^sub>t B"
by auto

lemma trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_subst: "trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (a \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<theta>) = trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s a \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
by (auto simp add: subst_apply_pairs_def)

lemma trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_fv_subst_subset:
  "t \<in> trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<Longrightarrow> fv (t \<cdot> \<theta>) \<subseteq> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<theta>)"
by (force simp add: subst_apply_pairs_def)

lemma trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_fv_subst_subset':
  fixes t::"('a,'b) term" and \<theta>::"('a,'b) subst"
  assumes "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F)"
  shows "fv (t \<cdot> \<theta>) \<subseteq> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<theta>)"
proof -
  { fix x assume "x \<in> fv t"
    hence "x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F"
      using fv_subset[OF assms] fv_subterms_set[of "trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F"] fv_trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_is_fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s[of F]
      by blast
    hence "fv (\<theta> x) \<subseteq> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<theta>)" using fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_subst_fv_subset by fast
  } thus ?thesis by (meson fv_subst_obtain_var subset_iff) 
qed

lemma trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_funs_term_cases:
  assumes "t \<in> trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<theta>)" "f \<in> funs_term t"
  shows "(\<exists>u \<in> trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F. f \<in> funs_term u) \<or> (\<exists>x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F. f \<in> funs_term (\<theta> x))"
using assms(1)
proof (induction F)
  case (Cons g F)
  obtain s u where g: "g = (s,u)" by (metis surj_pair)
  show ?case
  proof (cases "t \<in> trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<theta>)")
    case False
    thus ?thesis
      using assms(2) Cons.prems g funs_term_subst[of _ \<theta>]
      by (auto simp add: subst_apply_pairs_def)
  qed (use Cons.IH in fastforce)
qed simp

lemma trm\<^sub>s\<^sub>t\<^sub>p_subst: 
  assumes "subst_domain \<theta> \<inter> set (bvars\<^sub>s\<^sub>t\<^sub>p a) = {}"
  shows "trms\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>t\<^sub>p \<theta>) = trms\<^sub>s\<^sub>t\<^sub>p a \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
proof -
  have "rm_vars (set (bvars\<^sub>s\<^sub>t\<^sub>p a)) \<theta> = \<theta>" using assms by force
  thus ?thesis
    using assms
    by (auto simp add: subst_apply_pairs_def subst_apply_strand_step_def
             split: strand_step.splits)
qed

lemma trms\<^sub>s\<^sub>t_subst:
  assumes "subst_domain \<theta> \<inter> bvars\<^sub>s\<^sub>t A = {}"
  shows "trms\<^sub>s\<^sub>t (A \<cdot>\<^sub>s\<^sub>t \<theta>) = trms\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
using assms
proof (induction A)
  case (Cons a A)
  have 1: "subst_domain \<theta> \<inter> bvars\<^sub>s\<^sub>t A = {}" "subst_domain \<theta> \<inter> set (bvars\<^sub>s\<^sub>t\<^sub>p a) = {}"
    using Cons.prems by auto
  hence IH: "trms\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta> = trms\<^sub>s\<^sub>t (A \<cdot>\<^sub>s\<^sub>t \<theta>)" using Cons.IH by simp
  
  have "trms\<^sub>s\<^sub>t (a#A) = trms\<^sub>s\<^sub>t\<^sub>p a \<union> trms\<^sub>s\<^sub>t A" by auto
  hence 2: "trms\<^sub>s\<^sub>t (a#A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta> = (trms\<^sub>s\<^sub>t\<^sub>p a \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) \<union> (trms\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)" by (metis image_Un)

  have "trms\<^sub>s\<^sub>t (a#A \<cdot>\<^sub>s\<^sub>t \<theta>) = (trms\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>t\<^sub>p \<theta>)) \<union> trms\<^sub>s\<^sub>t (A \<cdot>\<^sub>s\<^sub>t \<theta>)"
    by (auto simp add: subst_apply_strand_def)
  hence 3: "trms\<^sub>s\<^sub>t (a#A \<cdot>\<^sub>s\<^sub>t \<theta>) = (trms\<^sub>s\<^sub>t\<^sub>p a \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) \<union> trms\<^sub>s\<^sub>t (A \<cdot>\<^sub>s\<^sub>t \<theta>)"
    using trm\<^sub>s\<^sub>t\<^sub>p_subst[OF 1(2)] by auto
  
  show ?case using IH 2 3 by metis
qed (simp add: subst_apply_strand_def)

lemma strand_map_set_subst:
  assumes \<delta>: "bvars\<^sub>s\<^sub>t S \<inter> (subst_domain \<delta> \<union> range_vars \<delta>) = {}"
  shows "\<Union>(set (map trms\<^sub>s\<^sub>t\<^sub>p (S \<cdot>\<^sub>s\<^sub>t \<delta>))) = (\<Union>(set (map trms\<^sub>s\<^sub>t\<^sub>p S))) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>"
using assms
proof (induction S)
  case (Cons x S)
  hence "bvars\<^sub>s\<^sub>t [x] \<inter> subst_domain \<delta> = {}" "bvars\<^sub>s\<^sub>t S \<inter> (subst_domain \<delta> \<union> range_vars \<delta>) = {}"
    unfolding bvars\<^sub>s\<^sub>t_def by force+
  hence *: "subst_domain \<delta> \<inter> set (bvars\<^sub>s\<^sub>t\<^sub>p x) = {}"
           "\<Union>(set (map trms\<^sub>s\<^sub>t\<^sub>p (S \<cdot>\<^sub>s\<^sub>t \<delta>))) = \<Union>(set (map trms\<^sub>s\<^sub>t\<^sub>p S)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>"
    using Cons.IH(1) bvars\<^sub>s\<^sub>t_singleton[of x] by auto
  hence "trms\<^sub>s\<^sub>t\<^sub>p (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = (trms\<^sub>s\<^sub>t\<^sub>p x) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>"
  proof (cases x)
    case (Inequality X F)
    thus ?thesis
      using rm_vars_apply'[of \<delta> "set X"] * 
      by (metis (no_types, lifting) image_cong trm\<^sub>s\<^sub>t\<^sub>p_subst)
  qed simp_all
  thus ?case using * subst_all_insert by auto
qed simp

lemma subst_apply_fv_subset_strand_trm:
  assumes P: "P = fv\<^sub>s\<^sub>t\<^sub>p \<or> P = fv\<^sub>r\<^sub>c\<^sub>v \<or> P = fv\<^sub>s\<^sub>n\<^sub>d \<or> P = fv\<^sub>e\<^sub>q ac \<or> P = fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q"
  and fv_sub: "fv t \<subseteq> \<Union>(set (map P S)) \<union> V"
  and \<delta>: "bvars\<^sub>s\<^sub>t S \<inter> (subst_domain \<delta> \<union> range_vars \<delta>) = {}"
  shows "fv (t \<cdot> \<delta>) \<subseteq> \<Union>(set (map P (S \<cdot>\<^sub>s\<^sub>t \<delta>))) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
using fv_strand_subst[OF P \<delta>] subst_apply_fv_subset[OF fv_sub, of \<delta>] by force

lemma subst_apply_fv_subset_strand_trm2:
  assumes fv_sub: "fv t \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> V"
  and \<delta>: "bvars\<^sub>s\<^sub>t S \<inter> (subst_domain \<delta> \<union> range_vars \<delta>) = {}"
  shows "fv (t \<cdot> \<delta>) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
using fv_strand_subst2[OF \<delta>] subst_apply_fv_subset[OF fv_sub, of \<delta>] by force

lemma subst_apply_fv_subset_strand:
  assumes P: "P = fv\<^sub>s\<^sub>t\<^sub>p \<or> P = fv\<^sub>r\<^sub>c\<^sub>v \<or> P = fv\<^sub>s\<^sub>n\<^sub>d \<or> P = fv\<^sub>e\<^sub>q ac \<or> P = fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q"
  and P_subset: "P x \<subseteq> \<Union>(set (map P S)) \<union> V"
  and \<delta>: "bvars\<^sub>s\<^sub>t S \<inter> (subst_domain \<delta> \<union> range_vars \<delta>) = {}"
         "set (bvars\<^sub>s\<^sub>t\<^sub>p x) \<inter> (subst_domain \<delta> \<union> range_vars \<delta>) = {}"
  shows "P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) \<subseteq> \<Union>(set (map P (S \<cdot>\<^sub>s\<^sub>t \<delta>))) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
proof (cases x)
  case (Send t)
  hence *: "fv\<^sub>s\<^sub>t\<^sub>p x = fv t" "fv\<^sub>s\<^sub>t\<^sub>p (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>)"
           "fv\<^sub>r\<^sub>c\<^sub>v x = {}" "fv\<^sub>r\<^sub>c\<^sub>v (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
           "fv\<^sub>s\<^sub>n\<^sub>d x = fv t" "fv\<^sub>s\<^sub>n\<^sub>d (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>)"
           "fv\<^sub>e\<^sub>q ac x = {}" "fv\<^sub>e\<^sub>q ac (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
           "fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q x = {}" "fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
    by auto
  hence **: "(P x = fv t \<and> P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>)) \<or> (P x = {} \<and> P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {})" by (metis P)
  moreover
  { assume "P x = {}" "P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}" hence ?thesis by simp }
  moreover
  { assume "P x = fv t" "P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>)"
    hence "fv t \<subseteq> \<Union>(set (map P S)) \<union> V" using P_subset by auto
    hence "fv (t \<cdot> \<delta>) \<subseteq> \<Union>(set (map P (S \<cdot>\<^sub>s\<^sub>t \<delta>))) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
      unfolding vars\<^sub>s\<^sub>t_def using P subst_apply_fv_subset_strand_trm assms by blast
    hence ?thesis using \<open>P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>)\<close> by force
  }
  ultimately show ?thesis by metis
next
  case (Receive t)
  hence *: "fv\<^sub>s\<^sub>t\<^sub>p x = fv t" "fv\<^sub>s\<^sub>t\<^sub>p (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>)"
           "fv\<^sub>r\<^sub>c\<^sub>v x = fv t" "fv\<^sub>r\<^sub>c\<^sub>v (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>)"
           "fv\<^sub>s\<^sub>n\<^sub>d x = {}" "fv\<^sub>s\<^sub>n\<^sub>d (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
           "fv\<^sub>e\<^sub>q ac x = {}" "fv\<^sub>e\<^sub>q ac (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
           "fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q x = {}" "fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
    by auto
  hence **: "(P x = fv t \<and> P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>)) \<or> (P x = {} \<and> P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {})" by (metis P)
  moreover
  { assume "P x = {}" "P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}" hence ?thesis by simp }
  moreover
  { assume "P x = fv t" "P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>)"
    hence "fv t \<subseteq> \<Union>(set (map P S)) \<union> V" using P_subset by auto
    hence "fv (t \<cdot> \<delta>) \<subseteq> \<Union>(set (map P (S \<cdot>\<^sub>s\<^sub>t \<delta>))) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
      unfolding vars\<^sub>s\<^sub>t_def using P subst_apply_fv_subset_strand_trm assms by blast
    hence ?thesis using \<open>P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>)\<close> by blast
  }
  ultimately show ?thesis by metis
next
  case (Equality ac' t t') show ?thesis
  proof (cases "ac' = ac")
    case True
    hence *: "fv\<^sub>s\<^sub>t\<^sub>p x = fv t \<union> fv t'" "fv\<^sub>s\<^sub>t\<^sub>p (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>) \<union> fv (t' \<cdot> \<delta>)"
             "fv\<^sub>r\<^sub>c\<^sub>v x = {}" "fv\<^sub>r\<^sub>c\<^sub>v (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
             "fv\<^sub>s\<^sub>n\<^sub>d x = {}" "fv\<^sub>s\<^sub>n\<^sub>d (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
             "fv\<^sub>e\<^sub>q ac x = fv t \<union> fv t'" "fv\<^sub>e\<^sub>q ac (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>) \<union> fv (t' \<cdot> \<delta>)"
             "fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q x = {}" "fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
      using Equality by auto
    hence **: "(P x = fv t \<union> fv t' \<and> P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>) \<union> fv (t' \<cdot> \<delta>))
              \<or> (P x = {} \<and> P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {})"
      by (metis P)
    moreover
    { assume "P x = {}" "P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}" hence ?thesis by simp }
    moreover
    { assume "P x = fv t \<union> fv t'" "P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>) \<union> fv (t' \<cdot> \<delta>)"
      hence "fv t \<subseteq> \<Union>(set (map P S)) \<union> V" "fv t' \<subseteq> \<Union>(set (map P S)) \<union> V" using P_subset by auto
      hence "fv (t \<cdot> \<delta>) \<subseteq> \<Union>(set (map P (S \<cdot>\<^sub>s\<^sub>t \<delta>))) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
            "fv (t' \<cdot> \<delta>) \<subseteq> \<Union>(set (map P (S \<cdot>\<^sub>s\<^sub>t \<delta>))) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
        unfolding vars\<^sub>s\<^sub>t_def using P subst_apply_fv_subset_strand_trm assms by metis+
      hence ?thesis using \<open>P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>) \<union> fv (t' \<cdot> \<delta>)\<close> by blast
    }
    ultimately show ?thesis by metis
  next
    case False
    hence *: "fv\<^sub>s\<^sub>t\<^sub>p x = fv t \<union> fv t'" "fv\<^sub>s\<^sub>t\<^sub>p (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>) \<union> fv (t' \<cdot> \<delta>)"
             "fv\<^sub>r\<^sub>c\<^sub>v x = {}" "fv\<^sub>r\<^sub>c\<^sub>v (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
             "fv\<^sub>s\<^sub>n\<^sub>d x = {}" "fv\<^sub>s\<^sub>n\<^sub>d (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
             "fv\<^sub>e\<^sub>q ac x = {}" "fv\<^sub>e\<^sub>q ac (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
             "fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q x = {}" "fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
      using Equality by auto
    hence **: "(P x = fv t \<union> fv t' \<and> P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>) \<union> fv (t' \<cdot> \<delta>))
              \<or> (P x = {} \<and> P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {})"
      by (metis P)
    moreover
    { assume "P x = {}" "P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}" hence ?thesis by simp }
    moreover
    { assume "P x = fv t \<union> fv t'" "P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>) \<union> fv (t' \<cdot> \<delta>)"
      hence "fv t \<subseteq> \<Union>(set (map P S)) \<union> V" "fv t' \<subseteq> \<Union>(set (map P S)) \<union> V" using P_subset by auto
      hence "fv (t \<cdot> \<delta>) \<subseteq> \<Union>(set (map P (S \<cdot>\<^sub>s\<^sub>t \<delta>))) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
            "fv (t' \<cdot> \<delta>) \<subseteq> \<Union>(set (map P (S \<cdot>\<^sub>s\<^sub>t \<delta>))) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
        unfolding vars\<^sub>s\<^sub>t_def using P subst_apply_fv_subset_strand_trm assms by metis+
      hence ?thesis using \<open>P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>) \<union> fv (t' \<cdot> \<delta>)\<close> by blast
    }
    ultimately show ?thesis by metis
  qed
next
  case (Inequality X F)
  hence *: "fv\<^sub>s\<^sub>t\<^sub>p x = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X" "fv\<^sub>s\<^sub>t\<^sub>p (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) - set X"
           "fv\<^sub>r\<^sub>c\<^sub>v x = {}" "fv\<^sub>r\<^sub>c\<^sub>v (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
           "fv\<^sub>s\<^sub>n\<^sub>d x = {}" "fv\<^sub>s\<^sub>n\<^sub>d (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
           "fv\<^sub>e\<^sub>q ac x = {}" "fv\<^sub>e\<^sub>q ac (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
           "fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q x = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X"
           "fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) - set X"
    using \<delta>(2) ineq_apply_subst[of \<delta> X F] by force+
  hence **: "(P x = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X \<and> P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) - set X)
            \<or> (P x = {} \<and> P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {})"
    by (metis P)
  moreover
  { assume "P x = {}" "P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}" hence ?thesis by simp }
  moreover
  { assume "P x = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X" "P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) - set X"
    hence "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X \<subseteq> \<Union>(set (map P S)) \<union> V"
      using P_subset by auto
    hence "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) \<subseteq> \<Union>(set (map P (S \<cdot>\<^sub>s\<^sub>t \<delta>))) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` (V \<union> set X))"
    proof (induction F)
      case (Cons f G)
      hence IH: "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) \<subseteq> \<Union>(set (map P (S \<cdot>\<^sub>s\<^sub>t \<delta>))) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` (V \<union> set X))"
        by (metis (no_types, lifting) Diff_subset_conv UN_insert le_sup_iff
                  list.simps(15) fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s.simps)
      obtain t t' where f: "f = (t,t')" by (metis surj_pair)
      hence "fv t \<subseteq> \<Union>(set (map P S)) \<union> (V \<union> set X)" "fv t' \<subseteq> \<Union>(set (map P S)) \<union> (V \<union> set X)"
        using Cons.prems by auto
      hence "fv (t \<cdot> \<delta>) \<subseteq> \<Union>(set (map P (S \<cdot>\<^sub>s\<^sub>t \<delta>))) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` (V \<union> set X))"
            "fv (t' \<cdot> \<delta>) \<subseteq> \<Union>(set (map P (S \<cdot>\<^sub>s\<^sub>t \<delta>))) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` (V \<union> set X))"
        using subst_apply_fv_subset_strand_trm[OF P _ assms(3)]
        by blast+
      thus ?case using f IH by (auto simp add: subst_apply_pairs_def)
    qed (simp add: subst_apply_pairs_def)
    moreover have "fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` set X) = set X" using assms(4) Inequality by force
    ultimately have "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) - set X \<subseteq> \<Union>(set (map P (S \<cdot>\<^sub>s\<^sub>t \<delta>))) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
      by auto
    hence ?thesis using \<open>P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) - set X\<close> by blast
  }
  ultimately show ?thesis by metis
qed

lemma subst_apply_fv_subset_strand2:
  assumes P: "P = fv\<^sub>s\<^sub>t\<^sub>p \<or> P = fv\<^sub>r\<^sub>c\<^sub>v \<or> P = fv\<^sub>s\<^sub>n\<^sub>d \<or> P = fv\<^sub>e\<^sub>q ac \<or> P = fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q \<or> P = fv_r\<^sub>e\<^sub>q ac"
  and P_subset: "P x \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> V"
  and \<delta>: "bvars\<^sub>s\<^sub>t S \<inter> (subst_domain \<delta> \<union> range_vars \<delta>) = {}"
         "set (bvars\<^sub>s\<^sub>t\<^sub>p x) \<inter> (subst_domain \<delta> \<union> range_vars \<delta>) = {}"
  shows "P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
proof (cases x)
  case (Send t)
  hence *: "fv\<^sub>s\<^sub>t\<^sub>p x = fv t" "fv\<^sub>s\<^sub>t\<^sub>p (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>)"
           "fv\<^sub>r\<^sub>c\<^sub>v x = {}" "fv\<^sub>r\<^sub>c\<^sub>v (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
           "fv\<^sub>s\<^sub>n\<^sub>d x = fv t" "fv\<^sub>s\<^sub>n\<^sub>d (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>)"
           "fv\<^sub>e\<^sub>q ac x = {}" "fv\<^sub>e\<^sub>q ac (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
           "fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q x = {}" "fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
           "fv_r\<^sub>e\<^sub>q ac x = {}" "fv_r\<^sub>e\<^sub>q ac (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
    by auto
  hence **: "(P x = fv t \<and> P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>)) \<or> (P x = {} \<and> P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {})" by (metis P)
  moreover
  { assume "P x = {}" "P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}" hence ?thesis by simp }
  moreover
  { assume "P x = fv t" "P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>)"
    hence "fv t \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> V" using P_subset by auto
    hence "fv (t \<cdot> \<delta>) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
      using P subst_apply_fv_subset_strand_trm2 assms by blast
    hence ?thesis using \<open>P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>)\<close> by blast
  }
  ultimately show ?thesis by metis
next
  case (Receive t)
  hence *: "fv\<^sub>s\<^sub>t\<^sub>p x = fv t" "fv\<^sub>s\<^sub>t\<^sub>p (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>)"
           "fv\<^sub>r\<^sub>c\<^sub>v x = fv t" "fv\<^sub>r\<^sub>c\<^sub>v (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>)"
           "fv\<^sub>s\<^sub>n\<^sub>d x = {}" "fv\<^sub>s\<^sub>n\<^sub>d (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
           "fv\<^sub>e\<^sub>q ac x = {}" "fv\<^sub>e\<^sub>q ac (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
           "fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q x = {}" "fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
           "fv_r\<^sub>e\<^sub>q ac x = {}" "fv_r\<^sub>e\<^sub>q ac (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
    by auto
  hence **: "(P x = fv t \<and> P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>)) \<or> (P x = {} \<and> P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {})" by (metis P)
  moreover
  { assume "P x = {}" "P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}" hence ?thesis by simp }
  moreover
  { assume "P x = fv t" "P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>)"
    hence "fv t \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> V" using P_subset by auto
    hence "fv (t \<cdot> \<delta>) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
      using P subst_apply_fv_subset_strand_trm2 assms by blast
    hence ?thesis using \<open>P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>)\<close> by blast
  }
  ultimately show ?thesis by metis
next
  case (Equality ac' t t') show ?thesis
  proof (cases "ac' = ac")
    case True
    hence *: "fv\<^sub>s\<^sub>t\<^sub>p x = fv t \<union> fv t'" "fv\<^sub>s\<^sub>t\<^sub>p (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>) \<union> fv (t' \<cdot> \<delta>)"
             "fv\<^sub>r\<^sub>c\<^sub>v x = {}" "fv\<^sub>r\<^sub>c\<^sub>v (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
             "fv\<^sub>s\<^sub>n\<^sub>d x = {}" "fv\<^sub>s\<^sub>n\<^sub>d (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
             "fv\<^sub>e\<^sub>q ac x = fv t \<union> fv t'" "fv\<^sub>e\<^sub>q ac (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>) \<union> fv (t' \<cdot> \<delta>)"
             "fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q x = {}" "fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
             "fv_r\<^sub>e\<^sub>q ac x = fv t'" "fv_r\<^sub>e\<^sub>q ac (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t' \<cdot> \<delta>)"
      using Equality by auto
    hence **: "(P x = fv t \<union> fv t' \<and> P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>) \<union> fv (t' \<cdot> \<delta>))
              \<or> (P x = {} \<and> P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {})
              \<or> (P x = fv t' \<and> P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t' \<cdot> \<delta>))"
      by (metis P)
    moreover
    { assume "P x = {}" "P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}" hence ?thesis by simp }
    moreover
    { assume "P x = fv t \<union> fv t'" "P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>) \<union> fv (t' \<cdot> \<delta>)"
      hence "fv t \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> V" "fv t' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> V" using P_subset by auto
      hence "fv (t \<cdot> \<delta>) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
            "fv (t' \<cdot> \<delta>) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
        using P subst_apply_fv_subset_strand_trm2 assms by blast+
      hence ?thesis using \<open>P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>) \<union> fv (t' \<cdot> \<delta>)\<close> by blast
    }
    moreover
    { assume "P x = fv t'" "P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t' \<cdot> \<delta>)"
      hence "fv t' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> V" using P_subset by auto
      hence "fv (t' \<cdot> \<delta>) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
        using P subst_apply_fv_subset_strand_trm2 assms by blast+
      hence ?thesis using \<open>P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t' \<cdot> \<delta>)\<close> by blast
    }
    ultimately show ?thesis by metis
  next
    case False
    hence *: "fv\<^sub>s\<^sub>t\<^sub>p x = fv t \<union> fv t'" "fv\<^sub>s\<^sub>t\<^sub>p (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>) \<union> fv (t' \<cdot> \<delta>)"
             "fv\<^sub>r\<^sub>c\<^sub>v x = {}" "fv\<^sub>r\<^sub>c\<^sub>v (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
             "fv\<^sub>s\<^sub>n\<^sub>d x = {}" "fv\<^sub>s\<^sub>n\<^sub>d (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
             "fv\<^sub>e\<^sub>q ac x = {}" "fv\<^sub>e\<^sub>q ac (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
             "fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q x = {}" "fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
             "fv_r\<^sub>e\<^sub>q ac x = {}" "fv_r\<^sub>e\<^sub>q ac (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
      using Equality by auto
    hence **: "(P x = fv t \<union> fv t' \<and> P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>) \<union> fv (t' \<cdot> \<delta>))
              \<or> (P x = {} \<and> P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {})
              \<or> (P x = fv t' \<and> P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t' \<cdot> \<delta>))"
      by (metis P)
    moreover
    { assume "P x = {}" "P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}" hence ?thesis by simp }
    moreover
    { assume "P x = fv t \<union> fv t'" "P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>) \<union> fv (t' \<cdot> \<delta>)"
      hence "fv t \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> V" "fv t' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> V"
        using P_subset by auto
      hence "fv (t \<cdot> \<delta>) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
            "fv (t' \<cdot> \<delta>) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
        using P subst_apply_fv_subset_strand_trm2 assms by blast+
      hence ?thesis using \<open>P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t \<cdot> \<delta>) \<union> fv (t' \<cdot> \<delta>)\<close> by blast
    }
    moreover
    { assume "P x = fv t'" "P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t' \<cdot> \<delta>)"
      hence "fv t' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> V" using P_subset by auto
      hence "fv (t' \<cdot> \<delta>) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
        using P subst_apply_fv_subset_strand_trm2 assms by blast+
      hence ?thesis using \<open>P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv (t' \<cdot> \<delta>)\<close> by blast
    }
    ultimately show ?thesis by metis
  qed
next
  case (Inequality X F)
  hence *: "fv\<^sub>s\<^sub>t\<^sub>p x = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X" "fv\<^sub>s\<^sub>t\<^sub>p (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) - set X"
           "fv\<^sub>r\<^sub>c\<^sub>v x = {}" "fv\<^sub>r\<^sub>c\<^sub>v (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
           "fv\<^sub>s\<^sub>n\<^sub>d x = {}" "fv\<^sub>s\<^sub>n\<^sub>d (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
           "fv\<^sub>e\<^sub>q ac x = {}" "fv\<^sub>e\<^sub>q ac (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
           "fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q x = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X" "fv\<^sub>i\<^sub>n\<^sub>e\<^sub>q (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) - set X"
           "fv_r\<^sub>e\<^sub>q ac x = {}" "fv_r\<^sub>e\<^sub>q ac (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
    using \<delta>(2) ineq_apply_subst[of \<delta> X F] by force+
  hence **: "(P x = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X \<and> P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) - set X)
            \<or> (P x = {} \<and> P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {})"
    by (metis P)
  moreover
  { assume "P x = {}" "P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}" hence ?thesis by simp }
  moreover
  { assume "P x = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X" "P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) - set X"
    hence "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> V" using P_subset by auto
    hence "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` (V \<union> set X))"
    proof (induction F)
      case (Cons f G)
      hence IH: "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) \<subseteq>wfrestrictedvars\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` (V \<union> set X))"
        by (metis (no_types, lifting) Diff_subset_conv UN_insert le_sup_iff
                  list.simps(15) fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s.simps)
      obtain t t' where f: "f = (t,t')" by (metis surj_pair)
      hence "fv t \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> (V \<union> set X)" "fv t' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> (V \<union> set X)"
        using Cons.prems by auto
      hence "fv (t \<cdot> \<delta>) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` (V \<union> set X))"
            "fv (t' \<cdot> \<delta>) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` (V \<union> set X))"
        using subst_apply_fv_subset_strand_trm2[OF _ assms(3)] P
        by blast+
      thus ?case using f IH by (auto simp add: subst_apply_pairs_def)
    qed (simp add: subst_apply_pairs_def)
    moreover have "fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` set X) = set X" using assms(4) Inequality by force
    ultimately have "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) - set X \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
      by fastforce
    hence ?thesis using \<open>P (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) - set X\<close> by blast
  }
  ultimately show ?thesis by metis
qed

lemma strand_subst_fv_bounded_if_img_bounded:
  assumes "range_vars \<delta> \<subseteq> fv\<^sub>s\<^sub>t S"
  shows "fv\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>) \<subseteq> fv\<^sub>s\<^sub>t S"
using subst_sends_strand_fv_to_img[of S \<delta>] assms by blast

lemma strand_fv_subst_subset_if_subst_elim:
  assumes "subst_elim \<delta> v" and "v \<in> fv\<^sub>s\<^sub>t S \<or> bvars\<^sub>s\<^sub>t S \<inter> (subst_domain \<delta> \<union> range_vars \<delta>) = {}"
  shows "v \<notin> fv\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>)"
proof (cases "v \<in> fv\<^sub>s\<^sub>t S")
  case True thus ?thesis
  proof (induction S)
    case (Cons x S)
    have *: "v \<notin> fv\<^sub>s\<^sub>t\<^sub>p (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>)"
    using assms(1)
    proof (cases x)
      case (Inequality X F)
      hence "subst_elim (rm_vars (set X) \<delta>) v \<or> v \<in> set X" using assms(1) by blast
      moreover have "fv\<^sub>s\<^sub>t\<^sub>p (Inequality X F \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<delta>) - set X"
        using Inequality by auto
      ultimately have "v \<notin> fv\<^sub>s\<^sub>t\<^sub>p (Inequality X F \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>)"
        by (induct F) (auto simp add: subst_elim_def subst_apply_pairs_def)
      thus ?thesis using Inequality by simp
    qed (simp_all add: subst_elim_def)
    moreover have "v \<notin> fv\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>)" using Cons.IH
    proof (cases "v \<in> fv\<^sub>s\<^sub>t S")
      case False
      moreover have "v \<notin> range_vars \<delta>"
        by (simp add: subst_elimD''[OF assms(1)] range_vars_alt_def) 
      ultimately show ?thesis by (meson UnE subsetCE subst_sends_strand_fv_to_img)
    qed simp
    ultimately show ?case by auto
  qed simp
next
  case False
  thus ?thesis
    using assms fv_strand_subst'
    unfolding subst_elim_def
    by (metis (mono_tags, hide_lams) fv\<^sub>s\<^sub>e\<^sub>t.simps imageE mem_simps(8) subst_apply_term.simps(1))
qed

lemma strand_fv_subst_subset_if_subst_elim':
  assumes "subst_elim \<delta> v" "v \<in> fv\<^sub>s\<^sub>t S" "range_vars \<delta> \<subseteq> fv\<^sub>s\<^sub>t S"
  shows "fv\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>) \<subset> fv\<^sub>s\<^sub>t S"
using strand_fv_subst_subset_if_subst_elim[OF assms(1)] assms(2)
      strand_subst_fv_bounded_if_img_bounded[OF assms(3)]
by blast

lemma fv_ik_is_fv_rcv: "fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>s\<^sub>t S) = \<Union>(set (map fv\<^sub>r\<^sub>c\<^sub>v S))"
by (induct S rule: ik\<^sub>s\<^sub>t.induct) auto

lemma fv_ik_subset_fv_st[simp]: "fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>s\<^sub>t S) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S"
by (induct S rule: ik\<^sub>s\<^sub>t.induct) auto

lemma fv_assignment_rhs_subset_fv_st[simp]: "fv\<^sub>s\<^sub>e\<^sub>t (assignment_rhs\<^sub>s\<^sub>t S) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S"
by (induct S rule: assignment_rhs\<^sub>s\<^sub>t.induct) force+

lemma fv_ik_subset_fv_st'[simp]: "fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>s\<^sub>t S) \<subseteq> fv\<^sub>s\<^sub>t S"
by (induct S rule: ik\<^sub>s\<^sub>t.induct) auto

lemma ik\<^sub>s\<^sub>t_var_is_fv: "Var x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>s\<^sub>t A) \<Longrightarrow> x \<in> fv\<^sub>s\<^sub>t A"
by (meson fv_ik_subset_fv_st'[of A] fv_subset_subterms subsetCE term.set_intros(3))

lemma fv_assignment_rhs_subset_fv_st'[simp]: "fv\<^sub>s\<^sub>e\<^sub>t (assignment_rhs\<^sub>s\<^sub>t S) \<subseteq> fv\<^sub>s\<^sub>t S"
by (induct S rule: assignment_rhs\<^sub>s\<^sub>t.induct) auto

lemma ik\<^sub>s\<^sub>t_assignment_rhs\<^sub>s\<^sub>t_wfrestrictedvars_subset:
  "fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>s\<^sub>t A \<union> assignment_rhs\<^sub>s\<^sub>t A) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t A"
using fv_ik_subset_fv_st[of A] fv_assignment_rhs_subset_fv_st[of A]
by simp+

lemma strand_step_id_subst[iff]: "x \<cdot>\<^sub>s\<^sub>t\<^sub>p Var = x" by (cases x) auto

lemma strand_id_subst[iff]: "S \<cdot>\<^sub>s\<^sub>t Var = S" using strand_step_id_subst by (induct S) auto

lemma strand_subst_vars_union_bound[simp]: "vars\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>) \<subseteq> vars\<^sub>s\<^sub>t S \<union> range_vars \<delta>"
proof (induction S)
  case (Cons x S)
  moreover have "vars\<^sub>s\<^sub>t\<^sub>p (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) \<subseteq> vars\<^sub>s\<^sub>t\<^sub>p x \<union> range_vars \<delta>" using subst_sends_fv_to_img[of _ \<delta>]
  proof (cases x)
    case (Inequality X F)
    define \<delta>' where "\<delta>' \<equiv> rm_vars (set X) \<delta>"
    have 0: "range_vars \<delta>' \<subseteq> range_vars \<delta>"
      using rm_vars_img[of "set X" \<delta>]
      by (auto simp add: \<delta>'_def subst_domain_def range_vars_alt_def)

    have "vars\<^sub>s\<^sub>t\<^sub>p (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>') \<union> set X" "vars\<^sub>s\<^sub>t\<^sub>p x = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> set X"
      using Inequality by (auto simp add: \<delta>'_def)
    moreover have "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>') \<subseteq> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> range_vars \<delta>"
    proof (induction F)
      case (Cons f G)
      obtain t t' where f: "f = (t,t')" by moura
      hence "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (f#G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>') = fv (t \<cdot> \<delta>') \<union> fv (t' \<cdot> \<delta>') \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>')"
            "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (f#G) = fv t \<union> fv t' \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G"
        by (auto simp add: subst_apply_pairs_def)
      thus ?case
        using 0 Cons.IH subst_sends_fv_to_img[of t \<delta>'] subst_sends_fv_to_img[of t' \<delta>']
        unfolding f by auto
    qed (simp add: subst_apply_pairs_def)
    ultimately show ?thesis by auto
  qed auto
  ultimately show ?case by auto
qed simp

lemma strand_vars_split:
  "vars\<^sub>s\<^sub>t (S@S') = vars\<^sub>s\<^sub>t S \<union> vars\<^sub>s\<^sub>t S'"
  "wfrestrictedvars\<^sub>s\<^sub>t (S@S') = wfrestrictedvars\<^sub>s\<^sub>t S \<union> wfrestrictedvars\<^sub>s\<^sub>t S'"
  "fv\<^sub>s\<^sub>t (S@S') = fv\<^sub>s\<^sub>t S \<union> fv\<^sub>s\<^sub>t S'"
by auto

lemma bvars_subst_ident: "bvars\<^sub>s\<^sub>t S = bvars\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>)"
unfolding bvars\<^sub>s\<^sub>t_def
by (induct S) (simp_all add: subst_apply_strand_step_def split: strand_step.splits)

lemma strand_subst_subst_idem:
  assumes "subst_idem \<delta>" "subst_domain \<delta> \<union> range_vars \<delta> \<subseteq> fv\<^sub>s\<^sub>t S" "subst_domain \<theta> \<inter> fv\<^sub>s\<^sub>t S = {}"
          "range_vars \<delta> \<inter> bvars\<^sub>s\<^sub>t S = {}" "range_vars \<theta> \<inter> bvars\<^sub>s\<^sub>t S = {}"
  shows "(S \<cdot>\<^sub>s\<^sub>t \<delta>) \<cdot>\<^sub>s\<^sub>t \<theta> = (S \<cdot>\<^sub>s\<^sub>t \<delta>)"
  and   "(S \<cdot>\<^sub>s\<^sub>t \<delta>) \<cdot>\<^sub>s\<^sub>t (\<theta> \<circ>\<^sub>s \<delta>) = (S \<cdot>\<^sub>s\<^sub>t \<delta>)"
proof -
  from assms(2,3) have "fv\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>) \<inter> subst_domain \<theta> = {}"
    using subst_sends_strand_fv_to_img[of S \<delta>] by blast
  thus "(S \<cdot>\<^sub>s\<^sub>t \<delta>) \<cdot>\<^sub>s\<^sub>t \<theta> = (S \<cdot>\<^sub>s\<^sub>t \<delta>)" by blast
  thus "(S \<cdot>\<^sub>s\<^sub>t \<delta>) \<cdot>\<^sub>s\<^sub>t (\<theta> \<circ>\<^sub>s \<delta>) = (S \<cdot>\<^sub>s\<^sub>t \<delta>)"
    by (metis assms(1,4,5) bvars_subst_ident strand_subst_comp subst_idem_def)
qed

lemma strand_subst_img_bound:
  assumes "subst_domain \<delta> \<union> range_vars \<delta> \<subseteq> fv\<^sub>s\<^sub>t S"
    and "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> bvars\<^sub>s\<^sub>t S = {}"
  shows "range_vars \<delta> \<subseteq> fv\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>)"
proof -
  have "subst_domain \<delta> \<subseteq> \<Union>(set (map fv\<^sub>s\<^sub>t\<^sub>p S))" by (metis (no_types) fv\<^sub>s\<^sub>t_def Un_subset_iff assms(1))
  thus ?thesis
    unfolding range_vars_alt_def fv\<^sub>s\<^sub>t_def
    by (metis subst_range.simps fv_set_mono fv_strand_subst Int_commute assms(2) image_Un
              le_iff_sup)
qed

lemma strand_subst_img_bound':
  assumes "subst_domain \<delta> \<union> range_vars \<delta> \<subseteq> vars\<^sub>s\<^sub>t S"
    and "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> bvars\<^sub>s\<^sub>t S = {}"
  shows "range_vars \<delta> \<subseteq> vars\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>)"
proof -
  have "(subst_domain \<delta> \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` subst_domain \<delta>)) \<inter> vars\<^sub>s\<^sub>t S =
        subst_domain \<delta> \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` subst_domain \<delta>)"
    using assms(1) by (metis inf.absorb_iff1 range_vars_alt_def subst_range.simps)
  hence "range_vars \<delta> \<subseteq> fv\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>)"
    using vars_snd_rcv_strand fv_snd_rcv_strand assms(2) strand_subst_img_bound
    unfolding range_vars_alt_def
    by (metis (no_types) inf_le2 inf_sup_distrib1 subst_range.simps sup_bot.right_neutral)
  thus "range_vars \<delta> \<subseteq> vars\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>)"
    by (metis fv_snd_rcv_strand le_supI1 vars_snd_rcv_strand)
qed

lemma strand_subst_all_fv_subset:
  assumes "fv t \<subseteq> fv\<^sub>s\<^sub>t S" "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> bvars\<^sub>s\<^sub>t S = {}"
  shows "fv (t \<cdot> \<delta>) \<subseteq> fv\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>)"
using assms by (metis fv_strand_subst' Int_commute subst_apply_fv_subset)

lemma strand_subst_not_dom_fixed:
  assumes "v \<in> fv\<^sub>s\<^sub>t S" and "v \<notin> subst_domain \<delta>"
  shows "v \<in> fv\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>)"
using assms
proof (induction S)
  case (Cons x S')
  have 1: "\<And>X. v \<notin> subst_domain (rm_vars (set X) \<delta>)"
    using Cons.prems(2) rm_vars_dom_subset by force
  
  show ?case
  proof (cases "v \<in> fv\<^sub>s\<^sub>t S'")
    case True thus ?thesis using Cons.IH[OF _ Cons.prems(2)] by auto
  next
    case False
    hence 2: "v \<in> fv\<^sub>s\<^sub>t\<^sub>p x" using Cons.prems(1) by simp
    hence "v \<in> fv\<^sub>s\<^sub>t\<^sub>p (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>)" using Cons.prems(2) subst_not_dom_fixed
    proof (cases x)
      case (Inequality X F)
      hence "v \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X" using 2 by simp
      hence "v \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<delta>)"
        using subst_not_dom_fixed[OF _ 1]
        by (induct F) (auto simp add: subst_apply_pairs_def)
      thus ?thesis using Inequality 2 by auto
    qed (force simp add: subst_domain_def)+
    thus ?thesis by auto
  qed
qed simp

lemma strand_vars_unfold: "v \<in> vars\<^sub>s\<^sub>t S \<Longrightarrow> \<exists>S' x S''. S = S'@x#S'' \<and> v \<in> vars\<^sub>s\<^sub>t\<^sub>p x"
proof (induction S)
  case (Cons x S) thus ?case
  proof (cases "v \<in> vars\<^sub>s\<^sub>t\<^sub>p x")
    case True thus ?thesis by blast
  next
    case False
    hence "v \<in> vars\<^sub>s\<^sub>t S" using Cons.prems by auto
    thus ?thesis using Cons.IH by (metis append_Cons)
  qed
qed simp

lemma strand_fv_unfold: "v \<in> fv\<^sub>s\<^sub>t S \<Longrightarrow> \<exists>S' x S''. S = S'@x#S'' \<and> v \<in> fv\<^sub>s\<^sub>t\<^sub>p x"
proof (induction S)
  case (Cons x S) thus ?case
  proof (cases "v \<in> fv\<^sub>s\<^sub>t\<^sub>p x")
    case True thus ?thesis by blast
  next
    case False
    hence "v \<in> fv\<^sub>s\<^sub>t S" using Cons.prems by auto
    thus ?thesis using Cons.IH by (metis append_Cons)
  qed
qed simp

lemma subterm_if_in_strand_ik:
  "t \<in> ik\<^sub>s\<^sub>t S \<Longrightarrow> \<exists>t'. Receive t' \<in> set S \<and> t \<sqsubseteq> t'"
by (induct S rule: ik\<^sub>s\<^sub>t_induct) auto

lemma fv_subset_if_in_strand_ik:
  "t \<in> ik\<^sub>s\<^sub>t S \<Longrightarrow> fv t \<subseteq> \<Union>(set (map fv\<^sub>r\<^sub>c\<^sub>v S))"
proof -
  assume "t \<in> ik\<^sub>s\<^sub>t S"
  then obtain t' where "Receive t' \<in> set S" "t \<sqsubseteq> t'" by (metis subterm_if_in_strand_ik)
  hence "fv t \<subseteq> fv t'" by (simp add: subtermeq_vars_subset)
  thus ?thesis using in_strand_fv_subset_rcv[OF \<open>Receive t' \<in> set S\<close>] by auto
qed

lemma fv_subset_if_in_strand_ik':
  "t \<in> ik\<^sub>s\<^sub>t S \<Longrightarrow> fv t \<subseteq> fv\<^sub>s\<^sub>t S"
using fv_subset_if_in_strand_ik[of t S] fv_snd_rcv_strand_subset(2)[of S] by blast

lemma vars_subset_if_in_strand_ik2:
  "t \<in> ik\<^sub>s\<^sub>t S \<Longrightarrow> fv t \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S"
using fv_subset_if_in_strand_ik[of t S] vars_snd_rcv_strand_subset2(2)[of S] by blast


subsection \<open>Lemmata: Simple Strands\<close>
lemma simple_Cons[dest]: "simple (s#S) \<Longrightarrow> simple S"
unfolding simple_def by auto

lemma simple_split[dest]:
  assumes "simple (S@S')"
  shows "simple S" "simple S'"
using assms unfolding simple_def by auto

lemma simple_append[intro]: "\<lbrakk>simple S; simple S'\<rbrakk> \<Longrightarrow> simple (S@S')"
unfolding simple_def by auto

lemma simple_append_sym[sym]: "simple (S@S') \<Longrightarrow> simple (S'@S)" by auto

lemma not_simple_if_snd_fun: "(\<exists>S' S'' f X. S = S'@Send (Fun f X)#S'') \<Longrightarrow> \<not>simple S"
unfolding simple_def by auto

lemma not_list_all_elim: "\<not>list_all P A \<Longrightarrow> \<exists>B x C. A = B@x#C \<and> \<not>P x \<and> list_all P B"
proof (induction A rule: List.rev_induct)
  case (snoc a A)
  show ?case
  proof (cases "list_all P A")
    case True
    thus ?thesis using snoc.prems by auto
  next
    case False
    then obtain B x C where "A = B@x#C" "\<not>P x" "list_all P B" using snoc.IH[OF False] by auto
    thus ?thesis by auto
  qed
qed simp

lemma not_simple\<^sub>s\<^sub>t\<^sub>p_elim:
  assumes "\<not>simple\<^sub>s\<^sub>t\<^sub>p x"
  shows "(\<exists>f T. x = Send (Fun f T)) \<or> 
         (\<exists>a t t'. x = Equality a t t') \<or>
         (\<exists>X F. x = Inequality X F \<and> \<not>(\<exists>\<I>. ineq_model \<I> X F))"
using assms by (cases x) (fastforce elim: simple\<^sub>s\<^sub>t\<^sub>p.elims)+

lemma not_simple_elim:
  assumes "\<not>simple S"
  shows "(\<exists>A B f T. S = A@Send (Fun f T)#B \<and> simple A) \<or> 
         (\<exists>A B a t t'. S = A@Equality a t t'#B \<and> simple A) \<or>
         (\<exists>A B X F. S = A@Inequality X F#B \<and> \<not>(\<exists>\<I>. ineq_model \<I> X F))"
by (metis assms not_list_all_elim not_simple\<^sub>s\<^sub>t\<^sub>p_elim simple_def)

lemma simple_fun_prefix_unique:
  assumes "A = S@Send (Fun f X)#S'" "simple S"
  shows "\<forall>T g Y T'. A = T@Send (Fun g Y)#T' \<and> simple T \<longrightarrow> S = T \<and> f = g \<and> X = Y \<and> S' = T'"
proof -
  { fix T g Y T' assume *: "A = T@Send (Fun g Y)#T'" "simple T"
    { assume "length S < length T" hence False using assms *
        by (metis id_take_nth_drop not_simple_if_snd_fun nth_append nth_append_length)
    }
    moreover
    { assume "length S > length T" hence False using assms *
        by (metis id_take_nth_drop not_simple_if_snd_fun nth_append nth_append_length)
    }
    ultimately have "S = T" using assms * by (meson List.append_eq_append_conv linorder_neqE_nat)
  }
  thus ?thesis using assms(1) by blast
qed

lemma simple_snd_is_var: "\<lbrakk>Send t \<in> set S; simple S\<rbrakk> \<Longrightarrow> \<exists>v. t = Var v"
unfolding simple_def
by (metis list_all_append list_all_simps(1) simple\<^sub>s\<^sub>t\<^sub>p.elims(2) split_list_first
          strand_step.distinct(1) strand_step.distinct(5) strand_step.inject(1)) 


subsection \<open>Lemmata: Strand Measure\<close>
lemma measure\<^sub>s\<^sub>t_wellfounded: "wf measure\<^sub>s\<^sub>t" unfolding measure\<^sub>s\<^sub>t_def by simp

lemma strand_size_append[iff]: "size\<^sub>s\<^sub>t (S@S') = size\<^sub>s\<^sub>t S + size\<^sub>s\<^sub>t S'"
by (induct S) (auto simp add: size\<^sub>s\<^sub>t_def)

lemma strand_size_map_fun_lt[simp]:
  "size\<^sub>s\<^sub>t (map Send X) < size (Fun f X)"
  "size\<^sub>s\<^sub>t (map Send X) < size\<^sub>s\<^sub>t [Send (Fun f X)]"
  "size\<^sub>s\<^sub>t (map Send X) < size\<^sub>s\<^sub>t [Receive (Fun f X)]"
by (induct X) (auto simp add: size\<^sub>s\<^sub>t_def)

lemma strand_size_rm_fun_lt[simp]:
  "size\<^sub>s\<^sub>t (S@S') < size\<^sub>s\<^sub>t (S@Send (Fun f X)#S')"
  "size\<^sub>s\<^sub>t (S@S') < size\<^sub>s\<^sub>t (S@Receive (Fun f X)#S')"
by (induct S) (auto simp add: size\<^sub>s\<^sub>t_def)

lemma strand_fv_card_map_fun_eq:
  "card (fv\<^sub>s\<^sub>t (S@Send (Fun f X)#S')) = card (fv\<^sub>s\<^sub>t (S@(map Send X)@S'))"
proof -
  have "fv\<^sub>s\<^sub>t (S@Send (Fun f X)#S') = fv\<^sub>s\<^sub>t (S@(map Send X)@S')" by auto
  thus ?thesis by simp
qed

lemma strand_fv_card_rm_fun_le[simp]: "card (fv\<^sub>s\<^sub>t (S@S')) \<le> card (fv\<^sub>s\<^sub>t (S@Send (Fun f X)#S'))"
by (force intro: card_mono)

lemma strand_fv_card_rm_eq_le[simp]: "card (fv\<^sub>s\<^sub>t (S@S')) \<le> card (fv\<^sub>s\<^sub>t (S@Equality a t t'#S'))"
by (force intro: card_mono)


subsection \<open>Lemmata: Well-formed Strands\<close>
lemma wf_prefix[dest]: "wf\<^sub>s\<^sub>t V (S@S') \<Longrightarrow> wf\<^sub>s\<^sub>t V S"
by (induct S rule: wf\<^sub>s\<^sub>t.induct) auto

lemma wf_vars_mono[simp]: "wf\<^sub>s\<^sub>t V S \<Longrightarrow> wf\<^sub>s\<^sub>t (V \<union> W) S"
proof (induction S arbitrary: V)
  case (Cons x S) thus ?case
  proof (cases x)
    case (Send t)
    hence "wf\<^sub>s\<^sub>t (V \<union> fv t \<union> W) S" using Cons.prems(1) Cons.IH by simp
    thus ?thesis using Send by (simp add: sup_commute sup_left_commute)
  next
    case (Equality a t t')
    show ?thesis
    proof (cases a)
      case Assign
      hence "wf\<^sub>s\<^sub>t (V \<union> fv t \<union> W) S" "fv t' \<subseteq> V \<union> W" using Equality Cons.prems(1) Cons.IH by auto
      thus ?thesis using Equality Assign by (simp add: sup_commute sup_left_commute)
    next
      case Check thus ?thesis using Equality Cons by auto
    qed
  qed auto
qed simp

lemma wf\<^sub>s\<^sub>tI[intro]: "wfrestrictedvars\<^sub>s\<^sub>t S \<subseteq> V \<Longrightarrow> wf\<^sub>s\<^sub>t V S"
proof (induction S)
  case (Cons x S) thus ?case
  proof (cases x)
    case (Send t)
    hence "wf\<^sub>s\<^sub>t V S" "V \<union> fv t = V" using Cons by auto
    thus ?thesis using Send by simp
  next
    case (Equality a t t')
    show ?thesis
    proof (cases a)
      case Assign
      hence "wf\<^sub>s\<^sub>t V S" "fv t' \<subseteq> V" using Equality Cons by auto
      thus ?thesis using wf_vars_mono Equality Assign by simp
    next
      case Check thus ?thesis using Equality Cons by auto
    qed
  qed simp_all
qed simp

lemma wf\<^sub>s\<^sub>tI'[intro]: "\<Union>(fv\<^sub>r\<^sub>c\<^sub>v ` set S) \<union> \<Union>(fv_r\<^sub>e\<^sub>q assign ` set S) \<subseteq> V \<Longrightarrow> wf\<^sub>s\<^sub>t V S"
proof (induction S)
  case (Cons x S) thus ?case
  proof (cases x)
    case (Equality a t t') thus ?thesis using Cons by (cases a) auto
  qed simp_all
qed simp

lemma wf_append_exec: "wf\<^sub>s\<^sub>t V (S@S') \<Longrightarrow> wf\<^sub>s\<^sub>t (V \<union> wfvarsoccs\<^sub>s\<^sub>t S) S'"
proof (induction S arbitrary: V)
  case (Cons x S V) thus ?case
  proof (cases x)
    case (Send t)
    hence "wf\<^sub>s\<^sub>t (V \<union> fv t \<union> wfvarsoccs\<^sub>s\<^sub>t S) S'" using Cons.prems Cons.IH by simp
    thus ?thesis using Send by (auto simp add: sup_assoc)
  next
    case (Equality a t t') show ?thesis
    proof (cases a)
      case Assign
      hence "wf\<^sub>s\<^sub>t (V \<union> fv t \<union> wfvarsoccs\<^sub>s\<^sub>t S) S'" using Equality Cons.prems Cons.IH by auto
      thus ?thesis using Equality Assign by (auto simp add: sup_assoc)
    next
      case Check
      hence "wf\<^sub>s\<^sub>t (V \<union> wfvarsoccs\<^sub>s\<^sub>t S) S'" using Equality Cons.prems Cons.IH by auto
      thus ?thesis using Equality Check by (auto simp add: sup_assoc)
    qed
  qed auto
qed simp

lemma wf_append_suffix:
  "wf\<^sub>s\<^sub>t V S \<Longrightarrow> wfrestrictedvars\<^sub>s\<^sub>t S' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> V \<Longrightarrow> wf\<^sub>s\<^sub>t V (S@S')"
proof (induction V S rule: wf\<^sub>s\<^sub>t_induct)
  case (ConsSnd V t S)
  hence *: "wf\<^sub>s\<^sub>t (V \<union> fv t) S" by simp_all
  hence "wfrestrictedvars\<^sub>s\<^sub>t S' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> (V \<union> fv t)"
    using ConsSnd.prems(2) by fastforce
  thus ?case using ConsSnd.IH * by simp
next
  case (ConsRcv V t S)
  hence *: "fv t \<subseteq> V" "wf\<^sub>s\<^sub>t V S" by simp_all
  hence "wfrestrictedvars\<^sub>s\<^sub>t S' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> V"
    using ConsRcv.prems(2) by fastforce
  thus ?case using ConsRcv.IH * by simp
next
  case (ConsEq V t t' S)
  hence *: "fv t' \<subseteq> V" "wf\<^sub>s\<^sub>t (V \<union> fv t) S" by simp_all
  moreover have "vars\<^sub>s\<^sub>t\<^sub>p (Equality Assign t t') = fv t \<union> fv t'"
    by simp
  moreover have "wfrestrictedvars\<^sub>s\<^sub>t (Equality Assign t t'#S) = fv t \<union> fv t' \<union> wfrestrictedvars\<^sub>s\<^sub>t S"
    by auto
  ultimately have "wfrestrictedvars\<^sub>s\<^sub>t S' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> (V \<union> fv t)"
    using ConsEq.prems(2) by blast
  thus ?case using ConsEq.IH * by simp
qed (simp_all add: wf\<^sub>s\<^sub>tI)

lemma wf_append_suffix':
  assumes "wf\<^sub>s\<^sub>t V S"
    and "\<Union>(fv\<^sub>r\<^sub>c\<^sub>v ` set S') \<union> \<Union>(fv_r\<^sub>e\<^sub>q assign ` set S') \<subseteq> wfvarsoccs\<^sub>s\<^sub>t S \<union> V"
  shows "wf\<^sub>s\<^sub>t V (S@S')"
using assms
proof (induction V S rule: wf\<^sub>s\<^sub>t_induct)
  case (ConsSnd V t S)
  hence *: "wf\<^sub>s\<^sub>t (V \<union> fv t) S" by simp_all
  have "wfvarsoccs\<^sub>s\<^sub>t (send\<langle>t\<rangle>\<^sub>s\<^sub>t#S) = fv t \<union> wfvarsoccs\<^sub>s\<^sub>t S"
    unfolding wfvarsoccs\<^sub>s\<^sub>t_def by simp
  hence "(\<Union>a\<in>set S'. fv\<^sub>r\<^sub>c\<^sub>v a) \<union> (\<Union>a\<in>set S'. fv_r\<^sub>e\<^sub>q assign a) \<subseteq> wfvarsoccs\<^sub>s\<^sub>t S \<union> (V \<union> fv t)"
    using ConsSnd.prems(2) unfolding wfvarsoccs\<^sub>s\<^sub>t_def by auto
  thus ?case using ConsSnd.IH[OF *] by auto
next
  case (ConsEq V t t' S)
  hence *: "fv t' \<subseteq> V" "wf\<^sub>s\<^sub>t (V \<union> fv t) S" by simp_all
  have "wfvarsoccs\<^sub>s\<^sub>t (\<langle>assign: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t#S) = fv t \<union> wfvarsoccs\<^sub>s\<^sub>t S"
    unfolding wfvarsoccs\<^sub>s\<^sub>t_def by simp
  hence "(\<Union>a\<in>set S'. fv\<^sub>r\<^sub>c\<^sub>v a) \<union> (\<Union>a\<in>set S'. fv_r\<^sub>e\<^sub>q assign a) \<subseteq> wfvarsoccs\<^sub>s\<^sub>t S \<union> (V \<union> fv t)"
    using ConsEq.prems(2) unfolding wfvarsoccs\<^sub>s\<^sub>t_def by auto
  thus ?case using ConsEq.IH[OF *(2)] *(1) by auto
qed (auto simp add: wf\<^sub>s\<^sub>tI')

lemma wf_send_compose: "wf\<^sub>s\<^sub>t V (S@(map Send X)@S') = wf\<^sub>s\<^sub>t V (S@Send (Fun f X)#S')"
proof (induction S arbitrary: V)
  case Nil thus ?case 
  proof (induction X arbitrary: V)
    case (Cons y Y) thus ?case by (simp add: sup_assoc)
  qed simp
next
  case (Cons s S) thus ?case
  proof (cases s)
    case (Equality ac t t') thus ?thesis using Cons by (cases ac) auto
  qed auto
qed

lemma wf_snd_append[iff]: "wf\<^sub>s\<^sub>t V (S@[Send t]) = wf\<^sub>s\<^sub>t V S"
by (induct S rule: wf\<^sub>s\<^sub>t.induct) simp_all

lemma wf_snd_append': "wf\<^sub>s\<^sub>t V S \<Longrightarrow> wf\<^sub>s\<^sub>t V (Send t#S)"
by simp

lemma wf_rcv_append[dest]: "wf\<^sub>s\<^sub>t V (S@Receive t#S') \<Longrightarrow> wf\<^sub>s\<^sub>t V (S@S')"
by (induct S rule: wf\<^sub>s\<^sub>t.induct) simp_all

lemma wf_rcv_append'[intro]:
  "\<lbrakk>wf\<^sub>s\<^sub>t V (S@S'); fv t \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> V\<rbrakk> \<Longrightarrow> wf\<^sub>s\<^sub>t V (S@Receive t#S')"
proof (induction S rule: wf\<^sub>s\<^sub>t_induct)
  case (ConsRcv V t' S)
  hence "wf\<^sub>s\<^sub>t V (S@S')" "fv t \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> V"
    by auto+
  thus ?case using ConsRcv by auto
next
  case (ConsEq V t' t'' S)
  hence "fv t'' \<subseteq> V" by simp
  moreover have
      "wfrestrictedvars\<^sub>s\<^sub>t (Equality Assign t' t''#S) = fv t' \<union> fv t'' \<union> wfrestrictedvars\<^sub>s\<^sub>t S"
    by auto
  ultimately have "fv t \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> (V \<union> fv t')"
    using ConsEq.prems(2) by blast
  thus ?case using ConsEq by auto
qed auto

lemma wf_rcv_append''[intro]: "\<lbrakk>wf\<^sub>s\<^sub>t V S; fv t \<subseteq> \<Union>(set (map fv\<^sub>s\<^sub>n\<^sub>d S))\<rbrakk> \<Longrightarrow> wf\<^sub>s\<^sub>t V (S@[Receive t])"
by (induct S)
   (simp, metis vars_snd_rcv_strand_subset2(1) append_Nil2 le_supI1 order_trans wf_rcv_append')

lemma wf_rcv_append'''[intro]: "\<lbrakk>wf\<^sub>s\<^sub>t V S; fv t \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> V\<rbrakk> \<Longrightarrow> wf\<^sub>s\<^sub>t V (S@[Receive t])"
by (simp add: wf_rcv_append'[of _ _ "[]"])

lemma wf_eq_append[dest]: "wf\<^sub>s\<^sub>t V (S@Equality a t t'#S') \<Longrightarrow> fv t \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> V \<Longrightarrow> wf\<^sub>s\<^sub>t V (S@S')"
proof (induction S rule: wf\<^sub>s\<^sub>t_induct)
  case (Nil V)
  hence "wf\<^sub>s\<^sub>t (V \<union> fv t) S'" by (cases a) auto
  moreover have "V \<union> fv t = V" using Nil by auto
  ultimately show ?case by simp
next
  case (ConsRcv V u S)
  hence "wf\<^sub>s\<^sub>t V (S @ Equality a t t' # S')" "fv t \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> V" "fv u \<subseteq> V"
    by fastforce+
  hence "wf\<^sub>s\<^sub>t V (S@S')" using ConsRcv.IH by auto
  thus ?case using \<open>fv u \<subseteq> V\<close> by simp
next
  case (ConsEq V u u' S)
  hence "wf\<^sub>s\<^sub>t (V \<union> fv u) (S@Equality a t t'#S')" "fv t \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> (V \<union> fv u)" "fv u' \<subseteq> V"
    by auto
  hence "wf\<^sub>s\<^sub>t (V \<union> fv u) (S@S')" using ConsEq.IH by auto
  thus ?case using \<open>fv u' \<subseteq> V\<close> by simp
qed auto

lemma wf_eq_append'[intro]:
  "\<lbrakk>wf\<^sub>s\<^sub>t V (S@S'); fv t' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> V\<rbrakk> \<Longrightarrow> wf\<^sub>s\<^sub>t V (S@Equality a t t'#S')"
proof (induction S rule: wf\<^sub>s\<^sub>t_induct)
  case Nil thus ?case by (cases a) auto
next
  case (ConsEq V u u' S)
  hence "wf\<^sub>s\<^sub>t (V \<union> fv u) (S@S')" "fv t' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> V \<union> fv u"
    by fastforce+
  thus ?case using ConsEq by auto
next
  case (ConsEq2 V u u' S)
  hence "wf\<^sub>s\<^sub>t V (S@S')" by auto
  thus ?case using ConsEq2 by auto
next
  case (ConsRcv V u S)
  hence "wf\<^sub>s\<^sub>t V (S@S')" "fv t' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> V"
    by fastforce+
  thus ?case using ConsRcv by auto
next
  case (ConsSnd V u S)
  hence "wf\<^sub>s\<^sub>t (V \<union> fv u) (S@S')" "fv t' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> (V \<union> fv u)"
    by fastforce+
  thus ?case using ConsSnd by auto
qed auto

lemma wf_eq_append''[intro]:
  "\<lbrakk>wf\<^sub>s\<^sub>t V (S@S'); fv t' \<subseteq> wfvarsoccs\<^sub>s\<^sub>t S \<union> V\<rbrakk> \<Longrightarrow> wf\<^sub>s\<^sub>t V (S@[Equality a t t']@S')"
proof (induction S rule: wf\<^sub>s\<^sub>t_induct)
  case Nil thus ?case by (cases a) auto
next
  case (ConsEq V u u' S)
  hence "wf\<^sub>s\<^sub>t (V \<union> fv u) (S@S')" "fv t' \<subseteq> wfvarsoccs\<^sub>s\<^sub>t S \<union> V \<union> fv u" by fastforce+
  thus ?case using ConsEq by auto
next
  case (ConsEq2 V u u' S)
  hence "wf\<^sub>s\<^sub>t (V \<union> fv u) (S@S')" "fv t' \<subseteq> wfvarsoccs\<^sub>s\<^sub>t S \<union> V \<union> fv u" by fastforce+
  thus ?case using ConsEq2 by auto
next
  case (ConsRcv V u S)
  hence "wf\<^sub>s\<^sub>t V (S@S')" "fv t' \<subseteq> wfvarsoccs\<^sub>s\<^sub>t S \<union> V" by fastforce+
  thus ?case using ConsRcv by auto
next
  case (ConsSnd V u S)
  hence "wf\<^sub>s\<^sub>t (V \<union> fv u) (S@S')" "fv t' \<subseteq> wfvarsoccs\<^sub>s\<^sub>t S \<union> (V \<union> fv u)" by auto
  thus ?case using ConsSnd by auto
qed auto

lemma wf_eq_append'''[intro]:
  "\<lbrakk>wf\<^sub>s\<^sub>t V S; fv t' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S \<union> V\<rbrakk> \<Longrightarrow> wf\<^sub>s\<^sub>t V (S@[Equality a t t'])"
by (simp add: wf_eq_append'[of _ _ "[]"])

lemma wf_eq_check_append[dest]: "wf\<^sub>s\<^sub>t V (S@Equality Check t t'#S') \<Longrightarrow> wf\<^sub>s\<^sub>t V (S@S')"
by (induct S rule: wf\<^sub>s\<^sub>t.induct) simp_all

lemma wf_eq_check_append'[intro]: "wf\<^sub>s\<^sub>t V (S@S') \<Longrightarrow> wf\<^sub>s\<^sub>t V (S@Equality Check t t'#S')"
by (induct S rule: wf\<^sub>s\<^sub>t.induct) auto

lemma wf_eq_check_append''[intro]: "wf\<^sub>s\<^sub>t V S \<Longrightarrow> wf\<^sub>s\<^sub>t V (S@[Equality Check t t'])"
by (induct S rule: wf\<^sub>s\<^sub>t.induct) auto

lemma wf_ineq_append[dest]: "wf\<^sub>s\<^sub>t V (S@Inequality X F#S') \<Longrightarrow> wf\<^sub>s\<^sub>t V (S@S')"
by (induct S rule: wf\<^sub>s\<^sub>t.induct) simp_all

lemma wf_ineq_append'[intro]: "wf\<^sub>s\<^sub>t V (S@S') \<Longrightarrow> wf\<^sub>s\<^sub>t V (S@Inequality X F#S')"
by (induct S rule: wf\<^sub>s\<^sub>t.induct) auto

lemma wf_ineq_append''[intro]: "wf\<^sub>s\<^sub>t V S \<Longrightarrow> wf\<^sub>s\<^sub>t V (S@[Inequality X F])"
by (induct S rule: wf\<^sub>s\<^sub>t.induct) auto

lemma wf_rcv_fv_single[elim]: "wf\<^sub>s\<^sub>t V (Receive t#S') \<Longrightarrow> fv t \<subseteq> V"
by simp

lemma wf_rcv_fv: "wf\<^sub>s\<^sub>t V (S@Receive t#S') \<Longrightarrow> fv t \<subseteq> wfvarsoccs\<^sub>s\<^sub>t S \<union> V"
by (induct S arbitrary: V) (auto split!: strand_step.split poscheckvariant.split)

lemma wf_eq_fv: "wf\<^sub>s\<^sub>t V (S@Equality Assign t t'#S') \<Longrightarrow> fv t' \<subseteq> wfvarsoccs\<^sub>s\<^sub>t S \<union> V"
by (induct S arbitrary: V) (auto split!: strand_step.split poscheckvariant.split)

lemma wf_simple_fv_occurrence:
  assumes "wf\<^sub>s\<^sub>t {} S" "simple S" "v \<in> wfrestrictedvars\<^sub>s\<^sub>t S"
  shows "\<exists>S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f. S = S\<^sub>p\<^sub>r\<^sub>e@Send (Var v)#S\<^sub>s\<^sub>u\<^sub>f \<and> v \<notin> wfrestrictedvars\<^sub>s\<^sub>t S\<^sub>p\<^sub>r\<^sub>e"
using assms
proof (induction S rule: List.rev_induct)
  case (snoc x S)
  from \<open>wf\<^sub>s\<^sub>t {} (S@[x])\<close> have "wf\<^sub>s\<^sub>t {} S" "wf\<^sub>s\<^sub>t (wfrestrictedvars\<^sub>s\<^sub>t S) [x]"
    using wf_append_exec[THEN wf_vars_mono, of "{}" S "[x]" "wfrestrictedvars\<^sub>s\<^sub>t S - wfvarsoccs\<^sub>s\<^sub>t S"]
          vars_snd_rcv_strand_subset2(4)[of S]
          Diff_partition[of "wfvarsoccs\<^sub>s\<^sub>t S" "wfrestrictedvars\<^sub>s\<^sub>t S"]
    by auto
  from \<open>simple (S@[x])\<close> have "simple S" "simple\<^sub>s\<^sub>t\<^sub>p x" unfolding simple_def by auto

  show ?case
  proof (cases "v \<in> wfrestrictedvars\<^sub>s\<^sub>t S")
    case False
    show ?thesis
    proof (cases x)
      case (Receive t)
      hence "fv t \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S" using \<open>wf\<^sub>s\<^sub>t (wfrestrictedvars\<^sub>s\<^sub>t S) [x]\<close> by simp
      hence "v \<in> wfrestrictedvars\<^sub>s\<^sub>t S"
        using \<open>v \<in> wfrestrictedvars\<^sub>s\<^sub>t (S@[x])\<close> \<open>x = Receive t\<close>
        by auto
      thus ?thesis using \<open>x = Receive t\<close> snoc.IH[OF \<open>wf\<^sub>s\<^sub>t {} S\<close> \<open>simple S\<close>] by fastforce
    next
      case (Send t)
      hence "v \<in> vars\<^sub>s\<^sub>t\<^sub>p x" using \<open>v \<in> wfrestrictedvars\<^sub>s\<^sub>t (S@[x])\<close> False by auto
      from Send obtain w where "t = Var w" using \<open>simple\<^sub>s\<^sub>t\<^sub>p x\<close> by (cases t) simp_all
      hence "v = w" using \<open>x = Send t\<close> \<open>v \<in> vars\<^sub>s\<^sub>t\<^sub>p x\<close> by simp
      thus ?thesis using \<open>x = Send t\<close> \<open>v \<notin> wfrestrictedvars\<^sub>s\<^sub>t S\<close> \<open>t = Var w\<close> by auto
    next
      case (Equality ac t t') thus ?thesis using snoc.prems(2) unfolding simple_def by auto
    next
      case (Inequality t t') thus ?thesis using False snoc.prems(3) by auto
    qed
  qed (use snoc.IH[OF \<open>wf\<^sub>s\<^sub>t {} S\<close> \<open>simple S\<close>] in fastforce)
qed simp

lemma Unifier_strand_fv_subset:
  assumes g_in_ik: "t \<in> ik\<^sub>s\<^sub>t S"
  and \<delta>: "Unifier \<delta> (Fun f X) t"
  and disj: "bvars\<^sub>s\<^sub>t S \<inter> (subst_domain \<delta> \<union> range_vars \<delta>) = {}"
  shows "fv (Fun f X \<cdot> \<delta>) \<subseteq> \<Union>(set (map fv\<^sub>r\<^sub>c\<^sub>v (S \<cdot>\<^sub>s\<^sub>t \<delta>)))"
by (metis (no_types) fv_subset_if_in_strand_ik[OF g_in_ik]
          disj \<delta> fv_strand_subst subst_apply_fv_subset)

lemma wf\<^sub>s\<^sub>t_induct'[consumes 1, case_names Nil ConsSnd ConsRcv ConsEq ConsEq2 ConsIneq]:
  fixes S::"('a,'b) strand"
  assumes "wf\<^sub>s\<^sub>t V S"
          "P []"
          "\<And>t S. \<lbrakk>wf\<^sub>s\<^sub>t V S; P S\<rbrakk> \<Longrightarrow> P (S@[Send t])"
          "\<And>t S. \<lbrakk>wf\<^sub>s\<^sub>t V S; P S; fv t \<subseteq> V \<union> wfvarsoccs\<^sub>s\<^sub>t S\<rbrakk> \<Longrightarrow> P (S@[Receive t])"
          "\<And>t t' S. \<lbrakk>wf\<^sub>s\<^sub>t V S; P S; fv t' \<subseteq> V \<union> wfvarsoccs\<^sub>s\<^sub>t S\<rbrakk> \<Longrightarrow> P (S@[Equality Assign t t'])"
          "\<And>t t' S. \<lbrakk>wf\<^sub>s\<^sub>t V S; P S\<rbrakk> \<Longrightarrow> P (S@[Equality Check t t'])"
          "\<And>X F S. \<lbrakk>wf\<^sub>s\<^sub>t V S; P S\<rbrakk> \<Longrightarrow> P (S@[Inequality X F])"
  shows "P S"
using assms
proof (induction S rule: List.rev_induct)
  case (snoc x S)
  hence *: "wf\<^sub>s\<^sub>t V S" "wf\<^sub>s\<^sub>t (V \<union> wfvarsoccs\<^sub>s\<^sub>t S) [x]" by (metis wf_prefix, metis wf_append_exec)
  have IH: "P S" using snoc.IH[OF *(1)] snoc.prems by auto
  note ** = snoc.prems(3,4,5,6,7)[OF *(1) IH] *(2)
  show ?case using **(1,2,4,5,6)
  proof (cases x)
    case (Equality ac t t')
    then show ?thesis using **(3,4,6) by (cases ac) auto
  qed auto
qed simp

lemma wf_subst_apply:
  "wf\<^sub>s\<^sub>t V S \<Longrightarrow> wf\<^sub>s\<^sub>t (fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)) (S \<cdot>\<^sub>s\<^sub>t \<delta>)"
proof (induction S arbitrary: V rule: wf\<^sub>s\<^sub>t_induct)
  case (ConsRcv V t S)
  hence "wf\<^sub>s\<^sub>t V S" "fv t \<subseteq> V" by simp_all
  hence "wf\<^sub>s\<^sub>t (fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)) (S \<cdot>\<^sub>s\<^sub>t \<delta>)" "fv (t \<cdot> \<delta>) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
    using ConsRcv.IH subst_apply_fv_subset by simp_all
  thus ?case by simp
next
  case (ConsSnd V t S)
  hence "wf\<^sub>s\<^sub>t (V \<union> fv t) S" by simp
  hence "wf\<^sub>s\<^sub>t (fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` (V \<union> fv t))) (S \<cdot>\<^sub>s\<^sub>t \<delta>)" using ConsSnd.IH by metis
  hence "wf\<^sub>s\<^sub>t (fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V) \<union> fv (t \<cdot> \<delta>)) (S \<cdot>\<^sub>s\<^sub>t \<delta>)" using subst_apply_fv_union by metis
  thus ?case by simp
next
  case (ConsEq V t t' S)
  hence "wf\<^sub>s\<^sub>t (V \<union> fv t) S" "fv t' \<subseteq> V" by auto
  hence "wf\<^sub>s\<^sub>t (fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` (V \<union> fv t))) (S \<cdot>\<^sub>s\<^sub>t \<delta>)" and *: "fv (t' \<cdot> \<delta>) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
    using ConsEq.IH subst_apply_fv_subset by force+
  hence "wf\<^sub>s\<^sub>t (fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V) \<union> fv (t \<cdot> \<delta>)) (S \<cdot>\<^sub>s\<^sub>t \<delta>)" using subst_apply_fv_union by metis
  thus ?case using * by simp
qed simp_all

lemma wf_unify:
  assumes wf: "wf\<^sub>s\<^sub>t V (S@Send (Fun f X)#S')"
  and g_in_ik: "t \<in> ik\<^sub>s\<^sub>t S"
  and \<delta>: "Unifier \<delta> (Fun f X) t"
  and disj: "bvars\<^sub>s\<^sub>t (S@Send (Fun f X)#S') \<inter> (subst_domain \<delta> \<union> range_vars \<delta>) = {}"
  shows "wf\<^sub>s\<^sub>t (fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)) ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>)"
using assms
proof (induction S' arbitrary: V rule: List.rev_induct)
  case (snoc x S' V)
  have fun_fv_bound: "fv (Fun f X \<cdot> \<delta>) \<subseteq> \<Union>(set (map fv\<^sub>r\<^sub>c\<^sub>v (S \<cdot>\<^sub>s\<^sub>t \<delta>)))"
    using snoc.prems(4) bvars\<^sub>s\<^sub>t_split Unifier_strand_fv_subset[OF g_in_ik \<delta>] by auto
  hence "fv (Fun f X \<cdot> \<delta>) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>))" using fv_ik_is_fv_rcv by metis
  hence "fv (Fun f X \<cdot> \<delta>) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>)" using fv_ik_subset_fv_st[of "S \<cdot>\<^sub>s\<^sub>t \<delta>"] by blast
  hence *: "fv ((Fun f X) \<cdot> \<delta>) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>)" by fastforce

  from snoc.prems(1) have "wf\<^sub>s\<^sub>t V (S@Send (Fun f X)#S')"
    using wf_prefix[of V "S@Send (Fun f X)#S'" "[x]"] by simp
  hence **: "wf\<^sub>s\<^sub>t (fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)) ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>)"
    using snoc.IH[OF _ snoc.prems(2,3)] snoc.prems(4) by auto

  from snoc.prems(1) have ***: "wf\<^sub>s\<^sub>t (V \<union> wfvarsoccs\<^sub>s\<^sub>t (S@Send (Fun f X)#S')) [x]"
    using wf_append_exec[of V "(S@Send (Fun f X)#S')" "[x]"] by simp

  from snoc.prems(4) have disj':
      "bvars\<^sub>s\<^sub>t (S@S') \<inter> (subst_domain \<delta> \<union> range_vars \<delta>) = {}"
      "set (bvars\<^sub>s\<^sub>t\<^sub>p x) \<inter> (subst_domain \<delta> \<union> range_vars \<delta>) = {}"
    by auto

  show ?case
  proof (cases x)
    case (Send t)
    thus ?thesis using wf_snd_append[of "fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)" "(S@S') \<cdot>\<^sub>s\<^sub>t \<delta>"] ** by auto
  next
    case (Receive t)
    hence "fv\<^sub>s\<^sub>t\<^sub>p x \<subseteq> V \<union> wfvarsoccs\<^sub>s\<^sub>t (S@Send (Fun f X)#S')" using *** by auto
    hence "fv\<^sub>s\<^sub>t\<^sub>p x \<subseteq> V \<union> wfrestrictedvars\<^sub>s\<^sub>t (S@Send (Fun f X)#S')"
      using vars_snd_rcv_strand_subset2(4)[of "S@Send (Fun f X)#S'"] by blast
    hence "fv\<^sub>s\<^sub>t\<^sub>p x \<subseteq> V \<union> fv (Fun f X) \<union> wfrestrictedvars\<^sub>s\<^sub>t (S@S')" by auto
    hence "fv\<^sub>s\<^sub>t\<^sub>p (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V) \<union> fv ((Fun f X) \<cdot> \<delta>) \<union> wfrestrictedvars\<^sub>s\<^sub>t ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>)"
      by (metis (no_types) inf_sup_aci(5) subst_apply_fv_subset_strand2 subst_apply_fv_union disj')
    hence "fv\<^sub>s\<^sub>t\<^sub>p (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V) \<union> wfrestrictedvars\<^sub>s\<^sub>t ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>)" using * by blast
    hence "fv (t \<cdot> \<delta>) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V) " using \<open>x = Receive t\<close> by auto
    hence "wf\<^sub>s\<^sub>t (fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)) (((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>)@[Receive (t \<cdot> \<delta>)])"
      using wf_rcv_append'''[OF **, of "t \<cdot> \<delta>"] by metis
    thus ?thesis using \<open>x = Receive t\<close> by auto
  next
    case (Equality ac s s') show ?thesis
    proof (cases ac)
      case Assign
      hence "fv s' \<subseteq> V \<union> wfvarsoccs\<^sub>s\<^sub>t (S@Send (Fun f X)#S')" using Equality *** by auto
      hence "fv s' \<subseteq> V \<union> wfrestrictedvars\<^sub>s\<^sub>t (S@Send (Fun f X)#S')"
        using vars_snd_rcv_strand_subset2(4)[of "S@Send (Fun f X)#S'"] by blast
      hence "fv s' \<subseteq> V \<union> fv (Fun f X) \<union> wfrestrictedvars\<^sub>s\<^sub>t (S@S')" by auto
      moreover have "fv s' = fv_r\<^sub>e\<^sub>q ac x" "fv (s' \<cdot> \<delta>) = fv_r\<^sub>e\<^sub>q ac (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>)"
        using Equality by simp_all
      ultimately have "fv (s' \<cdot> \<delta>) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V) \<union> fv (Fun f X \<cdot> \<delta>) \<union> wfrestrictedvars\<^sub>s\<^sub>t ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>)"
        using subst_apply_fv_subset_strand2[of "fv\<^sub>e\<^sub>q ac" ac x]
        by (metis disj'(1) subst_apply_fv_subset_strand_trm2 subst_apply_fv_union sup_commute)
      hence "fv (s' \<cdot> \<delta>) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V) \<union> wfrestrictedvars\<^sub>s\<^sub>t ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>)" using * by blast
      hence "fv (s' \<cdot> \<delta>) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
        using \<open>x = Equality ac s s'\<close> by auto
      hence "wf\<^sub>s\<^sub>t (fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)) (((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>)@[Equality ac (s \<cdot> \<delta>) (s' \<cdot> \<delta>)])"
        using wf_eq_append'''[OF **] by metis
      thus ?thesis using \<open>x = Equality ac s s'\<close> by auto
    next
      case Check thus ?thesis using wf_eq_check_append''[OF **] Equality by simp
    qed
  next
    case (Inequality t t') thus ?thesis using wf_ineq_append''[OF **] by simp
  qed
qed (auto dest: wf_subst_apply)

lemma wf_equality:
  assumes wf: "wf\<^sub>s\<^sub>t V (S@Equality ac t t'#S')"
  and \<delta>: "mgu t t' = Some \<delta>"
  and disj: "bvars\<^sub>s\<^sub>t (S@Equality ac t t'#S') \<inter> (subst_domain \<delta> \<union> range_vars \<delta>) = {}"
  shows "wf\<^sub>s\<^sub>t (fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)) ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>)"
using assms
proof (induction S' arbitrary: V rule: List.rev_induct)
  case Nil thus ?case using wf_prefix[of V S "[Equality ac t t']"] wf_subst_apply[of V S \<delta>] by auto
next
  case (snoc x S' V) show ?case
  proof (cases ac)
    case Assign
    hence "fv t' \<subseteq> V \<union> wfvarsoccs\<^sub>s\<^sub>t S"
      using wf_eq_fv[of V, of S t t' "S'@[x]"] snoc by auto
    hence "fv t' \<subseteq> V \<union> wfrestrictedvars\<^sub>s\<^sub>t S"
      using vars_snd_rcv_strand_subset2(4)[of S] by blast
    hence "fv t' \<subseteq> V \<union> wfrestrictedvars\<^sub>s\<^sub>t (S@S')" by force
    moreover have disj':
        "bvars\<^sub>s\<^sub>t (S@S') \<inter> (subst_domain \<delta> \<union> range_vars \<delta>) = {}"
        "set (bvars\<^sub>s\<^sub>t\<^sub>p x) \<inter> (subst_domain \<delta> \<union> range_vars \<delta>) = {}"
        "bvars\<^sub>s\<^sub>t (S@Equality ac t t'#S') \<inter> (subst_domain \<delta> \<union> range_vars \<delta>) = {}"
      using snoc.prems(3) by auto
    ultimately have
        "fv (t' \<cdot> \<delta>) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V) \<union> wfrestrictedvars\<^sub>s\<^sub>t ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>)"
      by (metis inf_sup_aci(5) subst_apply_fv_subset_strand_trm2)
    moreover have "fv (t \<cdot> \<delta>) = fv (t' \<cdot> \<delta>)"
      by (metis MGU_is_Unifier[OF mgu_gives_MGU[OF \<delta>]])
    ultimately have *:
        "fv (t \<cdot> \<delta>) \<union> fv (t' \<cdot> \<delta>) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V) \<union> wfrestrictedvars\<^sub>s\<^sub>t ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>)"
      by simp
  
    from snoc.prems(1) have "wf\<^sub>s\<^sub>t V (S@Equality ac t t'#S')"
      using wf_prefix[of V "S@Equality ac t t'#S'"] by simp
    hence **: "wf\<^sub>s\<^sub>t (fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)) ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>)" by (metis snoc.IH \<delta> disj'(3))
  
    from snoc.prems(1) have ***: "wf\<^sub>s\<^sub>t (V \<union> wfvarsoccs\<^sub>s\<^sub>t (S@Equality ac t t'#S')) [x]"
      using wf_append_exec[of V "(S@Equality ac t t'#S')" "[x]"] by simp
  
    show ?thesis
    proof (cases x)
      case (Send t)
      thus ?thesis using wf_snd_append[of "fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)" "(S@S') \<cdot>\<^sub>s\<^sub>t \<delta>"] ** by auto
    next
      case (Receive s)
      hence "fv\<^sub>s\<^sub>t\<^sub>p x \<subseteq> V \<union> wfvarsoccs\<^sub>s\<^sub>t (S@Equality ac t t'#S')" using *** by auto
      hence "fv\<^sub>s\<^sub>t\<^sub>p x \<subseteq> V \<union> wfrestrictedvars\<^sub>s\<^sub>t (S@Equality ac t t'#S')"
        using vars_snd_rcv_strand_subset2(4)[of "S@Equality ac t t'#S'"] by blast
      hence "fv\<^sub>s\<^sub>t\<^sub>p x \<subseteq> V \<union> fv t \<union> fv t' \<union> wfrestrictedvars\<^sub>s\<^sub>t (S@S')"
        by (cases ac) auto
      hence "fv\<^sub>s\<^sub>t\<^sub>p (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V) \<union> fv (t \<cdot> \<delta>) \<union> fv (t' \<cdot> \<delta>) \<union> wfrestrictedvars\<^sub>s\<^sub>t ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>)"
        using subst_apply_fv_subset_strand2[of fv\<^sub>s\<^sub>t\<^sub>p]
        by (metis (no_types) inf_sup_aci(5) subst_apply_fv_union disj'(1,2))
      hence "fv\<^sub>s\<^sub>t\<^sub>p (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V) \<union> wfrestrictedvars\<^sub>s\<^sub>t ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>)"
        when "ac = Assign"
        using * that by blast
      hence "fv (s \<cdot> \<delta>) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>) \<union> (fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V))"
        when "ac = Assign"
        using \<open>x = Receive s\<close> that by auto
      hence "wf\<^sub>s\<^sub>t (fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)) (((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>)@[Receive (s \<cdot> \<delta>)])"
        when "ac = Assign"
        using wf_rcv_append'''[OF **, of "s \<cdot> \<delta>"] that by metis
      thus ?thesis using \<open>x = Receive s\<close> Assign by auto
    next
      case (Equality ac' s s') show ?thesis
      proof (cases ac')
        case Assign
        hence "fv s' \<subseteq> V \<union> wfvarsoccs\<^sub>s\<^sub>t (S@Equality ac t t'#S')" using *** Equality by auto
        hence "fv s' \<subseteq> V \<union> wfrestrictedvars\<^sub>s\<^sub>t (S@Equality ac t t'#S')"
          using vars_snd_rcv_strand_subset2(4)[of "S@Equality ac t t'#S'"] by blast
        hence "fv s' \<subseteq> V \<union> fv t \<union> fv t' \<union> wfrestrictedvars\<^sub>s\<^sub>t (S@S')"
          by (cases ac) auto
        moreover have "fv s' = fv_r\<^sub>e\<^sub>q ac' x" "fv (s' \<cdot> \<delta>) = fv_r\<^sub>e\<^sub>q ac' (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>)"
          using Equality by simp_all
        ultimately have
            "fv (s' \<cdot> \<delta>) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V) \<union> fv (t \<cdot> \<delta>) \<union> fv (t' \<cdot> \<delta>) \<union> wfrestrictedvars\<^sub>s\<^sub>t ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>)"
          using subst_apply_fv_subset_strand2[of "fv_r\<^sub>e\<^sub>q ac'" ac' x]
          by (metis disj'(1) subst_apply_fv_subset_strand_trm2 subst_apply_fv_union sup_commute)
        hence "fv (s' \<cdot> \<delta>) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V) \<union> wfrestrictedvars\<^sub>s\<^sub>t ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>)"
          using * \<open>ac = Assign\<close> by blast
        hence ****:
            "fv (s' \<cdot> \<delta>) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
          using \<open>x = Equality ac' s s'\<close> \<open>ac = Assign\<close> by auto
        thus ?thesis
          using \<open>x = Equality ac' s s'\<close> ** **** wf_eq_append' \<open>ac = Assign\<close>
          by (metis (no_types, lifting) append.assoc append_Nil2 strand_step.case(3)
                strand_subst_hom subst_apply_strand_step_def)
      next
        case Check thus ?thesis using wf_eq_check_append''[OF **] Equality by simp
      qed
    next
      case (Inequality s s') thus ?thesis using wf_ineq_append''[OF **] by simp
    qed
  qed (metis snoc.prems(1) wf_eq_check_append wf_subst_apply)
qed

lemma wf_rcv_prefix_ground:
  "wf\<^sub>s\<^sub>t {} ((map Receive M)@S) \<Longrightarrow> vars\<^sub>s\<^sub>t (map Receive M) = {}"
by (induct M) auto

lemma simple_wfvarsoccs\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>n\<^sub>d:
  assumes "simple S"
  shows "wfvarsoccs\<^sub>s\<^sub>t S = \<Union>(set (map fv\<^sub>s\<^sub>n\<^sub>d S))"
using assms unfolding simple_def
proof (induction S)
  case (Cons x S) thus ?case by (cases x) auto
qed simp

lemma wf\<^sub>s\<^sub>t_simple_induct[consumes 2, case_names Nil ConsSnd ConsRcv ConsIneq]:
  fixes S::"('a,'b) strand"
  assumes "wf\<^sub>s\<^sub>t V S" "simple S"
          "P []"
          "\<And>v S. \<lbrakk>wf\<^sub>s\<^sub>t V S; simple S; P S\<rbrakk> \<Longrightarrow> P (S@[Send (Var v)])"
          "\<And>t S. \<lbrakk>wf\<^sub>s\<^sub>t V S; simple S; P S; fv t \<subseteq> V \<union> \<Union>(set (map fv\<^sub>s\<^sub>n\<^sub>d S))\<rbrakk> \<Longrightarrow> P (S@[Receive t])"
          "\<And>X F S. \<lbrakk>wf\<^sub>s\<^sub>t V S; simple S; P S\<rbrakk> \<Longrightarrow> P (S@[Inequality X F])"
  shows "P S"
using assms
proof (induction S rule: wf\<^sub>s\<^sub>t_induct')
  case (ConsSnd t S)
  hence "P S" by auto
  obtain v where "t = Var v" using simple_snd_is_var[OF _ \<open>simple (S@[Send t])\<close>] by auto
  thus ?case using ConsSnd.prems(3)[OF \<open>wf\<^sub>s\<^sub>t V S\<close> _ \<open>P S\<close>] \<open>simple (S@[Send t])\<close> by auto
next
  case (ConsRcv t S) thus ?case using simple_wfvarsoccs\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>n\<^sub>d[of "S@[Receive t]"] by auto
qed (auto simp add: simple_def)

lemma wf_trm_stp_dom_fv_disjoint:
  "\<lbrakk>wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S \<theta>; t \<in> trms\<^sub>s\<^sub>t S\<rbrakk> \<Longrightarrow> subst_domain \<theta> \<inter> fv t = {}"
unfolding wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r_def by force

lemma wf_constr_bvars_disj: "wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S \<theta> \<Longrightarrow> (subst_domain \<theta> \<union> range_vars \<theta>) \<inter> bvars\<^sub>s\<^sub>t S = {}"
unfolding range_vars_alt_def wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r_def by fastforce

lemma wf_constr_bvars_disj':
  assumes "wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S \<theta>" "subst_domain \<delta> \<union> range_vars \<delta> \<subseteq> fv\<^sub>s\<^sub>t S"
  shows "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> bvars\<^sub>s\<^sub>t S = {}" (is ?A)
  and "(subst_domain \<theta> \<union> range_vars \<theta>) \<inter> bvars\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>) = {}" (is ?B)
proof -
  have "(subst_domain \<theta> \<union> range_vars \<theta>) \<inter> bvars\<^sub>s\<^sub>t S = {}" "fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>s\<^sub>t S = {}"
    using assms(1) unfolding range_vars_alt_def wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r_def by fastforce+
  thus ?A and ?B using assms(2) bvars_subst_ident[of S \<delta>] by blast+
qed

lemma (in intruder_model) wf_simple_strand_first_Send_var_split:
  assumes "wf\<^sub>s\<^sub>t {} S" "simple S" "\<exists>v \<in> wfrestrictedvars\<^sub>s\<^sub>t S. t \<cdot> \<I> = \<I> v"
  shows "\<exists>v S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f. S = S\<^sub>p\<^sub>r\<^sub>e@Send (Var v)#S\<^sub>s\<^sub>u\<^sub>f \<and> t \<cdot> \<I> = \<I> v
                      \<and> \<not>(\<exists>w \<in> wfrestrictedvars\<^sub>s\<^sub>t S\<^sub>p\<^sub>r\<^sub>e. t \<cdot> \<I> = \<I> w)"
    (is "?P S")
using assms
proof (induction S rule: wf\<^sub>s\<^sub>t_simple_induct)
  case (ConsSnd v S) show ?case
  proof (cases "\<exists>w \<in> wfrestrictedvars\<^sub>s\<^sub>t S. t \<cdot> \<I> = \<I> w")
    case True thus ?thesis using ConsSnd.IH by fastforce
  next
    case False thus ?thesis using ConsSnd.prems by auto
  qed
next
  case (ConsRcv t' S)
  have "fv t' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S" using ConsRcv.hyps(3) vars_snd_rcv_strand_subset2(1) by force
  hence "\<exists>v \<in> wfrestrictedvars\<^sub>s\<^sub>t S. t \<cdot> \<I> = \<I> v"
    using ConsRcv.prems(1) by fastforce
  hence "?P S" by (metis ConsRcv.IH)
  thus ?case by fastforce 
next
  case (ConsIneq X F S)
  moreover have "wfrestrictedvars\<^sub>s\<^sub>t (S @ [Inequality X F]) = wfrestrictedvars\<^sub>s\<^sub>t S" by auto
  ultimately have "?P S" by blast
  thus ?case by fastforce
qed simp

lemma (in intruder_model) wf_strand_first_Send_var_split:
  assumes "wf\<^sub>s\<^sub>t {} S" "\<exists>v \<in> wfrestrictedvars\<^sub>s\<^sub>t S. t \<cdot> \<I> \<sqsubseteq> \<I> v"
  shows "\<exists>S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f. \<not>(\<exists>w \<in> wfrestrictedvars\<^sub>s\<^sub>t S\<^sub>p\<^sub>r\<^sub>e. t \<cdot> \<I> \<sqsubseteq> \<I> w)
            \<and> ((\<exists>t'. S = S\<^sub>p\<^sub>r\<^sub>e@Send t'#S\<^sub>s\<^sub>u\<^sub>f \<and> t \<cdot> \<I> \<sqsubseteq> t' \<cdot> \<I>)
               \<or> (\<exists>t' t''. S = S\<^sub>p\<^sub>r\<^sub>e@Equality Assign t' t''#S\<^sub>s\<^sub>u\<^sub>f \<and> t \<cdot> \<I> \<sqsubseteq> t' \<cdot> \<I>))"
    (is "\<exists>S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f. ?P S\<^sub>p\<^sub>r\<^sub>e \<and> ?Q S S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f")
using assms
proof (induction S rule: wf\<^sub>s\<^sub>t_induct')
  case (ConsSnd t' S) show ?case
  proof (cases "\<exists>w \<in> wfrestrictedvars\<^sub>s\<^sub>t S. t \<cdot> \<I> \<sqsubseteq> \<I> w")
    case True
    then obtain S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f where "?P S\<^sub>p\<^sub>r\<^sub>e" "?Q S S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f"
      using ConsSnd.IH by moura
    thus ?thesis by fastforce
  next
    case False
    then obtain v where v: "v \<in> fv t'" "t \<cdot> \<I> \<sqsubseteq> \<I> v"
      using ConsSnd.prems by auto
    hence "t \<cdot> \<I> \<sqsubseteq> t' \<cdot> \<I>"
      using subst_mono[of "Var v" t' \<I>] vars_iff_subtermeq[of v t'] term.order_trans
      by auto 
    thus ?thesis using False v by auto
  qed
next
  case (ConsRcv t' S)
  have "fv t' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S"
    using ConsRcv.hyps vars_snd_rcv_strand_subset2(4)[of S] by blast
  hence "\<exists>v \<in> wfrestrictedvars\<^sub>s\<^sub>t S. t \<cdot> \<I> \<sqsubseteq> \<I> v"
    using ConsRcv.prems by fastforce
  then obtain S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f where "?P S\<^sub>p\<^sub>r\<^sub>e" "?Q S S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f"
    using ConsRcv.IH by moura
  thus ?case by fastforce
next
  case (ConsEq s s' S)
  have *: "fv s' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t S"
    using ConsEq.hyps vars_snd_rcv_strand_subset2(4)[of S]
    by blast
  show ?case
  proof (cases "\<exists>v \<in> wfrestrictedvars\<^sub>s\<^sub>t S. t \<cdot> \<I> \<sqsubseteq> \<I> v")
    case True
    then obtain S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f where "?P S\<^sub>p\<^sub>r\<^sub>e" "?Q S S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f"
      using ConsEq.IH by moura
    thus ?thesis by fastforce
  next
    case False
    then obtain v where "v \<in> fv s" "t \<cdot> \<I> \<sqsubseteq> \<I> v" using ConsEq.prems * by auto
    hence "t \<cdot> \<I> \<sqsubseteq> s \<cdot> \<I>"
      using vars_iff_subtermeq[of v s] subst_mono[of "Var v" s \<I>] term.order_trans
      by auto
    thus ?thesis using False by fastforce
  qed
next
  case (ConsEq2 s s' S)
  have "wfrestrictedvars\<^sub>s\<^sub>t (S@[Equality Check s s']) = wfrestrictedvars\<^sub>s\<^sub>t S" by auto
  hence "\<exists>v \<in> wfrestrictedvars\<^sub>s\<^sub>t S. t \<cdot> \<I> \<sqsubseteq> \<I> v" using ConsEq2.prems by metis
  then obtain S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f where "?P S\<^sub>p\<^sub>r\<^sub>e" "?Q S S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f"
    using ConsEq2.IH by moura
  thus ?case by fastforce
next
  case (ConsIneq X F S)
  hence "\<exists>v \<in> wfrestrictedvars\<^sub>s\<^sub>t S. t \<cdot> \<I> \<sqsubseteq> \<I> v" by fastforce
  then obtain S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f where "?P S\<^sub>p\<^sub>r\<^sub>e" "?Q S S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f"
    using ConsIneq.IH by moura
  thus ?case by fastforce
qed simp


subsection \<open>Constraint Semantics\<close>
context intruder_model
begin

subsubsection \<open>Definitions\<close>
text \<open>The constraint semantics in which the intruder is limited to composition only\<close>
fun strand_sem_c::"('fun,'var) terms \<Rightarrow> ('fun,'var) strand \<Rightarrow> ('fun,'var) subst \<Rightarrow> bool" ("\<lbrakk>_; _\<rbrakk>\<^sub>c")
where
  "\<lbrakk>M; []\<rbrakk>\<^sub>c = (\<lambda>\<I>. True)"
| "\<lbrakk>M; Send t#S\<rbrakk>\<^sub>c = (\<lambda>\<I>. M \<turnstile>\<^sub>c t \<cdot> \<I> \<and> \<lbrakk>M; S\<rbrakk>\<^sub>c \<I>)"
| "\<lbrakk>M; Receive t#S\<rbrakk>\<^sub>c = (\<lambda>\<I>. \<lbrakk>insert (t \<cdot> \<I>) M; S\<rbrakk>\<^sub>c \<I>)"
| "\<lbrakk>M; Equality _ t t'#S\<rbrakk>\<^sub>c = (\<lambda>\<I>. t \<cdot> \<I> = t' \<cdot> \<I> \<and> \<lbrakk>M; S\<rbrakk>\<^sub>c \<I>)"
| "\<lbrakk>M; Inequality X F#S\<rbrakk>\<^sub>c = (\<lambda>\<I>. ineq_model \<I> X F \<and> \<lbrakk>M; S\<rbrakk>\<^sub>c \<I>)"

definition constr_sem_c ("_ \<Turnstile>\<^sub>c \<langle>_,_\<rangle>") where "\<I> \<Turnstile>\<^sub>c \<langle>S,\<theta>\<rangle> \<equiv> (\<theta> supports \<I> \<and> \<lbrakk>{}; S\<rbrakk>\<^sub>c \<I>)"
abbreviation constr_sem_c' ("_ \<Turnstile>\<^sub>c \<langle>_\<rangle>" 90) where "\<I> \<Turnstile>\<^sub>c \<langle>S\<rangle> \<equiv> \<I> \<Turnstile>\<^sub>c \<langle>S,Var\<rangle>"

text \<open>The full constraint semantics\<close>
fun strand_sem_d::"('fun,'var) terms \<Rightarrow> ('fun,'var) strand \<Rightarrow> ('fun,'var) subst \<Rightarrow> bool" ("\<lbrakk>_; _\<rbrakk>\<^sub>d")
where
  "\<lbrakk>M; []\<rbrakk>\<^sub>d = (\<lambda>\<I>. True)"
| "\<lbrakk>M; Send t#S\<rbrakk>\<^sub>d = (\<lambda>\<I>. M \<turnstile> t \<cdot> \<I> \<and> \<lbrakk>M; S\<rbrakk>\<^sub>d \<I>)"
| "\<lbrakk>M; Receive t#S\<rbrakk>\<^sub>d = (\<lambda>\<I>. \<lbrakk>insert (t \<cdot> \<I>) M; S\<rbrakk>\<^sub>d \<I>)"
| "\<lbrakk>M; Equality _ t t'#S\<rbrakk>\<^sub>d = (\<lambda>\<I>. t \<cdot> \<I> = t' \<cdot> \<I> \<and> \<lbrakk>M; S\<rbrakk>\<^sub>d \<I>)"
| "\<lbrakk>M; Inequality X F#S\<rbrakk>\<^sub>d = (\<lambda>\<I>. ineq_model \<I> X F \<and> \<lbrakk>M; S\<rbrakk>\<^sub>d \<I>)"

definition constr_sem_d ("_ \<Turnstile> \<langle>_,_\<rangle>") where "\<I> \<Turnstile> \<langle>S,\<theta>\<rangle> \<equiv> (\<theta> supports \<I> \<and> \<lbrakk>{}; S\<rbrakk>\<^sub>d \<I>)"
abbreviation constr_sem_d' ("_ \<Turnstile> \<langle>_\<rangle>" 90) where "\<I> \<Turnstile> \<langle>S\<rangle> \<equiv> \<I> \<Turnstile> \<langle>S,Var\<rangle>"

lemmas strand_sem_induct = strand_sem_c.induct[case_names Nil ConsSnd ConsRcv ConsEq ConsIneq]


subsubsection \<open>Lemmata\<close>
lemma strand_sem_d_if_c: "\<I> \<Turnstile>\<^sub>c \<langle>S,\<theta>\<rangle> \<Longrightarrow> \<I> \<Turnstile> \<langle>S,\<theta>\<rangle>"
proof -
  assume *: "\<I> \<Turnstile>\<^sub>c \<langle>S,\<theta>\<rangle>"
  { fix M have "\<lbrakk>M; S\<rbrakk>\<^sub>c \<I> \<Longrightarrow> \<lbrakk>M; S\<rbrakk>\<^sub>d \<I>"
    proof (induction S rule: strand_sem_induct)
      case (ConsSnd M t S)
      hence "M \<turnstile>\<^sub>c t \<cdot> \<I>" "\<lbrakk>M; S\<rbrakk>\<^sub>d \<I>" by auto
      thus ?case using strand_sem_d.simps(2)[of M t S] by auto
    qed (auto simp add: ineq_model_def)
  }
  thus ?thesis using * by (simp add: constr_sem_c_def constr_sem_d_def)
qed

lemma strand_sem_mono_ik:
  "\<lbrakk>M \<subseteq> M'; \<lbrakk>M; S\<rbrakk>\<^sub>c \<theta>\<rbrakk> \<Longrightarrow> \<lbrakk>M'; S\<rbrakk>\<^sub>c \<theta>" (is "\<lbrakk>?A'; ?A''\<rbrakk> \<Longrightarrow> ?A")
  "\<lbrakk>M \<subseteq> M'; \<lbrakk>M; S\<rbrakk>\<^sub>d \<theta>\<rbrakk> \<Longrightarrow> \<lbrakk>M'; S\<rbrakk>\<^sub>d \<theta>" (is "\<lbrakk>?B'; ?B''\<rbrakk> \<Longrightarrow> ?B")
proof -
  show "\<lbrakk>?A'; ?A''\<rbrakk> \<Longrightarrow> ?A"
  proof (induction M S arbitrary: M M' rule: strand_sem_induct)
    case (ConsRcv M t S)
    thus ?case using ConsRcv.IH[of "insert (t \<cdot> \<theta>) M" "insert (t \<cdot> \<theta>) M'"] by auto
  next
    case (ConsSnd M t S)
    hence "M \<turnstile>\<^sub>c t \<cdot> \<theta>" "\<lbrakk>M'; S\<rbrakk>\<^sub>c \<theta>" by auto
    hence "M' \<turnstile>\<^sub>c t \<cdot> \<theta>" using ideduct_synth_mono \<open>M \<subseteq> M'\<close> by metis
    thus ?case using \<open>\<lbrakk>M'; S\<rbrakk>\<^sub>c \<theta>\<close> by simp
  qed auto

  show "\<lbrakk>?B'; ?B''\<rbrakk> \<Longrightarrow> ?B"
  proof (induction M S arbitrary: M M' rule: strand_sem_induct)
    case (ConsRcv M t S)
    thus ?case using ConsRcv.IH[of "insert (t \<cdot> \<theta>) M" "insert (t \<cdot> \<theta>) M'"] by auto
  next
    case (ConsSnd M t S)
    hence "M \<turnstile> t \<cdot> \<theta>" "\<lbrakk>M'; S\<rbrakk>\<^sub>d \<theta>" by auto
    hence "M' \<turnstile> t \<cdot> \<theta>" using ideduct_mono \<open>M \<subseteq> M'\<close> by metis
    thus ?case using \<open>\<lbrakk>M'; S\<rbrakk>\<^sub>d \<theta>\<close> by simp
  qed auto
qed

context
begin
private lemma strand_sem_split_left:
  "\<lbrakk>M; S@S'\<rbrakk>\<^sub>c \<theta> \<Longrightarrow> \<lbrakk>M; S\<rbrakk>\<^sub>c \<theta>"
  "\<lbrakk>M; S@S'\<rbrakk>\<^sub>d \<theta> \<Longrightarrow> \<lbrakk>M; S\<rbrakk>\<^sub>d \<theta>"
proof (induct S arbitrary: M)
  case (Cons x S)
  { case 1 thus ?case using Cons by (cases x) simp_all }
  { case 2 thus ?case using Cons by (cases x) simp_all }
qed simp_all

private lemma strand_sem_split_right:
  "\<lbrakk>M; S@S'\<rbrakk>\<^sub>c \<theta> \<Longrightarrow> \<lbrakk>M \<union> (ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>); S'\<rbrakk>\<^sub>c \<theta>"
  "\<lbrakk>M; S@S'\<rbrakk>\<^sub>d \<theta> \<Longrightarrow> \<lbrakk>M \<union> (ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>); S'\<rbrakk>\<^sub>d \<theta>"
proof (induction S arbitrary: M rule: ik\<^sub>s\<^sub>t_induct)
  case (ConsRcv t S)
  { case 1 thus ?case using ConsRcv.IH[of "insert (t \<cdot> \<theta>) M"] by simp }
  { case 2 thus ?case using ConsRcv.IH[of "insert (t \<cdot> \<theta>) M"] by simp }
qed simp_all

lemmas strand_sem_split[dest] =
  strand_sem_split_left(1) strand_sem_split_right(1)
  strand_sem_split_left(2) strand_sem_split_right(2)
end

lemma strand_sem_Send_split[dest]:
  "\<lbrakk>\<lbrakk>M; map Send T\<rbrakk>\<^sub>c \<theta>; t \<in> set T\<rbrakk> \<Longrightarrow> \<lbrakk>M; [Send t]\<rbrakk>\<^sub>c \<theta>" (is "\<lbrakk>?A'; ?A''\<rbrakk> \<Longrightarrow> ?A")
  "\<lbrakk>\<lbrakk>M; map Send T\<rbrakk>\<^sub>d \<theta>; t \<in> set T\<rbrakk> \<Longrightarrow> \<lbrakk>M; [Send t]\<rbrakk>\<^sub>d \<theta>" (is "\<lbrakk>?B'; ?B''\<rbrakk> \<Longrightarrow> ?B")
  "\<lbrakk>\<lbrakk>M; map Send T@S\<rbrakk>\<^sub>c \<theta>; t \<in> set T\<rbrakk> \<Longrightarrow> \<lbrakk>M; Send t#S\<rbrakk>\<^sub>c \<theta>" (is "\<lbrakk>?C'; ?C''\<rbrakk> \<Longrightarrow> ?C")
  "\<lbrakk>\<lbrakk>M; map Send T@S\<rbrakk>\<^sub>d \<theta>; t \<in> set T\<rbrakk> \<Longrightarrow> \<lbrakk>M; Send t#S\<rbrakk>\<^sub>d \<theta>" (is "\<lbrakk>?D'; ?D''\<rbrakk> \<Longrightarrow> ?D")
proof -
  show A: "\<lbrakk>?A'; ?A''\<rbrakk> \<Longrightarrow> ?A" by (induct "map Send T" arbitrary: T rule: strand_sem_c.induct) auto
  show B: "\<lbrakk>?B'; ?B''\<rbrakk> \<Longrightarrow> ?B" by (induct "map Send T" arbitrary: T rule: strand_sem_d.induct) auto
  show "\<lbrakk>?C'; ?C''\<rbrakk> \<Longrightarrow> ?C" "\<lbrakk>?D'; ?D''\<rbrakk> \<Longrightarrow> ?D"
    using list.set_map list.simps(8) set_empty ik_snd_empty sup_bot.right_neutral
    by (metis (no_types, lifting) A strand_sem_split(1,2) strand_sem_c.simps(2),
        metis (no_types, lifting) B strand_sem_split(3,4) strand_sem_d.simps(2))
qed

lemma strand_sem_Send_map:
  "(\<And>t. t \<in> set T \<Longrightarrow> \<lbrakk>M; [Send t]\<rbrakk>\<^sub>c \<I>) \<Longrightarrow> \<lbrakk>M; map Send T\<rbrakk>\<^sub>c \<I>"
  "(\<And>t. t \<in> set T \<Longrightarrow> \<lbrakk>M; [Send t]\<rbrakk>\<^sub>d \<I>) \<Longrightarrow> \<lbrakk>M; map Send T\<rbrakk>\<^sub>d \<I>"
by (induct T) auto

lemma strand_sem_Receive_map: "\<lbrakk>M; map Receive T\<rbrakk>\<^sub>c \<I>" "\<lbrakk>M; map Receive T\<rbrakk>\<^sub>d \<I>"
by (induct T arbitrary: M) auto

lemma strand_sem_append[intro]:
  "\<lbrakk>\<lbrakk>M; S\<rbrakk>\<^sub>c \<theta>; \<lbrakk>M \<union> (ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>); S'\<rbrakk>\<^sub>c \<theta>\<rbrakk> \<Longrightarrow> \<lbrakk>M; S@S'\<rbrakk>\<^sub>c \<theta>"
  "\<lbrakk>\<lbrakk>M; S\<rbrakk>\<^sub>d \<theta>; \<lbrakk>M \<union> (ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>); S'\<rbrakk>\<^sub>d \<theta>\<rbrakk> \<Longrightarrow> \<lbrakk>M; S@S'\<rbrakk>\<^sub>d \<theta>"
proof (induction S arbitrary: M)
  case (Cons x S) 
  { case 1 thus ?case using Cons by (cases x) auto }
  { case 2 thus ?case using Cons by (cases x) auto }
qed simp_all

lemma ineq_model_subst:
  fixes F::"(('a,'b) term \<times> ('a,'b) term) list"
  assumes "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> set X = {}"
    and "ineq_model (\<delta> \<circ>\<^sub>s \<theta>) X F"
  shows "ineq_model \<theta> X (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>)"
proof -
  { fix \<sigma>::"('a,'b) subst" and t t'
    assume \<sigma>: "subst_domain \<sigma> = set X" "ground (subst_range \<sigma>)"
        and *: "list_ex (\<lambda>f. fst f \<cdot> (\<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>)) \<noteq> snd f \<cdot> (\<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>))) F"
    obtain f where f: "f \<in> set F" "fst f \<cdot> \<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>) \<noteq> snd f \<cdot> \<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>)"
      using * by (induct F) auto
    have "\<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>) = \<delta> \<circ>\<^sub>s (\<sigma> \<circ>\<^sub>s \<theta>)"
      by (metis (no_types, lifting) \<sigma> subst_compose_assoc assms(1) inf_sup_aci(1)
              subst_comp_eq_if_disjoint_vars sup_inf_absorb range_vars_alt_def) 
    hence "(fst f \<cdot> \<delta>) \<cdot> \<sigma> \<circ>\<^sub>s \<theta> \<noteq> (snd f \<cdot> \<delta>) \<cdot> \<sigma> \<circ>\<^sub>s \<theta>" using f by auto
    moreover have "(fst f \<cdot> \<delta>, snd f \<cdot> \<delta>) \<in> set (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>)"
      using f(1) by (auto simp add: subst_apply_pairs_def)
    ultimately have "list_ex (\<lambda>f. fst f \<cdot> (\<sigma> \<circ>\<^sub>s \<theta>) \<noteq> snd f \<cdot> (\<sigma> \<circ>\<^sub>s \<theta>)) (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>)"
      using f(1) Bex_set by fastforce
  }
  thus ?thesis using assms unfolding ineq_model_def by simp
qed

lemma ineq_model_subst':
  fixes F::"(('a,'b) term \<times> ('a,'b) term) list"
  assumes "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> set X = {}"
    and "ineq_model \<theta> X (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>)"
  shows "ineq_model (\<delta> \<circ>\<^sub>s \<theta>) X F"
proof -
  { fix \<sigma>::"('a,'b) subst" and t t'
    assume \<sigma>: "subst_domain \<sigma> = set X" "ground (subst_range \<sigma>)"
        and *: "list_ex (\<lambda>f. fst f \<cdot> (\<sigma> \<circ>\<^sub>s \<theta>) \<noteq> snd f \<cdot> (\<sigma> \<circ>\<^sub>s \<theta>)) (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>)"
    obtain f where f: "f \<in> set (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>)" "fst f \<cdot> \<sigma> \<circ>\<^sub>s \<theta> \<noteq> snd f \<cdot> \<sigma> \<circ>\<^sub>s \<theta>"
      using * by (induct F) (auto simp add: subst_apply_pairs_def)
    then obtain g where g: "g \<in> set F" "f = g \<cdot>\<^sub>p \<delta>" by (auto simp add: subst_apply_pairs_def)
    have "\<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>) = \<delta> \<circ>\<^sub>s (\<sigma> \<circ>\<^sub>s \<theta>)"
      by (metis (no_types, lifting) \<sigma> subst_compose_assoc assms(1) inf_sup_aci(1)
              subst_comp_eq_if_disjoint_vars sup_inf_absorb range_vars_alt_def) 
    hence "fst g \<cdot> \<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>) \<noteq> snd g \<cdot> \<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>)"
      using f(2) g by (simp add: prod.case_eq_if)
    hence "list_ex (\<lambda>f. fst f \<cdot> (\<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>)) \<noteq> snd f \<cdot> (\<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>))) F"
      using g Bex_set by fastforce
  }
  thus ?thesis using assms unfolding ineq_model_def by simp
qed

lemma ineq_model_ground_subst:
  fixes F::"(('a,'b) term \<times> ('a,'b) term) list"
  assumes "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X \<subseteq> subst_domain \<delta>"
    and "ground (subst_range \<delta>)"
    and "ineq_model \<delta> X F"
  shows "ineq_model (\<delta> \<circ>\<^sub>s \<theta>) X F"
proof -
  { fix \<sigma>::"('a,'b) subst" and t t'
    assume \<sigma>: "subst_domain \<sigma> = set X" "ground (subst_range \<sigma>)"
        and *: "list_ex (\<lambda>f. fst f \<cdot> (\<sigma> \<circ>\<^sub>s \<delta>) \<noteq> snd f \<cdot> (\<sigma> \<circ>\<^sub>s \<delta> )) F"
    obtain f where f: "f \<in> set F" "fst f \<cdot> \<sigma> \<circ>\<^sub>s \<delta> \<noteq> snd f \<cdot> \<sigma> \<circ>\<^sub>s \<delta>"
      using * by (induct F) auto
    hence "fv (fst f) \<subseteq> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F" "fv (snd f) \<subseteq> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F" by auto
    hence "fv (fst f) - set X \<subseteq> subst_domain \<delta>" "fv (snd f) - set X \<subseteq> subst_domain \<delta>"
      using assms(1) by auto
    hence "fv (fst f \<cdot> \<sigma>) \<subseteq> subst_domain \<delta>" "fv (snd f \<cdot> \<sigma>) \<subseteq> subst_domain \<delta>"
      using \<sigma> by (simp_all add: range_vars_alt_def subst_fv_unfold_ground_img)
    hence "fv (fst f \<cdot> \<sigma> \<circ>\<^sub>s \<delta>) = {}" "fv (snd f \<cdot> \<sigma> \<circ>\<^sub>s \<delta>) = {}"
      using assms(2) by (simp_all add: subst_fv_dom_ground_if_ground_img)
    hence "fst f \<cdot> \<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>) \<noteq> snd f \<cdot> \<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>)" using f(2) subst_ground_ident by fastforce 
    hence "list_ex (\<lambda>f. fst f \<cdot> (\<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>)) \<noteq> snd f \<cdot> (\<sigma> \<circ>\<^sub>s (\<delta> \<circ>\<^sub>s \<theta>))) F"
      using f(1) Bex_set by fastforce
  }
  thus ?thesis using assms unfolding ineq_model_def by simp
qed

context
begin
private lemma strand_sem_subst_c:
  assumes "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> bvars\<^sub>s\<^sub>t S = {}"
  shows "\<lbrakk>M; S\<rbrakk>\<^sub>c (\<delta> \<circ>\<^sub>s \<theta>) \<Longrightarrow> \<lbrakk>M; S \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>c \<theta>"
using assms
proof (induction S arbitrary: \<delta> M rule: strand_sem_induct)
  case (ConsSnd M t S)
  hence "\<lbrakk>M; S \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>c \<theta>" "M \<turnstile>\<^sub>c t \<cdot> (\<delta> \<circ>\<^sub>s \<theta>)" by auto
  hence "M \<turnstile>\<^sub>c (t \<cdot> \<delta>) \<cdot> \<theta>"
    using subst_comp_all[of \<delta> \<theta> M] subst_subst_compose[of t \<delta> \<theta>] by simp
  thus ?case
    using \<open>\<lbrakk>M; S \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>c \<theta>\<close>
    unfolding subst_apply_strand_def
    by simp
next
  case (ConsRcv M t S)
  have *: "\<lbrakk>insert (t \<cdot> \<delta> \<circ>\<^sub>s \<theta>) M; S\<rbrakk>\<^sub>c (\<delta> \<circ>\<^sub>s \<theta>)" using ConsRcv.prems(1) by simp
  have "bvars\<^sub>s\<^sub>t (Receive t#S) = bvars\<^sub>s\<^sub>t S" by auto
  hence **: "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> bvars\<^sub>s\<^sub>t S = {}" using ConsRcv.prems(2) by blast
  have "\<lbrakk>M; Receive (t \<cdot> \<delta>)#(S \<cdot>\<^sub>s\<^sub>t \<delta>)\<rbrakk>\<^sub>c \<theta>"
    using ConsRcv.IH[OF * **] by (simp add: subst_all_insert)
  thus ?case by simp
next
  case (ConsIneq M X F S)
  hence *: "\<lbrakk>M; S \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>c \<theta>" and
        ***: "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> set X = {}" 
    unfolding bvars\<^sub>s\<^sub>t_def ineq_model_def by auto
  have **: "ineq_model (\<delta> \<circ>\<^sub>s \<theta>) X F"
    using ConsIneq by (auto simp add: subst_compose_assoc ineq_model_def)
  have "\<forall>\<gamma>. subst_domain \<gamma> = set X \<and> ground (subst_range \<gamma>)
          \<longrightarrow> (subst_domain \<delta> \<union> range_vars \<delta>) \<inter> (subst_domain \<gamma> \<union> range_vars \<gamma>) = {}"
    using * ** *** unfolding range_vars_alt_def by auto
  hence "\<forall>\<gamma>. subst_domain \<gamma> = set X \<and> ground (subst_range \<gamma>) \<longrightarrow> \<gamma> \<circ>\<^sub>s \<delta> = \<delta> \<circ>\<^sub>s \<gamma>"
    by (metis subst_comp_eq_if_disjoint_vars)
  hence "ineq_model \<theta> X (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>)"
    using ineq_model_subst[OF *** **]
    by blast
  moreover have "rm_vars (set X) \<delta> = \<delta>" using ConsIneq.prems(2) by force
  ultimately show ?case using * by auto
qed simp_all

private lemma strand_sem_subst_c':
  assumes "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> bvars\<^sub>s\<^sub>t S = {}"
  shows "\<lbrakk>M; S \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>c \<theta> \<Longrightarrow> \<lbrakk>M; S\<rbrakk>\<^sub>c (\<delta> \<circ>\<^sub>s \<theta>)"
using assms
proof (induction S arbitrary: \<delta> M rule: strand_sem_induct)
  case (ConsSnd M t S)
  hence "\<lbrakk>M; [Send t] \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>c \<theta>" "\<lbrakk>M; S \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>c \<theta>" by auto
  hence "\<lbrakk>M; S\<rbrakk>\<^sub>c (\<delta> \<circ>\<^sub>s \<theta>)" using ConsSnd.IH[OF _] ConsSnd.prems(2) by auto
  moreover have "\<lbrakk>M; [Send t]\<rbrakk>\<^sub>c (\<delta> \<circ>\<^sub>s \<theta>)"
  proof -
    have "M \<turnstile>\<^sub>c t \<cdot> \<delta> \<cdot> \<theta>" using \<open>\<lbrakk>M; [Send t] \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>c \<theta>\<close> by auto
    hence "M \<turnstile>\<^sub>c t \<cdot> (\<delta> \<circ>\<^sub>s \<theta>)" using subst_subst_compose by metis
    thus "\<lbrakk>M; [Send t]\<rbrakk>\<^sub>c (\<delta> \<circ>\<^sub>s \<theta>)" by auto
  qed
  ultimately show ?case by auto
next
  case (ConsRcv M t S)
  hence "\<lbrakk>(insert (t \<cdot> \<delta> \<cdot> \<theta>) M); S \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>c \<theta>" by (simp add: subst_all_insert)
  thus ?case using ConsRcv.IH ConsRcv.prems(2) by auto
next
  case (ConsIneq M X F S)
  have \<delta>: "rm_vars (set X) \<delta> = \<delta>" using ConsIneq.prems(2) by force
  hence *: "\<lbrakk>M; S\<rbrakk>\<^sub>c (\<delta> \<circ>\<^sub>s \<theta>)"
    and ***: "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> set X = {}"
    using ConsIneq unfolding bvars\<^sub>s\<^sub>t_def ineq_model_def by auto
  have **: "ineq_model \<theta> X (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>)"
    using ConsIneq.prems(1) \<delta> by (auto simp add: subst_compose_assoc ineq_model_def)
  have "\<forall>\<gamma>. subst_domain \<gamma> = set X \<and> ground (subst_range \<gamma>)
          \<longrightarrow> (subst_domain \<delta> \<union> range_vars \<delta>) \<inter> (subst_domain \<gamma> \<union> range_vars \<gamma>) = {}"
    using * ** *** unfolding range_vars_alt_def by auto
  hence "\<forall>\<gamma>. subst_domain \<gamma> = set X \<and> ground (subst_range \<gamma>) \<longrightarrow> \<gamma> \<circ>\<^sub>s \<delta> = \<delta> \<circ>\<^sub>s \<gamma>"
    by (metis subst_comp_eq_if_disjoint_vars)
  hence "ineq_model (\<delta> \<circ>\<^sub>s \<theta>) X F"
    using ineq_model_subst'[OF *** **]
    by blast
  thus ?case using * by auto
next
  case ConsEq thus ?case unfolding bvars\<^sub>s\<^sub>t_def by auto
qed simp_all

private lemma strand_sem_subst_d:
  assumes "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> bvars\<^sub>s\<^sub>t S = {}"
  shows "\<lbrakk>M; S\<rbrakk>\<^sub>d (\<delta> \<circ>\<^sub>s \<theta>) \<Longrightarrow> \<lbrakk>M; S \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>d \<theta>"
using assms
proof (induction S arbitrary: \<delta> M rule: strand_sem_induct)
  case (ConsSnd M t S)
  hence "\<lbrakk>M; S \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>d \<theta>" "M \<turnstile> t \<cdot> (\<delta> \<circ>\<^sub>s \<theta>)" by auto
  hence "M \<turnstile> (t \<cdot> \<delta>) \<cdot> \<theta>"
    using subst_comp_all[of \<delta> \<theta> M] subst_subst_compose[of t \<delta> \<theta>] by simp
  thus ?case using \<open>\<lbrakk>M; S \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>d \<theta>\<close> by simp
next
  case (ConsRcv M t S) 
  have *: "\<lbrakk>insert (t \<cdot> \<delta> \<circ>\<^sub>s \<theta>) M; S\<rbrakk>\<^sub>d (\<delta> \<circ>\<^sub>s \<theta>)" using ConsRcv.prems(1) by simp
  have "bvars\<^sub>s\<^sub>t (Receive t#S) = bvars\<^sub>s\<^sub>t S" by auto
  hence **: "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> bvars\<^sub>s\<^sub>t S = {}" using ConsRcv.prems(2) by blast
  have "\<lbrakk>M; Receive (t \<cdot> \<delta>)#(S \<cdot>\<^sub>s\<^sub>t \<delta>)\<rbrakk>\<^sub>d \<theta>"
    using ConsRcv.IH[OF * **] by (simp add: subst_all_insert)
  thus ?case by simp
next
  case (ConsIneq M X F S)
  hence *: "\<lbrakk>M; S \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>d \<theta>" and
        ***: "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> set X = {}" 
    unfolding bvars\<^sub>s\<^sub>t_def ineq_model_def by auto
  have **: "ineq_model (\<delta> \<circ>\<^sub>s \<theta>) X F"
    using ConsIneq by (auto simp add: subst_compose_assoc ineq_model_def)
  have "\<forall>\<gamma>. subst_domain \<gamma> = set X \<and> ground (subst_range \<gamma>)
          \<longrightarrow> (subst_domain \<delta> \<union> range_vars \<delta>) \<inter> (subst_domain \<gamma> \<union> range_vars \<gamma>) = {}"
    using * ** *** unfolding range_vars_alt_def by auto
  hence "\<forall>\<gamma>. subst_domain \<gamma> = set X \<and> ground (subst_range \<gamma>) \<longrightarrow> \<gamma> \<circ>\<^sub>s \<delta> = \<delta> \<circ>\<^sub>s \<gamma>"
    by (metis subst_comp_eq_if_disjoint_vars)
  hence "ineq_model \<theta> X (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>)"
    using ineq_model_subst[OF *** **]
    by blast
  moreover have "rm_vars (set X) \<delta> = \<delta>" using ConsIneq.prems(2) by force
  ultimately show ?case using * by auto
next
  case ConsEq thus ?case unfolding bvars\<^sub>s\<^sub>t_def by auto
qed simp_all

private lemma strand_sem_subst_d':
  assumes "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> bvars\<^sub>s\<^sub>t S = {}"
  shows "\<lbrakk>M; S \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>d \<theta> \<Longrightarrow> \<lbrakk>M; S\<rbrakk>\<^sub>d (\<delta> \<circ>\<^sub>s \<theta>)"
using assms
proof (induction S arbitrary: \<delta> M rule: strand_sem_induct)
  case (ConsSnd M t S)
  hence "\<lbrakk>M; [Send t] \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>d \<theta>" "\<lbrakk>M; S \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>d \<theta>" by auto
  hence "\<lbrakk>M; S\<rbrakk>\<^sub>d (\<delta> \<circ>\<^sub>s \<theta>)" using ConsSnd.IH[OF _] ConsSnd.prems(2) by auto
  moreover have "\<lbrakk>M; [Send t]\<rbrakk>\<^sub>d (\<delta> \<circ>\<^sub>s \<theta>)"
  proof -
    have "M \<turnstile> t \<cdot> \<delta> \<cdot> \<theta>" using \<open>\<lbrakk>M; [Send t] \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>d \<theta>\<close> by auto
    hence "M \<turnstile> t \<cdot> (\<delta> \<circ>\<^sub>s \<theta>)" using subst_subst_compose by metis
    thus "\<lbrakk>M; [Send t]\<rbrakk>\<^sub>d (\<delta> \<circ>\<^sub>s \<theta>)" by auto
  qed
  ultimately show ?case by auto
next
  case (ConsRcv M t S)
  hence "\<lbrakk>insert (t \<cdot> \<delta> \<cdot> \<theta>) M; S \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>d \<theta>" by (simp add: subst_all_insert)
  thus ?case using ConsRcv.IH ConsRcv.prems(2) by auto
next
  case (ConsIneq M X F S)
  have \<delta>: "rm_vars (set X) \<delta> = \<delta>" using ConsIneq.prems(2) by force
  hence *: "\<lbrakk>M; S\<rbrakk>\<^sub>d (\<delta> \<circ>\<^sub>s \<theta>)"
    and ***: "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> set X = {}"
    using ConsIneq unfolding bvars\<^sub>s\<^sub>t_def ineq_model_def by auto
  have **: "ineq_model \<theta> X (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>)"
    using ConsIneq.prems(1) \<delta> by (auto simp add: subst_compose_assoc ineq_model_def)
  have "\<forall>\<gamma>. subst_domain \<gamma> = set X \<and> ground (subst_range \<gamma>)
          \<longrightarrow> (subst_domain \<delta> \<union> range_vars \<delta>) \<inter> (subst_domain \<gamma> \<union> range_vars \<gamma>) = {}"
    using * ** *** unfolding range_vars_alt_def by auto
  hence "\<forall>\<gamma>. subst_domain \<gamma> = set X \<and> ground (subst_range \<gamma>) \<longrightarrow> \<gamma> \<circ>\<^sub>s \<delta> = \<delta> \<circ>\<^sub>s \<gamma>"
    by (metis subst_comp_eq_if_disjoint_vars)
  hence "ineq_model (\<delta> \<circ>\<^sub>s \<theta>) X F"
    using ineq_model_subst'[OF *** **]
    by blast
  thus ?case using * by auto
next
  case ConsEq thus ?case unfolding bvars\<^sub>s\<^sub>t_def by auto
qed simp_all

lemmas strand_sem_subst =
  strand_sem_subst_c strand_sem_subst_c' strand_sem_subst_d strand_sem_subst_d'
end

lemma strand_sem_subst_subst_idem:
  assumes \<delta>: "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> bvars\<^sub>s\<^sub>t S = {}"
  shows "\<lbrakk>\<lbrakk>M; S \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>c (\<delta> \<circ>\<^sub>s \<theta>); subst_idem \<delta>\<rbrakk> \<Longrightarrow> \<lbrakk>M; S\<rbrakk>\<^sub>c (\<delta> \<circ>\<^sub>s \<theta>)"
using strand_sem_subst(2)[OF assms, of M "\<delta> \<circ>\<^sub>s \<theta>"] subst_compose_assoc[of \<delta> \<delta> \<theta>]
unfolding subst_idem_def by argo

lemma strand_sem_subst_comp:
  assumes "(subst_domain \<theta> \<union> range_vars \<theta>) \<inter> bvars\<^sub>s\<^sub>t S = {}"
    and "\<lbrakk>M; S\<rbrakk>\<^sub>c \<delta>" "subst_domain \<theta> \<inter> (vars\<^sub>s\<^sub>t S \<union> fv\<^sub>s\<^sub>e\<^sub>t M) = {}"
  shows "\<lbrakk>M; S\<rbrakk>\<^sub>c (\<theta> \<circ>\<^sub>s \<delta>)"
proof -
  from assms(3) have "subst_domain \<theta> \<inter> vars\<^sub>s\<^sub>t S = {}" "subst_domain \<theta> \<inter> fv\<^sub>s\<^sub>e\<^sub>t M = {}" by auto
  hence "S \<cdot>\<^sub>s\<^sub>t \<theta> = S" "M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta> = M" using strand_substI set_subst_ident[of M \<theta>] by (blast, blast)
  thus ?thesis using assms(2) by (auto simp add: strand_sem_subst(2)[OF assms(1)])
qed

lemma strand_sem_c_imp_ineqs_neq:
  assumes "\<lbrakk>M; S\<rbrakk>\<^sub>c \<I>" "Inequality X [(t,t')] \<in> set S"
  shows "t \<noteq> t' \<and> (\<forall>\<delta>. subst_domain \<delta> = set X \<and> ground (subst_range \<delta>)
                        \<longrightarrow> t \<cdot> \<delta> \<noteq> t' \<cdot> \<delta> \<and> t \<cdot> \<delta> \<cdot> \<I> \<noteq> t' \<cdot> \<delta> \<cdot> \<I>)"
using assms
proof (induction rule: strand_sem_induct)
  case (ConsIneq M Y F S) thus ?case
  proof (cases "Inequality X [(t,t')] \<in> set S")
    case False
    hence "X = Y" "F = [(t,t')]" using ConsIneq by auto
    hence *: "\<forall>\<theta>. subst_domain \<theta> = set X \<and> ground (subst_range \<theta>) \<longrightarrow> t \<cdot> \<theta> \<cdot> \<I> \<noteq> t' \<cdot> \<theta> \<cdot> \<I>"
      using ConsIneq by (auto simp add: ineq_model_def)
    then obtain \<theta> where \<theta>: "subst_domain \<theta> = set X" "ground (subst_range \<theta>)" "t \<cdot> \<theta> \<cdot> \<I> \<noteq> t' \<cdot> \<theta> \<cdot> \<I>"
      using interpretation_subst_exists'[of "set X"] by moura
    hence "t \<noteq> t'" by auto
    moreover have "\<And>\<I> \<theta>. t \<cdot> \<theta> \<cdot> \<I> \<noteq> t' \<cdot> \<theta> \<cdot> \<I> \<Longrightarrow> t \<cdot> \<theta> \<noteq> t' \<cdot> \<theta>" by auto
    ultimately show ?thesis using * by auto
  qed simp
qed simp_all

lemma strand_sem_c_imp_ineq_model:
  assumes "\<lbrakk>M; S\<rbrakk>\<^sub>c \<I>" "Inequality X F \<in> set S"
  shows "ineq_model \<I> X F"
using assms by (induct S rule: strand_sem_induct) force+

lemma strand_sem_wf_simple_fv_sat:
  assumes "wf\<^sub>s\<^sub>t {} S" "simple S" "\<lbrakk>{}; S\<rbrakk>\<^sub>c \<I>"
  shows "\<And>v. v \<in> wfrestrictedvars\<^sub>s\<^sub>t S \<Longrightarrow> ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c \<I> v"
using assms
proof (induction S rule: wf\<^sub>s\<^sub>t_simple_induct)
  case (ConsRcv t S)
  have "v \<in> wfrestrictedvars\<^sub>s\<^sub>t S"
    using ConsRcv.hyps(3) ConsRcv.prems(1) vars_snd_rcv_strand2
    by fastforce
  moreover have "\<lbrakk>{}; S\<rbrakk>\<^sub>c \<I>" using \<open>\<lbrakk>{}; S@[Receive t]\<rbrakk>\<^sub>c \<I>\<close> by blast
  moreover have "ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> ik\<^sub>s\<^sub>t (S@[Receive t]) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" by auto
  ultimately show ?case using ConsRcv.IH ideduct_synth_mono by meson
next
  case (ConsIneq X F S)
  hence "v \<in> wfrestrictedvars\<^sub>s\<^sub>t S" by fastforce
  moreover have "\<lbrakk>{}; S\<rbrakk>\<^sub>c \<I>" using \<open>\<lbrakk>{}; S@[Inequality X F]\<rbrakk>\<^sub>c \<I>\<close> by blast
  moreover have "ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> ik\<^sub>s\<^sub>t (S@[Inequality X F]) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" by auto
  ultimately show ?case using ConsIneq.IH ideduct_synth_mono by meson
next
  case (ConsSnd w S)
  hence *: "\<lbrakk>{}; S\<rbrakk>\<^sub>c \<I>" "ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c \<I> w" by auto
  have **: "ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> ik\<^sub>s\<^sub>t (S@[Send (Var w)]) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" by simp
  show ?case
  proof (cases "v = w")
    case True thus ?thesis using *(2) ideduct_synth_mono[OF _ **] by meson
  next
    case False
    hence "v \<in> wfrestrictedvars\<^sub>s\<^sub>t S" using ConsSnd.prems(1) by auto
    thus ?thesis using ConsSnd.IH[OF _ *(1)] ideduct_synth_mono[OF _ **] by metis
  qed
qed simp

lemma strand_sem_wf_ik_or_assignment_rhs_fun_subterm:
  assumes "wf\<^sub>s\<^sub>t {} A" "\<lbrakk>{}; A\<rbrakk>\<^sub>c \<I>" "Var x \<in> ik\<^sub>s\<^sub>t A" "\<I> x = Fun f T"
          "t\<^sub>i \<in> set T" "\<not>ik\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c t\<^sub>i" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
  obtains S where
    "Fun f S \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>s\<^sub>t A) \<or> Fun f S \<in> subterms\<^sub>s\<^sub>e\<^sub>t (assignment_rhs\<^sub>s\<^sub>t A)"
    "Fun f T = Fun f S \<cdot> \<I>"
proof -
  have "x \<in> wfrestrictedvars\<^sub>s\<^sub>t A"
    by (metis (no_types) assms(3) set_rev_mp term.set_intros(3) vars_subset_if_in_strand_ik2)
  moreover have "Fun f T \<cdot> \<I> = Fun f T"
    by (metis subst_ground_ident interpretation_grounds_all assms(4,7))
  ultimately obtain A\<^sub>p\<^sub>r\<^sub>e A\<^sub>s\<^sub>u\<^sub>f where *:
      "\<not>(\<exists>w \<in> wfrestrictedvars\<^sub>s\<^sub>t A\<^sub>p\<^sub>r\<^sub>e. Fun f T \<sqsubseteq> \<I> w)"
      "(\<exists>t. A = A\<^sub>p\<^sub>r\<^sub>e@Send t#A\<^sub>s\<^sub>u\<^sub>f \<and> Fun f T \<sqsubseteq> t \<cdot> \<I>) \<or>
       (\<exists>t t'. A = A\<^sub>p\<^sub>r\<^sub>e@Equality Assign t t'#A\<^sub>s\<^sub>u\<^sub>f \<and> Fun f T \<sqsubseteq> t \<cdot> \<I>)"
    using wf_strand_first_Send_var_split[OF assms(1)] assms(4) subtermeqI' by metis
  moreover
  { fix t assume **: "A = A\<^sub>p\<^sub>r\<^sub>e@Send t#A\<^sub>s\<^sub>u\<^sub>f" "Fun f T \<sqsubseteq> t \<cdot> \<I>"
    hence "ik\<^sub>s\<^sub>t A\<^sub>p\<^sub>r\<^sub>e \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c t \<cdot> \<I>" "\<not>ik\<^sub>s\<^sub>t A\<^sub>p\<^sub>r\<^sub>e \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c t\<^sub>i"
      using assms(2,6) by (auto intro: ideduct_synth_mono)
    then obtain s where s: "s \<in> ik\<^sub>s\<^sub>t A\<^sub>p\<^sub>r\<^sub>e" "Fun f T \<sqsubseteq> s \<cdot> \<I>"
      using assms(5) **(2) by (induct rule: intruder_synth_induct) auto
    then obtain g S where gS: "Fun g S \<sqsubseteq> s" "Fun f T = Fun g S \<cdot> \<I>"
      using subterm_subst_not_img_subterm[OF s(2)] *(1) by force
    hence ?thesis using that **(1) s(1) by force
  }
  moreover
  { fix t t' assume **: "A = A\<^sub>p\<^sub>r\<^sub>e@Equality Assign t t'#A\<^sub>s\<^sub>u\<^sub>f" "Fun f T \<sqsubseteq> t \<cdot> \<I>"
    with assms(2) have "t \<cdot> \<I> = t' \<cdot> \<I>" by auto
    hence "Fun f T \<sqsubseteq> t' \<cdot> \<I>" using **(2) by auto
    from assms(1) **(1) have "fv t' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t A\<^sub>p\<^sub>r\<^sub>e"
      using wf_eq_fv[of "{}" A\<^sub>p\<^sub>r\<^sub>e t t' A\<^sub>s\<^sub>u\<^sub>f] vars_snd_rcv_strand_subset2(4)[of A\<^sub>p\<^sub>r\<^sub>e]
      by blast
    then obtain g S where gS: "Fun g S \<sqsubseteq> t'" "Fun f T = Fun g S \<cdot> \<I>"
      using subterm_subst_not_img_subterm[OF \<open>Fun f T \<sqsubseteq> t' \<cdot> \<I>\<close>] *(1) by fastforce
    hence ?thesis using that **(1) by auto
  }
  ultimately show ?thesis by auto
qed

lemma strand_sem_not_unif_is_sat_ineq:
  assumes "\<nexists>\<theta>. Unifier \<theta> t t'"
  shows "\<lbrakk>M; [Inequality X [(t,t')]]\<rbrakk>\<^sub>c \<I>" "\<lbrakk>M; [Inequality X [(t,t')]]\<rbrakk>\<^sub>d \<I>"
using assms list_ex_simps(1)[of _ "(t,t')" "[]"] prod.sel[of t t']
      strand_sem_c.simps(1,5) strand_sem_d.simps(1,5)
unfolding ineq_model_def by presburger+

lemma ineq_model_singleI[intro]:
  assumes "\<forall>\<delta>. subst_domain \<delta> = set X \<and> ground (subst_range \<delta>) \<longrightarrow> t \<cdot> \<delta> \<cdot> \<I> \<noteq> t' \<cdot> \<delta> \<cdot> \<I>"
  shows "ineq_model \<I> X [(t,t')]"
using assms unfolding ineq_model_def by auto

lemma ineq_model_singleE:
  assumes "ineq_model \<I> X [(t,t')]"
  shows "\<forall>\<delta>. subst_domain \<delta> = set X \<and> ground (subst_range \<delta>) \<longrightarrow> t \<cdot> \<delta> \<cdot> \<I> \<noteq> t' \<cdot> \<delta> \<cdot> \<I>"
using assms unfolding ineq_model_def by auto

lemma ineq_model_single_iff:
  fixes F::"(('a,'b) term \<times> ('a,'b) term) list"
  shows "ineq_model \<I> X F \<longleftrightarrow>
         ineq_model \<I> X [(Fun f (Fun c []#map fst F),Fun f (Fun c []#map snd F))]"
    (is "?A \<longleftrightarrow> ?B")
proof -
  let ?P = "\<lambda>\<delta> f. fst f \<cdot> (\<delta> \<circ>\<^sub>s \<I>) \<noteq> snd f \<cdot> (\<delta> \<circ>\<^sub>s \<I>)"
  let ?Q = "\<lambda>\<delta> t t'. t \<cdot> (\<delta> \<circ>\<^sub>s \<I>) \<noteq> t' \<cdot> (\<delta> \<circ>\<^sub>s \<I>)"
  let ?T = "\<lambda>g. Fun c []#map g F"
  let ?S = "\<lambda>\<delta> g. map (\<lambda>x. x \<cdot> (\<delta> \<circ>\<^sub>s \<I>)) (Fun c []#map g F)"
  let ?t = "Fun f (?T fst)"
  let ?t' = "Fun f (?T snd)"

  have len: "\<And>g h. length (?T g) = length (?T h)"
            "\<And>g h \<delta>. length (?S \<delta> g) = length (?T h)"
            "\<And>g h \<delta>. length (?S \<delta> g) = length (?T h)"
            "\<And>g h \<delta> \<sigma>. length (?S \<delta> g) = length (?S \<sigma> h)"
    by simp_all

  { fix \<delta>::"('a,'b) subst"
    assume \<delta>: "subst_domain \<delta> = set X" "ground (subst_range \<delta>)"
    have "list_ex (?P \<delta>) F \<longleftrightarrow> ?Q \<delta> ?t ?t'"
    proof
      assume "list_ex (?P \<delta>) F"
      then obtain a where a: "a \<in> set F" "?P \<delta> a" by (metis (mono_tags, lifting) Bex_set)
      thus "?Q \<delta> ?t ?t'" by auto
    qed (fastforce simp add: Bex_set)
  } thus ?thesis unfolding ineq_model_def by auto
qed


subsection \<open>Constraint Semantics (Alternative, Equivalent Version)\<close>
text \<open>These are the constraint semantics used in the CSF 2017 paper\<close>
fun strand_sem_c'::"('fun,'var) terms \<Rightarrow> ('fun,'var) strand \<Rightarrow> ('fun,'var) subst \<Rightarrow> bool"  ("\<lbrakk>_; _\<rbrakk>\<^sub>c''") 
  where
  "\<lbrakk>M; []\<rbrakk>\<^sub>c' = (\<lambda>\<I>. True)"
| "\<lbrakk>M; Send t#S\<rbrakk>\<^sub>c' = (\<lambda>\<I>. M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c t \<cdot> \<I> \<and> \<lbrakk>M; S\<rbrakk>\<^sub>c' \<I>)"
| "\<lbrakk>M; Receive t#S\<rbrakk>\<^sub>c' = \<lbrakk>insert t M; S\<rbrakk>\<^sub>c'"
| "\<lbrakk>M; Equality _ t t'#S\<rbrakk>\<^sub>c' = (\<lambda>\<I>. t \<cdot> \<I> = t' \<cdot> \<I> \<and> \<lbrakk>M; S\<rbrakk>\<^sub>c' \<I>)"
| "\<lbrakk>M; Inequality X F#S\<rbrakk>\<^sub>c' = (\<lambda>\<I>. ineq_model \<I> X F \<and> \<lbrakk>M; S\<rbrakk>\<^sub>c' \<I>)"

fun strand_sem_d'::"('fun,'var) terms \<Rightarrow> ('fun,'var) strand \<Rightarrow> ('fun,'var) subst \<Rightarrow> bool" ("\<lbrakk>_; _\<rbrakk>\<^sub>d''")
where
  "\<lbrakk>M; []\<rbrakk>\<^sub>d' = (\<lambda>\<I>. True)"
| "\<lbrakk>M; Send t#S\<rbrakk>\<^sub>d' = (\<lambda>\<I>. M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<I> \<and> \<lbrakk>M; S\<rbrakk>\<^sub>d' \<I>)"
| "\<lbrakk>M; Receive t#S\<rbrakk>\<^sub>d' = \<lbrakk>insert t M; S\<rbrakk>\<^sub>d'"
| "\<lbrakk>M; Equality _ t t'#S\<rbrakk>\<^sub>d' = (\<lambda>\<I>. t \<cdot> \<I> = t' \<cdot> \<I> \<and> \<lbrakk>M; S\<rbrakk>\<^sub>d' \<I>)"
| "\<lbrakk>M; Inequality X F#S\<rbrakk>\<^sub>d' = (\<lambda>\<I>. ineq_model \<I> X F \<and> \<lbrakk>M; S\<rbrakk>\<^sub>d' \<I>)"

lemma strand_sem_eq_defs:
  "\<lbrakk>M; \<A>\<rbrakk>\<^sub>c' \<I> = \<lbrakk>M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>; \<A>\<rbrakk>\<^sub>c \<I>"
  "\<lbrakk>M; \<A>\<rbrakk>\<^sub>d' \<I> = \<lbrakk>M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>; \<A>\<rbrakk>\<^sub>d \<I>"
proof -
  have 1: "\<lbrakk>M; \<A>\<rbrakk>\<^sub>c' \<I> \<Longrightarrow> \<lbrakk>M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>; \<A>\<rbrakk>\<^sub>c \<I>"
    by (induct \<A> arbitrary: M rule: strand_sem_induct) force+
  have 2: "\<lbrakk>M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>; \<A>\<rbrakk>\<^sub>c \<I> \<Longrightarrow> \<lbrakk>M; \<A>\<rbrakk>\<^sub>c' \<I>"
    by (induct \<A> arbitrary: M rule: strand_sem_c'.induct) auto
  have 3: "\<lbrakk>M; \<A>\<rbrakk>\<^sub>d' \<I> \<Longrightarrow> \<lbrakk>M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>; \<A>\<rbrakk>\<^sub>d \<I>"
    by (induct \<A> arbitrary: M rule: strand_sem_induct) force+
  have 4: "\<lbrakk>M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>; \<A>\<rbrakk>\<^sub>d \<I> \<Longrightarrow> \<lbrakk>M; \<A>\<rbrakk>\<^sub>d' \<I>"
    by (induct \<A> arbitrary: M rule: strand_sem_d'.induct) auto

  show "\<lbrakk>M; \<A>\<rbrakk>\<^sub>c' \<I> = \<lbrakk>M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>; \<A>\<rbrakk>\<^sub>c \<I>" "\<lbrakk>M; \<A>\<rbrakk>\<^sub>d' \<I> = \<lbrakk>M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>; \<A>\<rbrakk>\<^sub>d \<I>"
    by (metis 1 2, metis 3 4)
qed

lemma strand_sem_split'[dest]:
  "\<lbrakk>M; S@S'\<rbrakk>\<^sub>c' \<theta> \<Longrightarrow> \<lbrakk>M; S\<rbrakk>\<^sub>c' \<theta>" 
  "\<lbrakk>M; S@S'\<rbrakk>\<^sub>c' \<theta> \<Longrightarrow> \<lbrakk>M \<union> ik\<^sub>s\<^sub>t S; S'\<rbrakk>\<^sub>c' \<theta>"
  "\<lbrakk>M; S@S'\<rbrakk>\<^sub>d' \<theta> \<Longrightarrow> \<lbrakk>M; S\<rbrakk>\<^sub>d' \<theta>"
  "\<lbrakk>M; S@S'\<rbrakk>\<^sub>d' \<theta> \<Longrightarrow> \<lbrakk>M \<union> ik\<^sub>s\<^sub>t S; S'\<rbrakk>\<^sub>d' \<theta>"
using strand_sem_eq_defs[of M "S@S'" \<theta>]
      strand_sem_eq_defs[of M S \<theta>]
      strand_sem_eq_defs[of "M \<union> ik\<^sub>s\<^sub>t S" S' \<theta>]
      strand_sem_split(2,4)
by (auto simp add: image_Un)

lemma strand_sem_append'[intro]:
  "\<lbrakk>M; S\<rbrakk>\<^sub>c' \<theta> \<Longrightarrow> \<lbrakk>M \<union> ik\<^sub>s\<^sub>t S; S'\<rbrakk>\<^sub>c' \<theta> \<Longrightarrow> \<lbrakk>M; S@S'\<rbrakk>\<^sub>c' \<theta>"
  "\<lbrakk>M; S\<rbrakk>\<^sub>d' \<theta> \<Longrightarrow> \<lbrakk>M \<union> ik\<^sub>s\<^sub>t S; S'\<rbrakk>\<^sub>d' \<theta> \<Longrightarrow> \<lbrakk>M; S@S'\<rbrakk>\<^sub>d' \<theta>"
using strand_sem_eq_defs[of M "S@S'" \<theta>]
      strand_sem_eq_defs[of M S \<theta>]
      strand_sem_eq_defs[of "M \<union> ik\<^sub>s\<^sub>t S" S' \<theta>]
by (auto simp add: image_Un)

end

subsection \<open>Dual Strands\<close>
fun dual\<^sub>s\<^sub>t::"('a,'b) strand \<Rightarrow> ('a,'b) strand" where
  "dual\<^sub>s\<^sub>t [] = []"
| "dual\<^sub>s\<^sub>t (Receive t#S) = Send t#(dual\<^sub>s\<^sub>t S)"
| "dual\<^sub>s\<^sub>t (Send t#S) = Receive t#(dual\<^sub>s\<^sub>t S)"
| "dual\<^sub>s\<^sub>t (x#S) = x#(dual\<^sub>s\<^sub>t S)"

lemma dual\<^sub>s\<^sub>t_append: "dual\<^sub>s\<^sub>t (A@B) = (dual\<^sub>s\<^sub>t A)@(dual\<^sub>s\<^sub>t B)"
by (induct A rule: dual\<^sub>s\<^sub>t.induct) auto

lemma dual\<^sub>s\<^sub>t_self_inverse: "dual\<^sub>s\<^sub>t (dual\<^sub>s\<^sub>t S) = S"
proof (induction S)
  case (Cons x S) thus ?case by (cases x) auto
qed simp

lemma dual\<^sub>s\<^sub>t_trms_eq: "trms\<^sub>s\<^sub>t (dual\<^sub>s\<^sub>t S) = trms\<^sub>s\<^sub>t S"
proof (induction S)
  case (Cons x S) thus ?case by (cases x) auto
qed simp

lemma dual\<^sub>s\<^sub>t_fv: "fv\<^sub>s\<^sub>t (dual\<^sub>s\<^sub>t A) = fv\<^sub>s\<^sub>t A"
by (induct A rule: dual\<^sub>s\<^sub>t.induct) auto

lemma dual\<^sub>s\<^sub>t_bvars: "bvars\<^sub>s\<^sub>t (dual\<^sub>s\<^sub>t A) = bvars\<^sub>s\<^sub>t A"
by (induct A rule: dual\<^sub>s\<^sub>t.induct) fastforce+


end
