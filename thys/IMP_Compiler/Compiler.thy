(*  Title:       A Shorter Compiler Correctness Proof for Language IMP
    Author:      Pasquale Noce
                 Software Engineer at HID Global, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at hidglobal dot com
*)

section "Compiler formalization"

theory Compiler
  imports
    "HOL-IMP.BExp"
    "HOL-IMP.Star"
begin


subsection "Introduction"

text \<open>
This paper presents a compiler correctness proof for the didactic imperative programming language
IMP, introduced in @{cite "Nipkow14"}, shorter than the proof described in @{cite "Nipkow14"} and
included in the Isabelle2021 distribution @{cite "Klein21"}. Actually, the size of the presented
proof is just two thirds of the book's proof in the number of formal text lines, and as such it
promises to constitute a further enhanced reference for the formal verification of compilers meant
for larger, real-world programming languages.

Given compiler \emph{completeness}, viz. the simulation of source code execution by compiled code,
"in a deterministic language like IMP", compiler correctness "reduces to preserving termination: if
the machine program terminates, so must the source program", even though proving this "is not much
easier" (@{cite "Nipkow14"}, section 8.4). However, the presented proof does not depend on language
determinism, so that the proposed approach is applicable to non-deterministic languages as well.

As a confirmation, this paper extends IMP with an additional command @{text "c\<^sub>1 OR c\<^sub>2"}, standing
for the non-deterministic choice between commands @{text c\<^sub>1} and @{text c\<^sub>2}, and proves compiler
\emph{correctness}, viz. the simulation of compiled code execution by source code, for such extended
language. Of course, the aforesaid comparison between proof sizes does not consider the lines in the
proof of lemma @{text ccomp_correct} (which proves compiler correctness for commands) pertaining to
non-deterministic choice, since this command is not included in the original language IMP. Anyway,
non-deterministic choice turns out to extend that proof just by a modest number of lines.

For further information about the formal definitions and proofs contained in this paper, see
Isabelle documentation, particularly @{cite "Paulson21"}, @{cite "Nipkow21"}, @{cite "Krauss21"},
and @{cite "Nipkow11"}.
\<close>


subsection "Definitions"

text \<open>
Here below are the definitions of IMP commands, extended with non-deterministic choice, as well as
of their big-step semantics.

As in the original theory file @{cite "Klein21"}, program counter's values are modeled using type
@{typ int} rather than @{typ nat}. As a result, the same declarations and definitions used in
@{cite "Klein21"} to deal with this modeling choice are adopted here as well.

\null
\<close>

declare [[coercion_enabled]]
declare [[coercion "int :: nat \<Rightarrow> int"]]
declare [[syntax_ambiguity_warning = false]]

datatype com =
  SKIP |
  Assign vname aexp  ("_ ::= _" [1000, 61] 61) |
  Seq com com  ("_;;/ _" [60, 61] 60) |
  If bexp com com  ("(IF _/ THEN _/ ELSE _)" [0, 0, 61] 61) |
  Or com com  ("(_ OR _)" [60, 61] 61) |
  While bexp com  ("(WHILE _/ DO _)" [0, 61] 61)

inductive big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55) where
Skip:  "(SKIP, s) \<Rightarrow> s" |
Assign:  "(x ::= a, s) \<Rightarrow> s(x := aval a s)" |
Seq:  "\<lbrakk>(c\<^sub>1, s\<^sub>1) \<Rightarrow> s\<^sub>2; (c\<^sub>2, s\<^sub>2) \<Rightarrow> s\<^sub>3\<rbrakk> \<Longrightarrow> (c\<^sub>1;; c\<^sub>2, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
IfTrue:  "\<lbrakk>bval b s; (c\<^sub>1, s) \<Rightarrow> t\<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
IfFalse:  "\<lbrakk>\<not> bval b s; (c\<^sub>2, s) \<Rightarrow> t\<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
Or1:  "(c\<^sub>1, s) \<Rightarrow> t \<Longrightarrow> (c\<^sub>1 OR c\<^sub>2, s) \<Rightarrow> t" |
Or2:  "(c\<^sub>2, s) \<Rightarrow> t \<Longrightarrow> (c\<^sub>1 OR c\<^sub>2, s) \<Rightarrow> t" |
WhileFalse:  "\<not> bval b s \<Longrightarrow> (WHILE b DO c, s) \<Rightarrow> s" |
WhileTrue:  "\<lbrakk>bval b s\<^sub>1; (c, s\<^sub>1) \<Rightarrow> s\<^sub>2; (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3\<rbrakk> \<Longrightarrow>
  (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3"

declare big_step.intros [intro]

abbreviation (output)
"isize xs \<equiv> int (length xs)"

notation isize ("size")

primrec (nonexhaustive) inth :: "'a list \<Rightarrow> int \<Rightarrow> 'a" (infixl "!!" 100) where
"(x # xs) !! i = (if i = 0 then x else xs !! (i - 1))"

lemma inth_append [simp]:
 "0 \<le> i \<Longrightarrow>
    (xs @ ys) !! i = (if i < size xs then xs !! i else ys !! (i - size xs))"
by (induction xs arbitrary: i, auto simp: algebra_simps)

text \<open>
\null

Next, the instruction set and its semantics are defined. Particularly, to allow for the compilation
of non-deterministic choice commands, the instruction set is extended with an additional instruction
@{text JMPND} performing a non-deterministic jump -- viz. as a result of its execution, the program
counter unconditionally either jumps by the specified offset, or just moves to the next instruction.

As instruction execution can be non-deterministic, an inductively defined predicate @{text iexec},
rather than a simple non-recursive function as the one used in @{cite "Klein21"}, must be introduced
to define instruction semantics.

\null
\<close>

datatype instr = 
  LOADI int | LOAD vname | ADD | STORE vname |
  JMP int | JMPLESS int | JMPGE int | JMPND int

type_synonym stack = "val list"
type_synonym config = "int \<times> state \<times> stack"

abbreviation "hd2 xs \<equiv> hd (tl xs)"
abbreviation "tl2 xs \<equiv> tl (tl xs)"

inductive iexec :: "instr \<times> config \<Rightarrow> config \<Rightarrow> bool" (infix "\<mapsto>" 55) where
LoadI:  "(LOADI i, pc, s, stk) \<mapsto> (pc + 1, s, i # stk)" |
Load:  "(LOAD x, pc, s, stk) \<mapsto> (pc + 1, s, s x # stk)" |
Add:  "(ADD, pc, s, stk) \<mapsto> (pc + 1, s, (hd2 stk + hd stk) # tl2 stk)" |
Store:  "(STORE x, pc, s, stk) \<mapsto> (pc + 1, s(x := hd stk), tl stk)" |
Jmp:  "(JMP i, pc, s, stk) \<mapsto> (pc + i + 1, s, stk)" |
JmpLessY:  "hd2 stk < hd stk \<Longrightarrow>
  (JMPLESS i, pc, s, stk) \<mapsto> (pc + i + 1, s, tl2 stk)" |
JmpLessN:  "hd stk \<le> hd2 stk \<Longrightarrow>
  (JMPLESS i, pc, s, stk) \<mapsto> (pc + 1, s, tl2 stk)" |
JmpGeY:  "hd stk \<le> hd2 stk \<Longrightarrow>
  (JMPGE i, pc, s, stk) \<mapsto> (pc + i + 1, s, tl2 stk)" |
JmpGeN:  "hd2 stk < hd stk \<Longrightarrow>
  (JMPGE i, pc, s, stk) \<mapsto> (pc + 1, s, tl2 stk)" |
JmpNdY:  "(JMPND i, pc, s, stk) \<mapsto> (pc + i + 1, s, stk)" |
JmpNdN:  "(JMPND i, pc, s, stk) \<mapsto> (pc + 1, s, stk)"

declare iexec.intros [intro]

inductive_cases LoadIE  [elim!]:  "(LOADI i, pc, s, stk) \<mapsto> cf"
inductive_cases LoadE  [elim!]:  "(LOAD x, pc, s, stk) \<mapsto> cf"
inductive_cases AddE  [elim!]:  "(ADD, pc, s, stk) \<mapsto> cf"
inductive_cases StoreE  [elim!]:  "(STORE x, pc, s, stk) \<mapsto> cf"
inductive_cases JmpE  [elim!]:  "(JMP i, pc, s, stk) \<mapsto> cf"
inductive_cases JmpLessE  [elim!]:  "(JMPLESS i, pc, s, stk) \<mapsto> cf"
inductive_cases JmpGeE  [elim!]:  "(JMPGE i, pc, s, stk) \<mapsto> cf"
inductive_cases JmpNdE  [elim!]:  "(JMPND i, pc, s, stk) \<mapsto> cf"

definition exec1 :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool"
  ("(_/ \<turnstile>/ _/ \<rightarrow>/ _)" 55) where
"P \<turnstile> cf \<rightarrow> cf' \<equiv> (P !! fst cf, cf) \<mapsto> cf' \<and> 0 \<le> fst cf \<and> fst cf < size P"

abbreviation exec :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool"
  ("(_/ \<turnstile>/ _/ \<rightarrow>*/ _)" 55) where
"exec P \<equiv> star (exec1 P)"

text \<open>
\null

Next, compilation is formalized for arithmetic and boolean expressions (functions @{text acomp} and
@{text bcomp}), as well as for commands (function @{text ccomp}). Particularly, as opposed to what
happens in @{cite "Klein21"}, here @{text bcomp} takes a single input, viz. a 3-tuple comprised of
a boolean expression, a flag, and a jump offset. In this way, all three functions accept a single
input, which enables to streamline the compiler correctness proof developed in what follows.

\null
\<close>

primrec acomp :: "aexp \<Rightarrow> instr list" where
"acomp (N i) = [LOADI i]" |
"acomp (V x) = [LOAD x]" |
"acomp (Plus a\<^sub>1 a\<^sub>2) = acomp a\<^sub>1 @ acomp a\<^sub>2 @ [ADD]"

fun bcomp :: "bexp \<times> bool \<times> int \<Rightarrow> instr list" where
"bcomp (Bc v, f, i) = (if v = f then [JMP i] else [])" |
"bcomp (Not b, f, i) = bcomp (b, \<not> f, i)" |
"bcomp (And b\<^sub>1 b\<^sub>2, f, i) =
  (let cb\<^sub>2 = bcomp (b\<^sub>2, f, i);
     cb\<^sub>1 = bcomp (b\<^sub>1, False, size cb\<^sub>2 + (if f then 0 else i))
   in cb\<^sub>1 @ cb\<^sub>2)" |
"bcomp (Less a\<^sub>1 a\<^sub>2, f, i) =
  acomp a\<^sub>1 @ acomp a\<^sub>2 @ (if f then [JMPLESS i] else [JMPGE i])"

primrec ccomp :: "com \<Rightarrow> instr list" where
"ccomp SKIP = []" |
"ccomp (x ::= a) = acomp a @ [STORE x]" |
"ccomp (c\<^sub>1;; c\<^sub>2) = ccomp c\<^sub>1 @ ccomp c\<^sub>2" |
"ccomp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) =
  (let cc\<^sub>1 = ccomp c\<^sub>1; cc\<^sub>2 = ccomp c\<^sub>2; cb = bcomp (b, False, size cc\<^sub>1 + 1)
   in cb @ cc\<^sub>1 @ JMP (size cc\<^sub>2) # cc\<^sub>2)" |
"ccomp (c\<^sub>1 OR c\<^sub>2) =
  (let cc\<^sub>1 = ccomp c\<^sub>1; cc\<^sub>2 = ccomp c\<^sub>2
   in JMPND (size cc\<^sub>1 + 1) # cc\<^sub>1 @ JMP (size cc\<^sub>2) # cc\<^sub>2)" |
"ccomp (WHILE b DO c) =
  (let cc = ccomp c; cb = bcomp (b, False, size cc + 1)
   in cb @ cc @ [JMP (- (size cb + size cc + 1))])"

text \<open>
\null

Finally, two lemmas are proven automatically (both seem not to be included in the standard library,
though being quite basic) and registered for use by automatic proof tactics. In more detail:

  \<^item> The former lemma is an elimination rule similar to @{thm [source] impCE}, with the difference
that it retains the antecedent of the implication in the premise where the consequent is assumed to
hold. This rule permits to have both assumptions @{prop "\<not> bval b s"} and @{prop "bval b s"} in the
respective cases resulting from the execution of boolean expression @{text b} in state @{text s}.

  \<^item> The latter one is an introduction rule similar to @{thm [source] Suc_lessI}, with the difference
that its second assumption is more convenient for proving statements of the form @{prop "Suc m < n"}
arising from the compiler correctness proof developed in what follows.

\null
\<close>

lemma impCE2 [elim!]:
 "\<lbrakk>P \<longrightarrow> Q; \<not> P \<Longrightarrow> R; P \<Longrightarrow> Q \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
by blast

lemma Suc_lessI2 [intro!]:
 "\<lbrakk>m < n; m \<noteq> n - 1\<rbrakk> \<Longrightarrow> Suc m < n"
by simp

end
