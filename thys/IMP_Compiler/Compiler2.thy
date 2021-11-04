(*  Title:       A Shorter Compiler Correctness Proof for Language IMP
    Author:      Pasquale Noce
                 Software Engineer at HID Global, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at hidglobal dot com
*)

section "Compiler correctness"

theory Compiler2
  imports Compiler
begin


subsection "Preliminary definitions and lemmas"

text \<open>
Now everything is ready for the compiler correctness proof. First, two predicates are introduced,
@{text execl} and @{text execl_all}, both taking as inputs a program, i.e. a list of instructions,
@{text P} and a list of program configurations @{text cfs}, and respectively denoted using notations
@{text "P \<Turnstile> cfs"} and @{text "P \<Turnstile> cfs\<box>"}. In more detail:

  \<^item> @{text "P \<Turnstile> cfs"} means that program @{text P} \emph{may} transform each configuration within
@{text cfs} into the subsequent one, if any (word \emph{may} reflects the fact that programs can be
non-deterministic in this case study).
\\Thus, @{text execl} formalizes the notion of a \emph{small-step} program execution.

  \<^item> @{text "P \<Turnstile> cfs\<box>"} reinforces @{text "P \<Turnstile> cfs"} by additionally requiring that @{text cfs} be
nonempty, the initial program counter be zero (viz. execution starts from the first instruction in
@{text P}), and the final program counter falls outside @{text P} (viz. execution terminates).
\\Thus, @{text execl_all} formalizes the notion of a \emph{complete small-step} program execution,
so that assumptions @{text "acomp a \<Turnstile> cfs\<box>"}, @{text "bcomp x \<Turnstile> cfs\<box>"}, @{text "ccomp c \<Turnstile> cfs\<box>"}
will be used in the compiler correctness proofs for arithmetic/boolean expressions and commands.

Moreover, predicates @{text apred}, @{text bpred}, and @{text cpred} are defined to capture the link
between the initial and the final configuration upon the execution of an arithmetic expression, a
boolean expression, and a whole program, respectively, and abbreviation @{text off} is introduced as
a commodity to shorten the subsequent formal text.

\null
\<close>

fun execl :: "instr list \<Rightarrow> config list \<Rightarrow> bool" (infix "\<Turnstile>" 55) where
"P \<Turnstile> cf # cf' # cfs = (P \<turnstile> cf \<rightarrow> cf' \<and> P \<Turnstile> cf' # cfs)" |
"P \<Turnstile> _ = True"

definition execl_all :: "instr list \<Rightarrow> config list \<Rightarrow> bool" ("(_/ \<Turnstile>/ _\<box>)" 55) where
"P \<Turnstile> cfs\<box> \<equiv> P \<Turnstile> cfs \<and> cfs \<noteq> [] \<and>
  fst (cfs ! 0) = 0 \<and> fst (cfs ! (length cfs - 1)) \<notin> {0..<size P}"

definition apred :: "aexp \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" where
"apred \<equiv> \<lambda>a (pc, s, stk) (pc', s', stk').
  pc' = pc + size (acomp a) \<and> s' = s \<and> stk' = aval a s # stk"

definition bpred :: "bexp \<times> bool \<times> int \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" where
"bpred \<equiv> \<lambda>(b, f, i) (pc, s, stk) (pc', s', stk').
  pc' = pc + size (bcomp (b, f, i)) + (if bval b s = f then i else 0) \<and>
    s' = s \<and> stk' = stk"

definition cpred :: "com \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" where
"cpred \<equiv> \<lambda>c (pc, s, stk) (pc', s', stk').
  pc' = pc + size (ccomp c) \<and> (c, s) \<Rightarrow> s' \<and> stk' = stk"

abbreviation off :: "instr list \<Rightarrow> config \<Rightarrow> config" where
"off P cf \<equiv> (fst cf - size P, snd cf)"

text \<open>
\null

Next, some lemmas about @{const [source] execl} and @{const execl_all} are proven. In more detail,
given a program @{text P} and a list of configurations @{text cfs} such that @{prop "P \<Turnstile> cfs"}:

  \<^item> Lemma @{text execl_next} states that for any configuration in @{text cfs} but the last one, the
subsequent configuration must result from the execution of the referenced instruction of @{text P}
in that configuration.
\\Thus, @{text execl_next} permits to reproduce the execution of a single instruction.

  \<^item> Lemma @{text execl_last} states that a configuration in @{text cfs} whose program counter falls
outside @{text P} must be the last one in @{text cfs}.
\\Thus, @{text execl_last} permits to infer the completion of program execution.

  \<^item> Lemma @{text execl_drop} states that @{prop "P \<Turnstile> drop n cfs"} for any natural number @{text n},
and will be used to prove compiler correctness for loops by induction over the length of the list of
configurations @{text cfs}.

Furthermore, some other lemmas enabling to prove compiler correctness automatically for constructors
@{const N}, @{const V} (arithmetic expressions), @{const Bc} (boolean expressions) and @{const SKIP}
(commands) are also proven.

\null
\<close>

lemma iexec_offset_aux:
 "(i :: int) + 1 - j = i - j + 1 \<and> i + j - k + 1 = i - k + j + 1"
by simp

lemma iexec_offset [intro]:
 "(ins, pc, s, stk) \<mapsto> (pc', s', stk') \<Longrightarrow>
    (ins, pc - i, s, stk) \<mapsto> (pc' - i, s', stk')"
by (erule iexec.cases, auto simp: iexec_offset_aux)

lemma execl_next:
 "\<lbrakk>P \<Turnstile> cfs; k < length cfs; k \<noteq> length cfs - 1\<rbrakk> \<Longrightarrow>
    (P !! fst (cfs ! k), cfs ! k) \<mapsto> cfs ! Suc k"
by (induction cfs arbitrary: k rule: execl.induct, auto
 simp: nth_Cons exec1_def split: nat.split)

lemma execl_last:
 "\<lbrakk>P \<Turnstile> cfs; k < length cfs; fst (cfs ! k) \<notin> {0..<size P}\<rbrakk> \<Longrightarrow>
    length cfs - 1 = k"
by (induction cfs arbitrary: k rule: execl.induct, auto
 simp: nth_Cons exec1_def split: nat.split_asm)

lemma execl_drop:
 "P \<Turnstile> cfs \<Longrightarrow> P \<Turnstile> drop n cfs"
by (induction cfs arbitrary: n rule: execl.induct,
 simp_all add: drop_Cons split: nat.split)

lemma execl_all_N [simplified, intro]:
 "[LOADI i] \<Turnstile> cfs\<box> \<Longrightarrow> apred (N i) (cfs ! 0) (cfs ! (length cfs - 1))"
by (clarsimp simp: execl_all_def apred_def, cases "cfs ! 0",
 subgoal_tac "length cfs - 1 = 1", frule_tac [!] execl_next,
 ((rule ccontr)?, fastforce, (rule execl_last)?)+)

lemma execl_all_V [simplified, intro]:
 "[LOAD x] \<Turnstile> cfs\<box> \<Longrightarrow> apred (V x) (cfs ! 0) (cfs ! (length cfs - 1))"
by (clarsimp simp: execl_all_def apred_def, cases "cfs ! 0",
 subgoal_tac "length cfs - 1 = 1", frule_tac [!] execl_next,
 ((rule ccontr)?, fastforce, (rule execl_last)?)+)

lemma execl_all_Bc [simplified, intro]:
 "\<lbrakk>if v = f then [JMP i] else [] \<Turnstile> cfs\<box>; 0 \<le> i\<rbrakk> \<Longrightarrow>
    bpred (Bc v, f, i) (cfs ! 0) (cfs ! (length cfs - 1))"
by (clarsimp simp: execl_all_def bpred_def split: if_split_asm, cases "cfs ! 0",
 subgoal_tac "length cfs - 1 = 1", frule_tac [1-2] execl_next,
 ((rule ccontr)?, force, (rule execl_last)?)+, rule execl.cases [of "([], cfs)"],
 auto simp: exec1_def)

lemma execl_all_SKIP [simplified, intro]:
 "[] \<Turnstile> cfs\<box> \<Longrightarrow> cpred SKIP (cfs ! 0) (cfs ! (length cfs - 1))"
by (rule execl.cases [of "([], cfs)"], auto simp: execl_all_def exec1_def cpred_def)

text \<open>
\null

Next, lemma @{text execl_all_sub} is proven. It states that, if @{prop "P @ P' x @ P'' \<Turnstile> cfs\<box>"},
configuration @{text cf} within @{text cfs} refers to the start of program @{text "P' x"}, and the
initial and the final configuration in every complete execution of @{text "P' x"} satisfy predicate
@{text "Q x"}, then there exists a configuration @{text cf'} in @{text cfs} such that @{text cf} and
@{text cf'} satisfy @{text "Q x"}.
\\Thus, this lemma permits to reproduce the execution of a subprogram, particularly:

  \<^item> a compiled arithmetic expression @{text a}, where @{prop "Q = apred"} and @{prop "x = a"},

  \<^item> a compiled boolean expression @{text b}, where @{prop "Q = bpred"} and @{prop "x = (b, f, i)"}
(given a flag @{text f} and a jump offset @{text i}), and

  \<^item> a compiled command @{text c}, where @{prop "Q = cpred"} and @{prop "x = c"}.

Furthermore, lemma @{text execl_all_sub2} is derived from @{text execl_all_sub} to enable a shorter
symbolical execution of two consecutive subprograms.

\null
\<close>

lemma execl_sub_aux:
 "\<lbrakk>\<And>m n. \<forall>k \<in> {m..<n}. Q P' (((pc, s, stk) # cfs) ! k) \<Longrightarrow> P' \<Turnstile>
    map (off P) (case m of 0 \<Rightarrow> (pc, s, stk) # take n cfs | Suc m \<Rightarrow> F cfs m n);
    \<forall>k \<in> {m..<n+m+length cfs'}. Q P' ((cfs' @ (pc, s, stk) # cfs) ! (k-m))\<rbrakk> \<Longrightarrow>
  P' \<Turnstile> (pc - size P, s, stk) # map (off P) (take n cfs)"
  (is "\<lbrakk>\<And>_ _. \<forall>k \<in> _. Q P' (?F k) \<Longrightarrow> _; \<forall>k \<in> ?A. Q P' (?G k)\<rbrakk> \<Longrightarrow> _")
by (subgoal_tac "\<forall>k \<in> {0..<n}. Q P' (?F k)", fastforce, subgoal_tac
 "\<forall>k \<in> {0..<n}. k + m + length cfs' \<in> ?A \<and> ?F k = ?G (k + m + length cfs')",
 fastforce, simp add: nth_append)

lemma execl_sub:
 "\<lbrakk>P @ P' @ P'' \<Turnstile> cfs; \<forall>k \<in> {m..<n}.
     size P \<le> fst (cfs ! k) \<and> fst (cfs ! k) - size P < size P'\<rbrakk> \<Longrightarrow>
   P' \<Turnstile> map (off P) (drop m (take (Suc n) cfs))"
  (is "\<lbrakk>_; \<forall>k \<in> _. ?P P' cfs k\<rbrakk> \<Longrightarrow> P' \<Turnstile> map _ (?F cfs m (Suc n))")
proof (induction cfs arbitrary: m n rule: execl.induct [of _ P'], auto
 simp: take_Cons drop_Cons exec1_def split: nat.split, force, force, force,
 erule execl_sub_aux [where m = 0], subst append_Cons [of _ "[]"], simp,
 erule execl_sub_aux [where m = "Suc 0" and cfs' = "[]"], simp)
  fix P' pc s stk cfs m n
  let ?cf = "(pc, s, stk) :: config"
  assume "\<And>m n. \<forall>k \<in> {m..<n}. ?P P' (?cf # cfs) k \<Longrightarrow> P' \<Turnstile>
    map (off P) (case m of 0 \<Rightarrow> ?cf # take n cfs | Suc m \<Rightarrow> ?F cfs m n)"
  moreover assume "\<forall>k \<in> {Suc (Suc m)..<Suc n}. ?P P' cfs (k - Suc (Suc 0))"
  hence "\<forall>k \<in> {Suc m..<n}. ?P P' (?cf # cfs) k"
    by force
  ultimately show "P' \<Turnstile> map (off P) (?F cfs m n)"
    by fastforce
qed

lemma execl_all_sub [rule_format]:
  assumes
    A: "P @ P' x @ P'' \<Turnstile> cfs\<box>" and
    B: "k < length cfs" and
    C: "fst (cfs ! k) = size P" and
    D: "\<forall>cfs. P' x \<Turnstile> cfs\<box> \<longrightarrow> Q x (cfs ! 0) (cfs ! (length cfs - 1))"
  shows "\<exists>k' < length cfs. Q x (off P (cfs ! k)) (off P (cfs ! k'))"
proof -
  let ?P = "\<lambda>k. size P \<le> fst (cfs ! k) \<and> fst (cfs ! k) - size P < size (P' x)"
  let ?A = "{k'. k' \<in> {k..<length cfs} \<and> \<not> ?P k'}"
  have E: "Min ?A \<in> ?A"
    using A and B by (rule_tac Min_in, simp_all add: execl_all_def,
     rule_tac exI [of _ "length cfs - 1"], auto)
  hence "map (off P) (drop k (take (Suc (Min ?A)) cfs)) ! 0 = off P (cfs ! k)"
    (is "?cfs ! _ = _")
    by auto
  moreover have "length cfs \<le> Suc (Min ?A) \<longrightarrow> Min ?A = length cfs - 1"
    using E by auto
  with A and B and E have F: "?cfs ! (length ?cfs - 1) = off P (cfs ! Min ?A)"
    by (subst nth_map, auto simp: min_def execl_all_def, arith)
  hence "?cfs \<noteq> [] \<and> fst (?cfs ! (length ?cfs - 1)) \<notin> {0..<size (P' x)}"
    using E by (auto simp: min_def)
  moreover have "\<not> (\<exists>k'. k' \<in> {k'. k' \<in> {k..<Min ?A} \<and> \<not> ?P k'})"
    by (rule notI, erule exE, frule rev_subsetD [of _ _ ?A], rule subsetI,
     insert E, simp, subgoal_tac "finite ?A", drule Min_le, force+)
  hence "P' x \<Turnstile> ?cfs"
    using A by (subst (asm) execl_all_def, rule_tac execl_sub, blast+)
  ultimately have "Q x (?cfs ! 0) (?cfs ! (length ?cfs - 1))"
    using C and D by (auto simp: execl_all_def)
  thus ?thesis
    using E and F by (rule_tac exI [of _ "Min ?A"], auto)
qed

lemma execl_all_sub2:
  assumes
    A: "P x @ P' x' @ P'' \<Turnstile> cfs\<box>"
      (is "?P \<Turnstile> _\<box>") and
    B: "\<And>cfs. P x \<Turnstile> cfs\<box> \<Longrightarrow> (\<lambda>(pc, s, stk) (pc', s', stk').
      pc' = pc + size (P x) + I s \<and> Q s s' \<and> stk' = F s stk)
        (cfs ! 0) (cfs ! (length cfs - 1))"
      (is "\<And>cfs. _ \<Longrightarrow> ?Q x (cfs ! 0) (cfs ! (length cfs - 1))") and
    C: "\<And>cfs. P' x' \<Turnstile> cfs\<box> \<Longrightarrow> (\<lambda>(pc, s, stk) (pc', s', stk').
      pc' = pc + size (P' x') + I' s \<and> Q' s s' \<and> stk' = F' s stk)
        (cfs ! 0) (cfs ! (length cfs - 1))"
      (is "\<And>cfs. _ \<Longrightarrow> ?Q' x' (cfs ! 0) (cfs ! (length cfs - 1))") and
    D: "I (fst (snd (cfs ! 0))) = 0"
  shows "\<exists>k < length cfs. \<exists>t. (\<lambda>(pc, s, stk) (pc', s', stk').
    pc = 0 \<and> pc' = size (P x) + size (P' x') + I' t \<and> Q s t \<and> Q' t s' \<and>
      stk' = F' t (F s stk)) (cfs ! 0) (cfs ! k)"
by (subgoal_tac "[] @ ?P \<Turnstile> cfs\<box>", drule execl_all_sub [where k = 0 and Q = ?Q],
 insert A B, (clarsimp simp: execl_all_def)+, insert A C D, drule execl_all_sub
 [where Q = ?Q'], simp+, clarify, rule exI, rule conjI, simp, rule exI, auto)


subsection "Main theorem"

text \<open>
It is time to prove compiler correctness. First, lemmas @{text acomp_acomp}, @{text bcomp_bcomp} are
derived from @{thm [source] execl_all_sub2} to reproduce the execution of two consecutive compiled
arithmetic expressions (possibly generated by both @{const acomp} and @{const bcomp}) and boolean
expressions (possibly generated by @{const bcomp}), respectively. Subsequently, the correctness of
@{const acomp} and @{const bcomp} is proven in lemmas @{text acomp_correct}, @{text bcomp_correct}.

\null
\<close>

lemma acomp_acomp:
 "\<lbrakk>acomp a\<^sub>1 @ acomp a\<^sub>2 @ P \<Turnstile> cfs\<box>;
    \<And>cfs. acomp a\<^sub>1 \<Turnstile> cfs\<box> \<Longrightarrow> apred a\<^sub>1 (cfs ! 0) (cfs ! (length cfs - 1));
    \<And>cfs. acomp a\<^sub>2 \<Turnstile> cfs\<box> \<Longrightarrow> apred a\<^sub>2 (cfs ! 0) (cfs ! (length cfs - 1))\<rbrakk> \<Longrightarrow>
  case cfs ! 0 of (pc, s, stk) \<Rightarrow> pc = 0 \<and> (\<exists>k < length cfs. cfs ! k =
    (size (acomp a\<^sub>1 @ acomp a\<^sub>2), s, aval a\<^sub>2 s # aval a\<^sub>1 s # stk))"
by (drule execl_all_sub2 [where I = "\<lambda>s. 0" and I' = "\<lambda>s. 0" and Q = "\<lambda>s s'. s' = s"
 and Q' = "\<lambda>s s'. s' = s" and F = "\<lambda>s stk. aval a\<^sub>1 s # stk"
 and F' = "\<lambda>s stk. aval a\<^sub>2 s # stk"], auto simp: apred_def)

lemma bcomp_bcomp:
 "\<lbrakk>bcomp (b\<^sub>1, f\<^sub>1, i\<^sub>1) @ bcomp (b\<^sub>2, f\<^sub>2, i\<^sub>2) \<Turnstile> cfs\<box>;
    \<And>cfs. bcomp (b\<^sub>1, f\<^sub>1, i\<^sub>1) \<Turnstile> cfs\<box> \<Longrightarrow>
      bpred (b\<^sub>1, f\<^sub>1, i\<^sub>1) (cfs ! 0) (cfs ! (length cfs - 1));
    \<And>cfs. bcomp (b\<^sub>2, f\<^sub>2, i\<^sub>2) \<Turnstile> cfs\<box> \<Longrightarrow>
      bpred (b\<^sub>2, f\<^sub>2, i\<^sub>2) (cfs ! 0) (cfs ! (length cfs - 1))\<rbrakk> \<Longrightarrow>
  case cfs ! 0 of (pc, s, stk) \<Rightarrow> pc = 0 \<and> (bval b\<^sub>1 s \<noteq> f\<^sub>1 \<longrightarrow>
    (\<exists>k < length cfs. cfs ! k = (size (bcomp (b\<^sub>1, f\<^sub>1, i\<^sub>1) @ bcomp (b\<^sub>2, f\<^sub>2, i\<^sub>2)) +
      (if bval b\<^sub>2 s = f\<^sub>2 then i\<^sub>2 else 0), s, stk)))"
by (clarify, rule conjI, simp add: execl_all_def, rule impI, subst (asm) append_Nil2
 [symmetric], drule execl_all_sub2 [where I = "\<lambda>s. if bval b\<^sub>1 s = f\<^sub>1 then i\<^sub>1 else 0"
 and I' = "\<lambda>s. if bval b\<^sub>2 s = f\<^sub>2 then i\<^sub>2 else 0" and Q = "\<lambda>s s'. s' = s"
 and Q' = "\<lambda>s s'. s' = s" and F = "\<lambda>s stk. stk" and F' = "\<lambda>s stk. stk"],
 auto simp: bpred_def)

lemma acomp_correct [simplified, intro]:
 "acomp a \<Turnstile> cfs\<box> \<Longrightarrow> apred a (cfs ! 0) (cfs ! (length cfs - 1))"
proof (induction a arbitrary: cfs, simp_all, frule_tac [3] acomp_acomp, auto)
  fix a\<^sub>1 a\<^sub>2 cfs s stk k
  assume A: "acomp a\<^sub>1 @ acomp a\<^sub>2 @ [ADD] \<Turnstile> cfs\<box>"
    (is "?ca\<^sub>1 @ ?ca\<^sub>2 @ ?i \<Turnstile> _\<box>")
  assume B: "k < length cfs" and
    C: "cfs ! k = (size ?ca\<^sub>1 + size ?ca\<^sub>2, s, aval a\<^sub>2 s # aval a\<^sub>1 s # stk)"
  hence "cfs ! Suc k = (size (?ca\<^sub>1 @ ?ca\<^sub>2 @ ?i), s, aval (Plus a\<^sub>1 a\<^sub>2) s # stk)"
    using A by (insert execl_next [of "?ca\<^sub>1 @ ?ca\<^sub>2 @ ?i" cfs k],
     simp add: execl_all_def, drule_tac impI, auto)
  thus "apred (Plus a\<^sub>1 a\<^sub>2) (0, s, stk) (cfs ! (length cfs - Suc 0))"
    using A and B and C by (insert execl_last [of "?ca\<^sub>1 @ ?ca\<^sub>2 @ ?i" cfs "Suc k"],
     simp add: execl_all_def apred_def, drule_tac impI, auto)
qed

lemma bcomp_correct [simplified, intro]:
 "\<lbrakk>bcomp x \<Turnstile> cfs\<box>; 0 \<le> snd (snd x)\<rbrakk> \<Longrightarrow> bpred x (cfs ! 0) (cfs ! (length cfs - 1))"
proof (induction x arbitrary: cfs rule: bcomp.induct, simp_all add: Let_def,
 frule_tac [4] acomp_acomp, frule_tac [3] bcomp_bcomp, auto, force simp: bpred_def)
  fix b\<^sub>1 b\<^sub>2 f i cfs s stk
  assume A: "bcomp (b\<^sub>1, False, size (bcomp (b\<^sub>2, f, i)) + (if f then 0 else i)) @
    bcomp (b\<^sub>2, f, i) \<Turnstile> cfs\<box>"
    (is "bcomp (_, _, ?n + ?i) @ ?cb \<Turnstile> _\<box>")
  moreover assume B: "cfs ! 0 = (0, s, stk)" and
   "\<And>cb cfs. \<lbrakk>cb = ?cb; bcomp (b\<^sub>1, False, ?n + ?i) \<Turnstile> cfs\<box>\<rbrakk> \<Longrightarrow>
      bpred (b\<^sub>1, False, ?n + ?i) (cfs ! 0) (cfs ! (length cfs - Suc 0))"
  ultimately have "\<exists>k < length cfs. bpred (b\<^sub>1, False, ?n + ?i)
    (off [] (cfs ! 0)) (off [] (cfs ! k))"
    by (rule_tac execl_all_sub, auto simp: execl_all_def)
  moreover assume C: "\<not> bval b\<^sub>1 s"
  ultimately obtain k where D: "k < length cfs" and
    E: "cfs ! k = (size (bcomp (b\<^sub>1, False, ?n + ?i)) + ?n + ?i, s, stk)"
    using B by (auto simp: bpred_def)
  assume "0 \<le> i"
  thus "bpred (And b\<^sub>1 b\<^sub>2, f, i) (0, s, stk) (cfs ! (length cfs - Suc 0))"
    using A and C and D and E by (insert execl_last, auto simp:
     execl_all_def bpred_def Let_def)
next
  fix b\<^sub>1 b\<^sub>2 f i cfs s stk k
  assume A: "bcomp (b\<^sub>1, False, size (bcomp (b\<^sub>2, f, i)) + (if f then 0 else i)) @
    bcomp (b\<^sub>2, f, i) \<Turnstile> cfs\<box>"
    (is "?cb\<^sub>1 @ ?cb\<^sub>2 \<Turnstile> _\<box>")
  assume "k < length cfs" and "0 \<le> i" and "bval b\<^sub>1 s" and
   "cfs ! k = (size ?cb\<^sub>1 + size ?cb\<^sub>2 + (if bval b\<^sub>2 s = f then i else 0), s, stk)"
  thus "bpred (And b\<^sub>1 b\<^sub>2, f, i) (0, s, stk) (cfs ! (length cfs - Suc 0))"
    using A by (insert execl_last, auto simp: execl_all_def bpred_def Let_def)
next
  fix a\<^sub>1 a\<^sub>2 f i cfs s stk k
  assume A: "acomp a\<^sub>1 @ acomp a\<^sub>2 @
    (if f then [JMPLESS i] else [JMPGE i]) \<Turnstile> cfs\<box>"
    (is "?ca\<^sub>1 @ ?ca\<^sub>2 @ ?i \<Turnstile> _\<box>")
  assume B: "k < length cfs" and
    C: "cfs ! k = (size ?ca\<^sub>1 + size ?ca\<^sub>2, s, aval a\<^sub>2 s # aval a\<^sub>1 s # stk)"
  hence D: "cfs ! Suc k =
    (size (?ca\<^sub>1 @ ?ca\<^sub>2 @ ?i) + (if bval (Less a\<^sub>1 a\<^sub>2) s = f then i else 0), s, stk)"
    using A by (insert execl_next [of "?ca\<^sub>1 @ ?ca\<^sub>2 @ ?i" cfs k],
     simp add: execl_all_def, drule_tac impI, auto split: if_split_asm)
  assume "0 \<le> i"
  with A and B and C and D have "length cfs - 1 = Suc k"
    by (rule_tac execl_last, auto simp: execl_all_def, simp split: if_split_asm)
  thus "bpred (Less a\<^sub>1 a\<^sub>2, f, i) (0, s, stk) (cfs ! (length cfs - Suc 0))"
    using D by (simp add: bpred_def)
qed

text \<open>
\null

Next, lemmas @{text bcomp_ccomp}, @{text ccomp_ccomp} are derived to reproduce the execution of a
compiled boolean expression followed by a compiled command and of two consecutive compiled commands,
respectively (possibly generated by @{const ccomp}). Then, compiler correctness for loops and for
all commands is proven in lemmas @{text while_correct} and @{text ccomp_correct}, respectively by
induction over the length of the list of configurations and by structural induction over commands.

\null
\<close>

lemma bcomp_ccomp:
 "\<lbrakk>bcomp (b, f, i) @ ccomp c @ P \<Turnstile> cfs\<box>; 0 \<le> i;
    \<And>cfs. ccomp c \<Turnstile> cfs\<box> \<Longrightarrow> cpred c (cfs ! 0) (cfs ! (length cfs - 1))\<rbrakk> \<Longrightarrow>
  case cfs ! 0 of (pc, s, stk) \<Rightarrow> pc = 0 \<and> (bval b s \<noteq> f \<longrightarrow>
    (\<exists>k < length cfs. case cfs ! k of (pc', s', stk') \<Rightarrow>
      pc' = size (bcomp (b, f, i) @ ccomp c) \<and> (c, s) \<Rightarrow> s' \<and> stk' = stk))"
by (clarify, rule conjI, simp add: execl_all_def, rule impI, drule execl_all_sub2
 [where I = "\<lambda>s. if bval b s = f then i else 0" and I' = "\<lambda>s. 0"
 and Q = "\<lambda>s s'. s' = s" and Q' = "\<lambda>s s'. (c, s) \<Rightarrow> s'" and F = "\<lambda>s stk. stk"
 and F' = "\<lambda>s stk. stk"], insert bcomp_correct [of "(b, f, i)"],
 auto simp: bpred_def cpred_def)

lemma ccomp_ccomp:
 "\<lbrakk>ccomp c\<^sub>1 @ ccomp c\<^sub>2 \<Turnstile> cfs\<box>;
    \<And>cfs. ccomp c\<^sub>1 \<Turnstile> cfs\<box> \<Longrightarrow> cpred c\<^sub>1 (cfs ! 0) (cfs ! (length cfs - 1));
    \<And>cfs. ccomp c\<^sub>2 \<Turnstile> cfs\<box> \<Longrightarrow> cpred c\<^sub>2 (cfs ! 0) (cfs ! (length cfs - 1))\<rbrakk> \<Longrightarrow>
  case cfs ! 0 of (pc, s, stk) \<Rightarrow> pc = 0 \<and> (\<exists>k < length cfs. \<exists>t.
    case cfs ! k of (pc', s', stk') \<Rightarrow> pc' = size (ccomp c\<^sub>1 @ ccomp c\<^sub>2) \<and>
      (c\<^sub>1, s) \<Rightarrow> t \<and> (c\<^sub>2, t) \<Rightarrow> s' \<and> stk' = stk)"
by (subst (asm) append_Nil2 [symmetric], drule execl_all_sub2 [where I = "\<lambda>s. 0"
 and I' = "\<lambda>s. 0" and Q = "\<lambda>s s'. (c\<^sub>1, s) \<Rightarrow> s'" and Q' = "\<lambda>s s'. (c\<^sub>2, s) \<Rightarrow> s'"
 and F = "\<lambda>s stk. stk" and F' = "\<lambda>s stk. stk"], auto simp: cpred_def, force)

lemma while_correct [simplified, intro]:
 "\<lbrakk>bcomp (b, False, size (ccomp c) + 1) @ ccomp c @
    [JMP (- (size (bcomp (b, False, size (ccomp c) + 1) @ ccomp c) + 1))] \<Turnstile> cfs\<box>;
    \<And>cfs. ccomp c \<Turnstile> cfs\<box> \<Longrightarrow> cpred c (cfs ! 0) (cfs ! (length cfs - 1))\<rbrakk> \<Longrightarrow>
  cpred (WHILE b DO c) (cfs ! 0) (cfs ! (length cfs - Suc 0))"
  (is "\<lbrakk>?cb @ ?cc @ [JMP (- ?n)] \<Turnstile> _\<box>; \<And>_. _ \<Longrightarrow> _\<rbrakk> \<Longrightarrow> ?Q cfs")
proof (induction cfs rule: length_induct, frule bcomp_ccomp, auto)
  fix cfs s stk
  assume A: "?cb @ ?cc @ [JMP (- size ?cb - size ?cc - 1)] \<Turnstile> cfs\<box>"
  hence "\<exists>k < length cfs. bpred (b, False, size (ccomp c) + 1)
    (off [] (cfs ! 0)) (off [] (cfs ! k))"
    by (rule_tac execl_all_sub, auto simp: execl_all_def)
  moreover assume B: "\<not> bval b s" and "cfs ! 0 = (0, s, stk)"
  ultimately obtain k where "k < length cfs" and "cfs ! k = (?n, s, stk)"
    by (auto simp: bpred_def)
  thus "cpred (WHILE b DO c) (0, s, stk) (cfs ! (length cfs - Suc 0))"
    using A and B by (insert execl_last, auto simp: execl_all_def cpred_def Let_def)
next
  fix cfs s s' stk k
  assume A: "?cb @ ?cc @ [JMP (- size ?cb - size ?cc - 1)] \<Turnstile> cfs\<box>"
    (is "?P \<Turnstile> _\<box>")
  assume B: "k < length cfs" and "cfs ! k = (size ?cb + size ?cc, s', stk)"
  moreover from this have C: "k \<noteq> length cfs - 1"
    using A by (rule_tac notI, simp add: execl_all_def)
  ultimately have D: "cfs ! Suc k = (0, s', stk)"
    using A by (insert execl_next [of ?P cfs k], auto simp: execl_all_def)
  moreover have E: "Suc k + (length (drop (Suc k) cfs) - 1) = length cfs - 1"
    (is "Suc k + (length ?cfs - 1) = _")
    using B and C by simp
  ultimately have "?P \<Turnstile> ?cfs\<box>"
    using A and B and C by (auto simp: execl_all_def intro: execl_drop)
  moreover assume "\<forall>cfs'. length cfs' < length cfs \<longrightarrow> ?P \<Turnstile> cfs'\<box> \<longrightarrow> ?Q cfs'"
  hence "length ?cfs < length cfs \<longrightarrow> ?P \<Turnstile> ?cfs\<box> \<longrightarrow> ?Q ?cfs" ..
  ultimately have "cpred (WHILE b DO c) (cfs ! Suc k) (cfs ! (length cfs - 1))"
    using B and C and E by simp
  moreover assume "bval b s" and "(c, s) \<Rightarrow> s'"
  ultimately show "cpred (WHILE b DO c) (0, s, stk) (cfs ! (length cfs - Suc 0))"
    using D by (auto simp: cpred_def)
qed

lemma ccomp_correct:
 "ccomp c \<Turnstile> cfs\<box> \<Longrightarrow> cpred c (cfs ! 0) (cfs ! (length cfs - 1))"
proof (induction c arbitrary: cfs, simp_all add: Let_def, frule_tac [4] bcomp_ccomp,
 frule_tac [3] ccomp_ccomp, auto)
  fix a x cfs
  assume A: "acomp a @ [STORE x] \<Turnstile> cfs\<box>"
  hence "\<exists>k < length cfs. apred a (off [] (cfs ! 0)) (off [] (cfs ! k))"
    by (rule_tac execl_all_sub, auto simp: execl_all_def)
  moreover obtain s stk where B: "cfs ! 0 = (0, s, stk)"
    using A by (cases "cfs ! 0", simp add: execl_all_def)
  ultimately obtain k where C: "k < length cfs" and
    D: "cfs ! k = (size (acomp a), s, aval a s # stk)"
    by (auto simp: apred_def)
  hence "cfs ! Suc k = (size (acomp a) + 1, s(x := aval a s), stk)"
    using A by (insert execl_next [of "acomp a @ [STORE x]" cfs k],
     simp add: execl_all_def, drule_tac impI, auto)
  thus "cpred (x ::= a) (cfs ! 0) (cfs ! (length cfs - Suc 0))"
    using A and B and C and D by (insert execl_last [of "acomp a @ [STORE x]"
     cfs "Suc k"], simp add: execl_all_def cpred_def, drule_tac impI, auto)
next
  fix c\<^sub>1 c\<^sub>2 cfs s s' t stk k
  assume "ccomp c\<^sub>1 @ ccomp c\<^sub>2 \<Turnstile> cfs\<box>" and "k < length cfs" and
   "cfs ! k = (size (ccomp c\<^sub>1) + size (ccomp c\<^sub>2), s', stk)"
  moreover assume "(c\<^sub>1, s) \<Rightarrow> t" and "(c\<^sub>2, t) \<Rightarrow> s'"
  ultimately show "cpred (c\<^sub>1;; c\<^sub>2) (0, s, stk) (cfs ! (length cfs - Suc 0))"
    by (insert execl_last, auto simp: execl_all_def cpred_def)
next
  fix b c\<^sub>1 c\<^sub>2 cfs s stk
  assume A: "bcomp (b, False, size (ccomp c\<^sub>1) + 1) @ ccomp c\<^sub>1 @
    JMP (size (ccomp c\<^sub>2)) # ccomp c\<^sub>2 \<Turnstile> cfs\<box>"
    (is "bcomp ?x @ ?cc\<^sub>1 @ _ # ?cc\<^sub>2 \<Turnstile> _\<box>")
  let ?P = "bcomp ?x @ ?cc\<^sub>1 @ [JMP (size ?cc\<^sub>2)]"
  have "\<exists>k < length cfs. bpred ?x (off [] (cfs ! 0)) (off [] (cfs ! k))"
    using A by (rule_tac execl_all_sub, auto simp: execl_all_def)
  moreover assume B: "\<not> bval b s" and "cfs ! 0 = (0, s, stk)"
  ultimately obtain k where C: "k < length cfs" and D: "cfs ! k = (size ?P, s, stk)"
    by (force simp: bpred_def)
  assume "\<And>cfs. ?cc\<^sub>2 \<Turnstile> cfs\<box> \<Longrightarrow> cpred c\<^sub>2 (cfs ! 0) (cfs ! (length cfs - Suc 0))"
  hence "\<exists>k' < length cfs. cpred c\<^sub>2 (off ?P (cfs ! k)) (off ?P (cfs ! k'))"
    using A and C and D by (rule_tac execl_all_sub [where P'' = "[]"], auto)
  then obtain k' where "k' < length cfs" and "case cfs ! k' of (pc', s', stk') \<Rightarrow>
    pc' = size (?P @ ?cc\<^sub>2) \<and> (c\<^sub>2, s) \<Rightarrow> s' \<and> stk' = stk"
    using D by (fastforce simp: cpred_def)
  thus "cpred (IF b THEN c\<^sub>1 ELSE c\<^sub>2) (0, s, stk) (cfs ! (length cfs - Suc 0))"
    using A and B by (insert execl_last, auto simp: execl_all_def cpred_def Let_def)
next
  fix b c\<^sub>1 c\<^sub>2 cfs s s' stk k
  assume A: "bcomp (b, False, size (ccomp c\<^sub>1) + 1) @ ccomp c\<^sub>1 @
    JMP (size (ccomp c\<^sub>2)) # ccomp c\<^sub>2 \<Turnstile> cfs\<box>"
    (is "?cb @ ?cc\<^sub>1 @ ?i # ?cc\<^sub>2 \<Turnstile> _\<box>")
  assume B: "k < length cfs" and C: "cfs ! k = (size ?cb + size ?cc\<^sub>1, s', stk)"
  hence D: "cfs ! Suc k = (size (?cb @ ?cc\<^sub>1 @ ?i # ?cc\<^sub>2), s', stk)"
    (is "_ = (size ?P, _, _)")
    using A by (insert execl_next [of ?P cfs k], simp add: execl_all_def,
     drule_tac impI, auto)
  assume "bval b s" and "(c\<^sub>1, s) \<Rightarrow> s'"
  thus "cpred (IF b THEN c\<^sub>1 ELSE c\<^sub>2) (0, s, stk) (cfs ! (length cfs - Suc 0))"
    using A and B and C and D by (insert execl_last [of ?P cfs "Suc k"],
     simp add: execl_all_def cpred_def Let_def, drule_tac impI, auto)
next
  fix c\<^sub>1 c\<^sub>2 cfs
  assume A: "JMPND (size (ccomp c\<^sub>1) + 1) # ccomp c\<^sub>1 @
    JMP (size (ccomp c\<^sub>2)) # ccomp c\<^sub>2 \<Turnstile> cfs\<box>"
    (is "JMPND (?n\<^sub>1 + 1) # ?cc\<^sub>1 @ JMP ?n\<^sub>2 # ?cc\<^sub>2 \<Turnstile> _\<box>")
  let ?P = "JMPND (?n\<^sub>1 + 1) # ?cc\<^sub>1 @ [JMP ?n\<^sub>2]"
  assume
    B: "\<And>cfs. ?cc\<^sub>1 \<Turnstile> cfs\<box> \<Longrightarrow> cpred c\<^sub>1 (cfs ! 0) (cfs ! (length cfs - Suc 0))" and
    C: "\<And>cfs. ?cc\<^sub>2 \<Turnstile> cfs\<box> \<Longrightarrow> cpred c\<^sub>2 (cfs ! 0) (cfs ! (length cfs - Suc 0))"
  from A obtain s stk where D: "cfs ! 0 = (0, s, stk)"
    by (cases "cfs ! 0", simp add: execl_all_def)
  with A have "cfs ! 1 = (1, s, stk) \<or> cfs ! 1 = (?n\<^sub>1 + 2, s, stk)"
    by (insert execl_next [of "?P @ ?cc\<^sub>2" cfs 0], simp add: execl_all_def,
     drule_tac impI, auto)
  moreover {
    assume E: "cfs ! 1 = (1, s, stk)"
    hence "\<exists>k < length cfs. cpred c\<^sub>1 (off [hd ?P] (cfs ! 1)) (off [hd ?P] (cfs ! k))"
      using A and B by (rule_tac execl_all_sub, auto simp: execl_all_def)
    then obtain k where "k < length cfs" and "case cfs ! k of (pc', s', stk') \<Rightarrow>
      pc' = ?n\<^sub>1 + 1 \<and> (c\<^sub>1, s) \<Rightarrow> s' \<and> stk' = stk"
      using E by (fastforce simp: cpred_def)
    moreover from this have "case cfs ! Suc k of (pc', s', stk') \<Rightarrow>
      pc' = ?n\<^sub>1 + ?n\<^sub>2 + 2 \<and> (c\<^sub>1, s) \<Rightarrow> s' \<and> stk' = stk"
      using A by (insert execl_next [of "?P @ ?cc\<^sub>2" cfs k], simp add: execl_all_def,
       drule_tac impI, auto)
    ultimately have "cpred (c\<^sub>1 OR c\<^sub>2) (cfs ! 0) (cfs ! (length cfs - Suc 0))"
      using A and D by (insert execl_last [of "?P @ ?cc\<^sub>2" cfs "Suc k"],
       simp add: execl_all_def cpred_def split_def Let_def, drule_tac impI, auto)
  }
  moreover {
    assume E: "cfs ! 1 = (?n\<^sub>1 + 2, s, stk)"
    with A and C have "\<exists>k<length cfs. cpred c\<^sub>2 (off ?P (cfs!1)) (off ?P (cfs!k))"
      by (rule_tac execl_all_sub [where P'' = "[]"], auto simp: execl_all_def)
    then obtain k where "k < length cfs" and "case cfs ! k of (pc', s', stk') \<Rightarrow>
      pc' = ?n\<^sub>1 + ?n\<^sub>2 + 2 \<and> (c\<^sub>2, s) \<Rightarrow> s' \<and> stk' = stk"
      using E by (fastforce simp: cpred_def)
    with A and D have "cpred (c\<^sub>1 OR c\<^sub>2) (cfs ! 0) (cfs ! (length cfs - Suc 0))"
      by (insert execl_last, auto simp: execl_all_def cpred_def Let_def)
  }
  ultimately show "cpred (c\<^sub>1 OR c\<^sub>2) (cfs ! 0) (cfs ! (length cfs - Suc 0))" ..
qed

text \<open>
\null

Finally, the main compiler correctness theorem, expressed using predicate @{const exec}, is proven.
First, @{prop "P \<turnstile> cf \<rightarrow>* cf'"} is shown to imply the existence of a nonempty list of configurations
@{text cfs} such that @{prop "P \<Turnstile> cfs"}, whose initial and final configurations match @{text cf}
and @{text cf'}, respectively. Then, the main theorem is derived as a straightforward consequence of
this lemma and of the previous lemma @{thm [source] ccomp_correct}.

\null
\<close>

lemma exec_execl [dest!]:
 "P \<turnstile> cf \<rightarrow>* cf' \<Longrightarrow> \<exists>cfs. P \<Turnstile> cfs \<and> cfs \<noteq> [] \<and> hd cfs = cf \<and> last cfs = cf'"
by (erule star.induct, force, erule exE, rule list.exhaust, blast,
 simp del: last.simps, rule exI, subst execl.simps(1), simp)

theorem ccomp_exec:
 "ccomp c \<turnstile> (0, s, stk) \<rightarrow>* (size (ccomp c), s', stk') \<Longrightarrow> (c, s) \<Rightarrow> s' \<and> stk' = stk"
by (insert ccomp_correct, force simp: hd_conv_nth last_conv_nth execl_all_def cpred_def)

end
