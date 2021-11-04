chapter \<open>Preliminaries\<close>

(*<*)
theory Prelim
  imports Main "HOL-Eisbach.Eisbach"
begin
(*>*)

section \<open>Trivia\<close>

abbreviation (input) any where "any \<equiv> undefined"

lemma Un_Diff2: "B \<inter> C = {} \<Longrightarrow> A \<union> B - C = A - C \<union> B" by auto

lemma Diff_Diff_Un: "A - B - C = A - (B \<union> C)" by auto

fun first :: "nat \<Rightarrow> nat list" where
  "first 0 = []"
| "first (Suc n) = n # first n"


text \<open>Facts about zipping lists:\<close>

lemma fst_set_zip_map_fst:
  "length xs = length ys \<Longrightarrow> fst ` (set (zip (map fst xs) ys)) = fst ` (set xs)"
  by (induct xs ys rule: list_induct2) auto

lemma snd_set_zip_map_snd:
  "length xs = length ys \<Longrightarrow> snd ` (set (zip xs (map snd ys))) = snd ` (set ys)"
  by (induct xs ys rule: list_induct2) auto

lemma snd_set_zip:
  "length xs = length ys \<Longrightarrow> snd ` (set (zip xs ys)) = set ys"
  by (induct xs ys rule: list_induct2) auto

lemma set_zip_D: "(x, y) \<in> set (zip xs ys) \<Longrightarrow> x \<in> set xs \<and> y \<in> set ys"
  using set_zip_leftD set_zip_rightD by auto

lemma inj_on_set_zip_map:
  assumes i: "inj_on f X"
    and a: "(f x1, y1) \<in> set (zip (map f xs) ys)" "set xs \<subseteq> X" "x1 \<in> X" "length xs = length ys"
  shows "(x1, y1) \<in> set (zip xs ys)"
using a proof (induct xs arbitrary: ys x1 y1)
  case (Cons x xs yys)
  thus ?case using i unfolding inj_on_def by (cases yys) auto
qed (insert i, auto)

lemma set_zip_map_fst_snd:
  assumes "(u,x) \<in> set (zip us (map snd txs))"
    and "(t,u) \<in> set (zip (map fst txs) us)"
    and "distinct (map snd txs)"
    and "distinct us" and "length us = length txs"
  shows "(t, x) \<in> set txs"
  using assms(5,1-4)
  by (induct us txs arbitrary: u x t rule: list_induct2)
    (auto dest: set_zip_leftD set_zip_rightD)

lemma set_zip_map_fst_snd2:
  assumes "(u, x) \<in> set (zip us (map snd txs))"
    and "(t, x) \<in> set txs"
    and "distinct (map snd txs)"
    and "distinct us" and "length us = length txs"
  shows "(t, u) \<in> set (zip (map fst txs) us)"
  using assms(5,1-4)
  by (induct us txs arbitrary: u x t rule: list_induct2)
    (auto dest: set_zip_rightD simp: image_iff)

lemma set_zip_length_map:
  assumes "(x1, y1) \<in> set (zip xs ys)" and "length xs = length ys"
  shows "(f x1, y1) \<in> set (zip (map f xs) ys)"
  using assms(2,1) by (induct xs ys arbitrary: x1 y1 rule: list_induct2) auto

definition asList :: "'a set \<Rightarrow> 'a list" where
  "asList A \<equiv> SOME as. set as = A"

lemma asList[simp,intro!]: "finite A \<Longrightarrow> set (asList A) = A"
  unfolding asList_def by (meson finite_list tfl_some)

lemma triv_Un_imp_aux:
  "(\<And>a. \<phi> \<Longrightarrow> a \<notin> A \<Longrightarrow> a \<in> B \<longleftrightarrow> a \<in> C) \<Longrightarrow> \<phi> \<longrightarrow> A \<union> B = A \<union> C"
  by auto

definition toN where "toN n \<equiv> [0..<(Suc n)]"

lemma set_toN[simp]: "set (toN n) = {0..n}"
  unfolding toN_def by auto

declare list.map_cong[cong]


section \<open>Some Proof Infrastructure\<close>

ML \<open>
exception TAC of term

val simped = Thm.rule_attribute [] (fn context => fn thm =>
  let
    val ctxt = Context.proof_of context;
    val (thm', ctxt') = yield_singleton (apfst snd oo Variable.import false) thm ctxt;
    val full_goal = Thm.prop_of thm';
    val goal = Goal.prove ctxt' [] [] full_goal (fn {context = ctxt, prems = _} =>
      HEADGOAL (asm_full_simp_tac ctxt THEN' TRY o SUBGOAL (fn (goal, _) => raise (TAC goal))))
      |> K (HOLogic.mk_Trueprop @{term True})
      handle TAC goal => goal;
    val thm = Goal.prove ctxt' [] [] goal (fn {context = ctxt, prems = _} =>
      HEADGOAL (Method.insert_tac ctxt [thm'] THEN' asm_full_simp_tac ctxt))
      |> singleton (Variable.export ctxt' ctxt);
  in thm end)

val _ = Theory.setup
  (Attrib.setup \<^binding>\<open>simped\<close> (pair simped) "simped rule");
\<close>

method RULE methods meth uses rule =
  (rule rule; (solves meth)?)

text \<open>TryUntilFail:\<close>
(* This is non-hazardous, since it does not touch the goal on which it fails. *)
method TUF methods meth =
  ((meth;fail)+)?

text \<open>Helping a method, usually simp or auto, with specific substitutions inserted.
For auto, this is a bit like a "simp!" analogue of "intro!" and "dest!": It forces
the application of an indicated simplification rule, if this is possible.\<close>

method variousSubsts1 methods meth uses s1 =
  (meth?,(subst s1)?, meth?)
method variousSubsts2 methods meth uses s1 s2 =
  (meth?,(subst s1)?, meth?, subst s2, meth?)
method variousSubsts3 methods meth uses s1 s2 s3 =
  (meth?,(subst s1)?, meth?, (subst s2)?, meth?, (subst s3)?, meth?)
method variousSubsts4 methods meth uses s1 s2 s3 s4 =
  (meth?,(subst s1)?, meth?, (subst s2)?, meth?, (subst s3)?, meth?, (subst s4)?, meth?)
method variousSubsts5 methods meth uses s1 s2 s3 s4 s5 =
  (meth?,(subst s1)?, meth?, (subst s2)?, meth?, (subst s3)?, meth?, (subst s4)?, meth?, (subst s5)?, meth?)
method variousSubsts6 methods meth uses s1 s2 s3 s4 s5 s6 =
  (meth?,(subst s1)?, meth?, (subst s2)?, meth?, (subst s3)?, meth?,
         (subst s4)?, meth?, (subst s5)?, meth?, (subst s6)?, meth?)

(*<*)
end
(*>*)

