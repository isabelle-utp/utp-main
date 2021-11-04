theory Global
  imports Main Result
begin

sledgehammer_params [timeout = 30]
sledgehammer_params [provers = "cvc4 e spass vampire z3"]

lemma if_then_Some_else_None_eq[simp]:
  "(if a then Some b else None) = Some c \<longleftrightarrow> a \<and> b = c"
  "(if a then Some b else None) = None \<longleftrightarrow> \<not> a"
  by (cases a) simp_all

lemma if_then_else_distributive: "(if a then f b else f c) = f (if a then b else c)"
  by simp

fun traverse :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
  "traverse f [] = Some []" |
  "traverse f (x # xs) = do {
    x' \<leftarrow> f x;
    xs' \<leftarrow> traverse f xs;
    Some (x' # xs')
  }"

lemma traverse_length: "traverse f xs = Some ys \<Longrightarrow> length ys = length xs"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    by (auto simp add: Option.bind_eq_Some_conv)
qed

datatype 'instr fundef =
  Fundef (body: "'instr list") (arity: nat)

lemma rel_fundef_arities: "rel_fundef r gd1 gd2 \<Longrightarrow> arity gd1 = arity gd2"
  by (simp add: fundef.rel_sel)

lemma rel_fundef_body_length[simp]:
  "rel_fundef r fd1 fd2 \<Longrightarrow> length (body fd1) = length (body fd2)"
  by (auto intro: list_all2_lengthD simp add: fundef.rel_sel)

datatype ('fenv, 'henv, 'fun) prog =
  Prog (fun_env: 'fenv) (heap: 'henv) (main_fun: 'fun)

datatype ('fun, 'operand) frame =
  Frame 'fun (prog_counter: nat) (operand_stack: "'operand list")

datatype ('fenv, 'henv, 'frame) state =
  State (fun_env: 'fenv) (heap: 'henv) (callstack: "'frame list")

definition rewrite :: "'instr list \<Rightarrow> nat \<Rightarrow> 'instr \<Rightarrow> 'instr list" where
  "rewrite p pc i = list_update p pc i"

fun rewrite_fundef_body :: "'instr fundef \<Rightarrow> nat \<Rightarrow> 'instr \<Rightarrow> 'instr fundef" where
  "rewrite_fundef_body (Fundef xs ar) n x = Fundef (rewrite xs n x) ar"

lemmas length_rewrite[simp] = length_list_update[folded rewrite_def]
lemmas nth_rewrite_eq[simp] = nth_list_update_eq[folded rewrite_def]
lemmas nth_rewrite_neq[simp] = nth_list_update_neq[folded rewrite_def]
lemmas take_rewrite[simp] = take_update_cancel[folded rewrite_def]
lemmas take_rewrite_swap = take_update_swap[folded rewrite_def]
lemmas map_rewrite = map_update[folded rewrite_def]
lemmas list_all2_rewrite_cong[intro] = list_all2_update_cong[folded rewrite_def]

lemma body_rewrite_fundef_body[simp]: "body (rewrite_fundef_body fd n x) = rewrite (body fd) n x"
  by (cases fd) simp

lemma arity_rewrite_fundef_body[simp]: "arity (rewrite_fundef_body fd n x) = arity fd"
  by (cases fd) simp

lemma if_eq_const_conv: "(if x then y else z) = w \<longleftrightarrow> x \<and> y = w \<or> \<not>x \<and> z = w"
  by simp

end
