theory Ubx_type_inference  
  imports Result Ubx
    "HOL-Library.Monad_Syntax"
begin

section \<open>Type of operations\<close>

locale ubx_sp =
  ubx
    F_empty F_get F_add F_to_list
    heap_empty heap_get heap_add heap_to_list
    is_true is_false box_ubx1 unbox_ubx1 box_ubx2 unbox_ubx2
    \<OO>\<pp> \<AA>\<rr>\<ii>\<tt>\<yy> \<II>\<nn>\<ll>\<OO>\<pp> \<II>\<nn>\<ll> \<II>\<ss>\<II>\<nn>\<ll> \<DD>\<ee>\<II>\<nn>\<ll> \<UU>\<bb>\<xx>\<OO>\<pp> \<UU>\<bb>\<xx> \<BB>\<oo>\<xx> \<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp>
  for
    \<comment> \<open>Functions environment\<close>
    F_empty and F_get and F_add and F_to_list and

    \<comment> \<open>Memory heap\<close>
    heap_empty and heap_get and heap_add and heap_to_list and

    \<comment> \<open>Unboxed values\<close>
    is_true and is_false and
    box_ubx1 and unbox_ubx1 and
    box_ubx2 and unbox_ubx2 and

    \<comment> \<open>n-ary operations\<close>
    \<OO>\<pp> and \<AA>\<rr>\<ii>\<tt>\<yy> and \<II>\<nn>\<ll>\<OO>\<pp> and \<II>\<nn>\<ll> and \<II>\<ss>\<II>\<nn>\<ll> and \<DD>\<ee>\<II>\<nn>\<ll> and \<UU>\<bb>\<xx>\<OO>\<pp> and \<UU>\<bb>\<xx> and \<BB>\<oo>\<xx> and \<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp>
begin


section \<open>Strongest postcondition of instructions\<close>

fun sp_gen_pop_push where
  "sp_gen_pop_push (domain, codom) \<Sigma> = (
    let ar = length domain in
    if ar \<le> length \<Sigma> \<and> take ar \<Sigma> = domain then
      Ok (codom # drop ar \<Sigma>)
    else
      Error ()
  )"

fun sp_instr :: "('fun \<Rightarrow> _ fundef option) \<Rightarrow> _ \<Rightarrow> type option list \<Rightarrow> (unit, type option list) result" where
  "sp_instr _ (IPush _) \<Sigma> = Ok (None # \<Sigma>)" |
  "sp_instr _ (IPushUbx1 _) \<Sigma> = Ok (Some Ubx1 # \<Sigma>)" |
  "sp_instr _ (IPushUbx2 _) \<Sigma> = Ok (Some Ubx2 # \<Sigma>)" |
  "sp_instr _ IPop (_ # \<Sigma>) = Ok \<Sigma>" |
  "sp_instr _ (ILoad _) (None # \<Sigma>) = Ok (None # \<Sigma>)" |
  "sp_instr _ (ILoadUbx \<tau> _) (None # \<Sigma>) = Ok (Some \<tau> # \<Sigma>)" |
  "sp_instr _ (IStore _) (None # None # \<Sigma>) = Ok \<Sigma>" |
  "sp_instr _ (IStoreUbx \<tau>\<^sub>1 _) (None # Some \<tau>\<^sub>2 # \<Sigma>) = (if \<tau>\<^sub>1 = \<tau>\<^sub>2 then Ok \<Sigma> else Error ())" |
  "sp_instr _ (IOp op) \<Sigma> = sp_gen_pop_push (replicate (\<AA>\<rr>\<ii>\<tt>\<yy> op) None, None) \<Sigma>" |
  "sp_instr _ (IOpInl opinl) \<Sigma> = sp_gen_pop_push (replicate (\<AA>\<rr>\<ii>\<tt>\<yy> (\<DD>\<ee>\<II>\<nn>\<ll> opinl)) None, None) \<Sigma>" |
  "sp_instr _ (IOpUbx opubx) \<Sigma> = sp_gen_pop_push (\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp> opubx) \<Sigma>" |
  "sp_instr F (ICall f) \<Sigma> = do {
    fd \<leftarrow> Result.of_option () (F f);
    sp_gen_pop_push (replicate (arity fd) None, None) \<Sigma>
  }" |
  "sp_instr _ _ _ = Error ()"

lemma sp_instr_no_jump: "sp_instr F instr \<Sigma> = Ok type \<Longrightarrow> \<not> is_jump instr"
  by (induction instr \<Sigma> rule: sp_instr.induct) simp_all

lemma map_constant[simp]: "\<forall>x \<in> set xs. x = y \<Longrightarrow> map (\<lambda>_. y) xs = xs"
  by (simp add: map_idI)

lemma sp_generalize_instr:
  assumes "sp_instr F x \<Sigma> = Ok \<Sigma>'"
  shows "sp_instr F (generalize_instr x) (map (\<lambda>_. None) \<Sigma>) = Ok (map (\<lambda>_. None) \<Sigma>')"
  using assms
  apply (induction F x \<Sigma> rule: sp_instr.induct;
      (auto simp: Let_def take_map drop_map; fail)?)
  subgoal for _ opubx
    apply (cases "\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp> opubx")
    by (auto simp add: Let_def take_map drop_map map_replicate_const \<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp>_\<AA>\<rr>\<ii>\<tt>\<yy>)
  done

lemma map_typeof_box: "map typeof (map box_operand \<Sigma>) = replicate (length \<Sigma>) None"
proof (induction \<Sigma>)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    by (cases x) simp_all
qed

section \<open>Strongest postcondition of function definitions\<close>

fun sp :: "('fun \<Rightarrow> _ fundef option) \<Rightarrow> _ list \<Rightarrow> type option list \<Rightarrow> (unit, type option list) result" where
  "sp _ [] \<Sigma> = Ok \<Sigma>" |
  "sp F (instr # p) \<Sigma> = do {
    \<Sigma>' \<leftarrow> sp_instr F instr \<Sigma>;
    sp F p \<Sigma>'
  }"

lemma sp_no_jump: "sp F xs \<Sigma> = Ok type \<Longrightarrow> \<forall>x \<in> set xs. \<not> is_jump x"
  by (induction xs arbitrary: \<Sigma>; auto dest: sp_instr_no_jump)

lemma sp_append: "sp F (xs @ ys) \<Sigma> = sp F xs \<Sigma> \<bind> sp F ys"
proof (induction xs arbitrary: \<Sigma>)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    by (cases "sp_instr F x \<Sigma>"; simp)
qed

lemmas sp_eq_bind_take_drop =
  sp_append[of _ "take n xs" "drop n xs" for n xs, unfolded append_take_drop_id]

lemma sp_generalize:
  assumes "sp F xs \<Sigma> = Ok \<Sigma>'"
  shows "sp F (map generalize_instr xs) (map (\<lambda>_. None) \<Sigma>) = Ok (map (\<lambda>_. None) \<Sigma>')"
using assms
proof (induction xs arbitrary: \<Sigma> \<Sigma>')
  case Nil
  then show ?case using assms(1) by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "sp_instr F x \<Sigma>")
    case (Error x1)
    then show ?thesis
      using Cons.prems by auto
  next
    case (Ok \<Sigma>'')
    show ?thesis
      using Cons sp_generalize_instr[OF Ok]
      by (simp add: Ok)
  qed
qed

lemma sp_generalize2:
  assumes "sp F xs (replicate n None) = Ok \<Sigma>'"
  shows "sp F (map generalize_instr xs) (replicate n None) = Ok (map (\<lambda>_. None) \<Sigma>')"
  using assms
  using sp_generalize by fastforce

lemma comp_K[simp]: "(\<lambda>_. x) \<circ> f = (\<lambda>_. x)"
  by auto

lemma is_ok_sp_generalize:
  assumes "is_ok (sp F xs (map (\<lambda>_. None) \<Sigma>))"
    shows "is_ok (sp F (map generalize_instr xs) (map (\<lambda>_. None) \<Sigma>))"
proof -
  from assms obtain res where 0: "sp F xs (map (\<lambda>_. None) \<Sigma>) = Ok res"
    by (auto simp add: is_ok_def)
  show ?thesis
    using sp_generalize[OF 0] by simp
qed

lemma is_ok_sp_generalize2:
  assumes "is_ok (sp F xs (replicate n None))"
  shows "is_ok (sp F (map generalize_instr xs) (replicate n None))"
  using assms is_ok_sp_generalize
  by (metis Ex_list_of_length map_replicate_const)

lemma sp_instr_op:
  assumes "\<DD>\<ee>\<II>\<nn>\<ll> opinl = op"
  shows "sp_instr F (IOp op) \<Sigma> = sp_instr F (IOpInl opinl) \<Sigma>"
  by (rule sp_instr.cases[of "(F, (IOp op), \<Sigma>)"]; simp add: Let_def assms)

lemma sp_list_update:
  assumes
    "n < length xs" and
    "\<forall>\<Sigma>. sp_instr F (xs ! n) \<Sigma> = sp_instr F x \<Sigma>"
  shows "sp F (xs[n := x]) = sp F xs"
proof (intro ext)
  fix ys
  have "sp F (take n xs @ x # drop (Suc n) xs) ys = sp F (take n xs @ xs ! n # drop (Suc n) xs) ys"
    unfolding sp_append
    using assms(2)
    by (cases "sp F (take n xs) ys"; simp)
  thus "sp F (xs[n := x]) ys = sp F xs ys"
    unfolding id_take_nth_drop[OF assms(1), symmetric]
    unfolding upd_conv_take_nth_drop[OF assms(1), symmetric]
    by assumption
qed

lemma sp_list_update_eq_Ok:
  assumes
    "n < length xs" and
    "\<forall>\<Sigma>. sp_instr F (xs ! n) \<Sigma> = sp_instr F x \<Sigma>" and
    "sp F xs ys = Ok zs"
  shows "sp F (xs[n := x]) ys = Ok zs"
  unfolding sp_list_update[OF assms(1,2)]
  using assms(3)
  by assumption

lemma is_ok_sp_list_update:
  assumes
    "is_ok (sp F xs types)" and
    "pc < length xs" and
    "\<forall>\<Sigma>. sp_instr F (xs ! pc) \<Sigma> = sp_instr F instr \<Sigma>"
  shows "is_ok (sp F (xs[pc := instr]) types)"
proof -
  from assms(1) obtain types' where "sp F xs types = Ok types'"
    unfolding is_ok_def by auto
  thus ?thesis
    using sp_list_update[OF assms(2,3)] by simp
qed

lemmas sp_rewrite = sp_list_update[folded rewrite_def]
lemmas sp_rewrite_eq_Ok = sp_list_update_eq_Ok[folded rewrite_def]
lemmas is_ok_sp_rewrite = is_ok_sp_list_update[folded rewrite_def]

end

end