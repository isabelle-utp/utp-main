theory Op_example
  imports OpUbx Ubx_type_inference Global Unboxed_lemmas
begin


section \<open>Dynamic values\<close>

datatype dynamic = DNil | DBool bool | DNum nat

definition is_true where
  "is_true d = (d = DBool True)"

definition is_false where
  "is_false d = (d = DBool False)"

definition box_bool :: "bool \<Rightarrow> dynamic" where
  "box_bool = DBool"

definition box_num :: "nat \<Rightarrow> dynamic" where
  "box_num = DNum"

fun unbox_num :: "dynamic \<Rightarrow> nat option" where
   "unbox_num (DNum n) = Some n" |
   "unbox_num _ = None"

fun unbox_bool :: "dynamic \<Rightarrow> bool option" where
   "unbox_bool (DBool b) = Some b" |
   "unbox_bool _ = None"

interpretation unboxed_dynamic:
  unboxedval is_true is_false box_num unbox_num box_bool unbox_bool
proof (unfold_locales; (simp add: is_true_def is_false_def)?)
  fix d n
  show "unbox_num d = Some n \<Longrightarrow> box_num n = d"
    by (cases d; simp add: box_num_def)
next
  fix d b
  show "unbox_bool d = Some b \<Longrightarrow> box_bool b = d"
    by (cases d; simp add: box_bool_def)
qed


section \<open>Normal operations\<close>

datatype op =
  OpNeg |
  OpAdd |
  OpMul

fun ar :: "op \<Rightarrow> nat" where
  "ar OpNeg = 1" |
  "ar OpAdd = 2" |
  "ar OpMul = 2"

fun eval_Neg :: "dynamic list \<Rightarrow> dynamic" where
  "eval_Neg [DBool b] = DBool (\<not>b)" |
  "eval_Neg [_] = DNil"

fun eval_Add :: "dynamic list \<Rightarrow> dynamic" where
  "eval_Add [DBool x, DBool y] = DBool (x \<or> y)" |
  "eval_Add [DNum x, DNum y] = DNum (x + y)" |
  "eval_Add [_, _] = DNil"

fun eval_Mul :: "dynamic list \<Rightarrow> dynamic" where
  "eval_Mul [DBool x, DBool y] = DBool (x \<and> y)" |
  "eval_Mul [DNum x, DNum y] = DNum (x * y)" |
  "eval_Mul [_, _] = DNil"

fun eval :: "op \<Rightarrow> dynamic list \<Rightarrow> dynamic" where
  "eval OpNeg = eval_Neg" |
  "eval OpAdd = eval_Add" |
  "eval OpMul = eval_Mul"

lemma eval_arith_domain: "length xs = ar op \<Longrightarrow> \<exists>y. eval op xs = y"
  by simp

interpretation op_Op: nary_operations eval ar
  using eval_arith_domain
  by (unfold_locales; simp)


section \<open>Inlined operations\<close>

datatype opinl =
  OpAddNum |
  OpMulNum

fun inl :: "op \<Rightarrow> dynamic list \<Rightarrow> opinl option" where
  "inl OpAdd [DNum _, DNum _] = Some OpAddNum" |
  "inl OpMul [DNum _, DNum _] = Some OpMulNum" |
  "inl _ _ = None"

inductive isinl :: "opinl \<Rightarrow> dynamic list \<Rightarrow> bool" where
  "isinl OpAddNum [DNum _, DNum _]" |
  "isinl OpMulNum [DNum _, DNum _]"

fun deinl :: "opinl \<Rightarrow> op" where
  "deinl OpAddNum = OpAdd" |
  "deinl OpMulNum = OpMul"

lemma inl_inj: "inj inl"
  unfolding inj_def
proof (intro allI impI)
  fix x y
  assume "inl x = inl y"
  thus "x = y"
    unfolding fun_eq_iff
    by (cases x; cases y; auto elim: inl.elims simp: HOL.eq_commute[of None])
qed

lemma inl_invertible: "inl op xs = Some opinl \<Longrightarrow> deinl opinl = op"
  by (induction op xs rule: inl.induct; simp)

fun eval_AddNum :: "dynamic list \<Rightarrow> dynamic" where
  "eval_AddNum [DNum x, DNum y] = DNum (x + y)" |
  "eval_AddNum [DBool x, DBool y] = DBool (x \<or> y)" |
  "eval_AddNum [_, _] = DNil"

fun eval_MulNum :: "dynamic list \<Rightarrow> dynamic" where
  "eval_MulNum [DNum x, DNum y] = DNum (x * y)" |
  "eval_MulNum [DBool x, DBool y] = DBool (x \<and> y)" |
  "eval_MulNum [_, _] = DNil"

fun eval_inl :: "opinl \<Rightarrow> dynamic list \<Rightarrow> dynamic" where
  "eval_inl OpAddNum = eval_AddNum" |
  "eval_inl OpMulNum = eval_MulNum"

lemma eval_AddNum_correct:
  "length xs = 2 \<Longrightarrow> eval_AddNum xs = eval_Add xs"
  by (induction xs rule: eval_AddNum.induct; simp)

lemma eval_MulNum_correct:
  "length xs = 2 \<Longrightarrow> eval_MulNum xs = eval_Mul xs"
  by (induction xs rule: eval_MulNum.induct; simp)

lemma eval_inl_correct:
  "length xs = ar (deinl opinl) \<Longrightarrow> eval_inl opinl xs = eval (deinl opinl) xs"
  using eval_AddNum_correct eval_MulNum_correct
  by (cases opinl; simp)

lemma inl_isinl:
  "inl op xs = Some opinl \<Longrightarrow> isinl opinl xs"
  by (induction op xs rule: inl.induct; auto intro: isinl.intros)

interpretation op_OpInl: nary_operations_inl eval ar eval_inl inl isinl deinl
  using inl_invertible
  using eval_inl_correct
  using inl_isinl
  by (unfold_locales; simp)


section \<open>Unboxed operations\<close>

datatype opubx =
  OpAddNumUbx

fun ubx :: "opinl \<Rightarrow> type option list \<Rightarrow> opubx option" where
  "ubx OpAddNum [Some Ubx1, Some Ubx1] = Some OpAddNumUbx" |
  "ubx _ _ = None"

fun deubx :: "opubx \<Rightarrow> opinl" where
  "deubx OpAddNumUbx = OpAddNum"

lemma ubx_invertible: "ubx opinl xs = Some opubx \<Longrightarrow> deubx opubx = opinl"
  by (induction opinl xs rule: ubx.induct; simp)

fun eval_AddNumUbx :: "(dynamic, nat, bool) unboxed list \<Rightarrow> (dynamic, nat, bool) unboxed option" where
  "eval_AddNumUbx [OpUbx1 x, OpUbx1 y] = Some (OpUbx1 (x + y))" |
  "eval_AddNumUbx _ = None"

fun eval_ubx :: "opubx \<Rightarrow> (dynamic, nat, bool) unboxed list \<Rightarrow> (dynamic, nat, bool) unboxed option" where
  "eval_ubx OpAddNumUbx = eval_AddNumUbx"

lemma eval_ubx_correct:
  "eval_ubx opubx xs = Some z \<Longrightarrow>
    eval_inl (deubx opubx) (map unboxed_dynamic.norm_unboxed xs) = unboxed_dynamic.norm_unboxed z"
  apply (cases opubx; simp)
  apply (induction xs rule: eval_AddNumUbx.induct; auto)
  by (simp add: box_num_def)

lemma eval_ubx_to_inl:
  assumes "eval_ubx opubx \<Sigma> = Some z"
  shows "inl (deinl (deubx opubx)) (map unboxed_dynamic.norm_unboxed \<Sigma>) = Some (deubx opubx)"
proof (cases opubx)
  case OpAddNumUbx
  then have "eval_AddNumUbx \<Sigma> = Some z"
    using assms by simp
  then show ?thesis
    using OpAddNumUbx
    apply (induction \<Sigma> rule: eval_AddNumUbx.induct; simp)
    by (simp add: box_num_def)
qed


subsection \<open>Abstract interpretation\<close>

fun typeof_opubx :: "opubx \<Rightarrow> type option list \<times> type option" where
  "typeof_opubx OpAddNumUbx = ([Some Ubx1, Some Ubx1], Some Ubx1)"

lemma ubx_imp_typeof_opubx:
  "ubx opinl ts = Some opubx \<Longrightarrow> fst (typeof_opubx opubx) = ts"
  by (induction opinl ts rule: ubx.induct; simp)

lemma typeof_opubx_correct:
  "typeof_opubx opubx = (map typeof xs, codomain) \<Longrightarrow>
    \<exists>y. eval_ubx opubx xs = Some y \<and> typeof y = codomain"
proof (induction opubx)
  case OpAddNumUbx
  obtain n1 n2 where xs_def: "xs = [OpUbx1 n1, OpUbx1 n2]" and "codomain = Some Ubx1"
    using OpAddNumUbx[symmetric]
    by (auto dest!: typeof_unboxed_inversion)
  then show ?case by simp
qed

lemma typeof_opubx_complete:
  "eval_ubx opubx xs = Some y \<Longrightarrow>
    typeof_opubx opubx = (map typeof xs, typeof y)"
proof (induction opubx)
  case OpAddNumUbx
  then show ?case
    by (auto elim: eval_AddNumUbx.elims)
qed

lemma typeof_opubx_ar: "length (fst (typeof_opubx opubx)) = ar (deinl (deubx opubx))"
  by (induction opubx; simp)

interpretation op_OpUbx:
  nary_operations_ubx
    eval ar eval_inl inl isinl deinl
    is_true is_false box_num unbox_num box_bool unbox_bool
    eval_ubx ubx deubx typeof_opubx
  using ubx_invertible
  using eval_ubx_correct
  using eval_ubx_to_inl
  using ubx_imp_typeof_opubx
  using typeof_opubx_correct
  using typeof_opubx_complete
  using typeof_opubx_ar
  by (unfold_locales; (simp; fail)?)

end