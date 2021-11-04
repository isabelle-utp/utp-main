theory Unboxed_lemmas
  imports Unboxed
begin

lemma typeof_bind_OpDyn[simp]: "typeof \<circ> OpDyn = (\<lambda>_. None)"
  by auto

lemma is_dyn_operand_eq_typeof: "is_dyn_operand = (\<lambda>x. typeof x = None)"
proof (intro ext)
  fix x
  show "is_dyn_operand x = (typeof x = None)"
    by (cases x; simp)
qed

lemma is_dyn_operand_eq_typeof_Dyn[simp]: "is_dyn_operand x \<longleftrightarrow> typeof x = None"
  by (cases x; simp)

lemma typeof_unboxed_eq_const:
  fixes x
  shows
    "typeof x = None \<longleftrightarrow> (\<exists>d. x = OpDyn d)"
    "typeof x = Some Ubx1 \<longleftrightarrow> (\<exists>n. x = OpUbx1 n)"
    "typeof x = Some Ubx2 \<longleftrightarrow> (\<exists>b. x = OpUbx2 b)"
  by (cases x; simp)+

lemmas typeof_unboxed_inversion = typeof_unboxed_eq_const[THEN iffD1]

lemma cast_inversions:
  "cast_Dyn x = Some d \<Longrightarrow> x = OpDyn d"
  "cast_Ubx1 x = Some n \<Longrightarrow> x = OpUbx1 n"
  "cast_Ubx2 x = Some b \<Longrightarrow> x = OpUbx2 b"
  by (cases x; simp)+

lemma traverse_cast_Dyn_replicate:
  assumes "traverse cast_Dyn xs = Some ys"
  shows "map typeof xs = replicate (length xs) None"
  using assms
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  from Cons.prems show ?case
    by (auto intro: Cons.IH dest: cast_inversions(1) simp add: bind_eq_Some_conv)
qed

context unboxedval begin

lemma unbox_typeof[simp]: "unbox \<tau> d = Some blob \<Longrightarrow> typeof blob = Some \<tau>"
  by (cases \<tau>; auto)

lemma cast_and_box_imp_typeof[simp]: "cast_and_box \<tau> blob = Some d \<Longrightarrow> typeof blob = Some \<tau>"
  using cast_inversions[of blob]
  by (induction \<tau>; auto dest: cast_inversions[of blob])

lemma norm_unbox_inverse[simp]: "unbox \<tau> d = Some blob \<Longrightarrow> norm_unboxed blob = d"
  using box_unbox_inverse
  by (cases \<tau>; auto)

lemma norm_cast_and_box_inverse[simp]:
  "cast_and_box \<tau> blob = Some d \<Longrightarrow> norm_unboxed blob = d"
  by (induction \<tau>; auto elim: cast_Dyn.elims cast_Ubx1.elims cast_Ubx2.elims)

lemma typeof_and_norm_unboxed_imp_cast_and_box:
  assumes "typeof x' = Some \<tau>" "norm_unboxed x' = x"
  shows "cast_and_box \<tau> x' = Some x"
  using assms
  by (induction \<tau>; induction x'; simp)

lemma norm_unboxed_bind_OpDyn[simp]: "norm_unboxed \<circ> OpDyn = id"
  by auto

lemmas box_stack_Nil[simp] = list.map(1)[of "box_frame f" for f, folded box_stack_def]
lemmas box_stack_Cons[simp] = list.map(2)[of "box_frame f" for f, folded box_stack_def]

lemma typeof_box_operand[simp]: "typeof (box_operand x) = None"
  by (cases x; simp)

lemma is_dyn_box_operand: "is_dyn_operand (box_operand x)"
  by (cases x) simp_all

lemma is_dyn_operand_comp_box_operand[simp]: "is_dyn_operand \<circ> box_operand = (\<lambda>_. True)"
  using is_dyn_box_operand by auto

lemma norm_box_operand[simp]: "norm_unboxed (box_operand x) = norm_unboxed x"
  by (cases x) simp_all

end

end