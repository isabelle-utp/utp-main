theory Unboxed
  imports Global Dynamic
begin

datatype type = Ubx1 | Ubx2

datatype ('dyn, 'ubx1, 'ubx2) unboxed =
  is_dyn_operand: OpDyn 'dyn |
  OpUbx1 'ubx1 |
  OpUbx2 'ubx2

fun typeof where
  "typeof (OpDyn _) = None" |
  "typeof (OpUbx1 _) = Some Ubx1" |
  "typeof (OpUbx2 _) = Some Ubx2"

fun cast_Dyn where
  "cast_Dyn (OpDyn d) = Some d" |
  "cast_Dyn _ = None"

fun cast_Ubx1 where
  "cast_Ubx1 (OpUbx1 x) = Some x" |
  "cast_Ubx1 _ = None"

fun cast_Ubx2 where
  "cast_Ubx2 (OpUbx2 x) = Some x" |
  "cast_Ubx2 _ = None"

locale unboxedval = dynval is_true is_false
  for is_true :: "'dyn \<Rightarrow> bool" and is_false +
  fixes
    box_ubx1 :: "'ubx1 \<Rightarrow> 'dyn" and unbox_ubx1 :: "'dyn \<Rightarrow> 'ubx1 option" and
    box_ubx2 :: "'ubx2 \<Rightarrow> 'dyn" and unbox_ubx2 :: "'dyn \<Rightarrow> 'ubx2 option"
  assumes
    box_unbox_inverse:
      "unbox_ubx1 d = Some u1 \<Longrightarrow> box_ubx1 u1 = d"
      "unbox_ubx2 d = Some u2 \<Longrightarrow> box_ubx2 u2 = d"
begin

fun unbox :: "type \<Rightarrow> 'dyn \<Rightarrow> ('dyn, 'ubx1, 'ubx2) unboxed option"  where
  "unbox Ubx1 = map_option OpUbx1 \<circ> unbox_ubx1" |
  "unbox Ubx2 = map_option OpUbx2 \<circ> unbox_ubx2"

fun cast_and_box where
  "cast_and_box Ubx1 = map_option box_ubx1 \<circ> cast_Ubx1" |
  "cast_and_box Ubx2 = map_option box_ubx2 \<circ> cast_Ubx2"

fun norm_unboxed where
  "norm_unboxed (OpDyn d) = d" |
  "norm_unboxed (OpUbx1 x) = box_ubx1 x" |
  "norm_unboxed (OpUbx2 x) = box_ubx2 x"

fun box_operand where
  "box_operand (OpDyn d) = OpDyn d" |
  "box_operand (OpUbx1 x) = OpDyn (box_ubx1 x)" |
  "box_operand (OpUbx2 x) = OpDyn (box_ubx2 x)"

fun box_frame where
  "box_frame f (Frame g pc \<Sigma>) = Frame g pc (if f = g then map box_operand \<Sigma> else \<Sigma>)"

definition box_stack where
  "box_stack f \<equiv> map (box_frame f)"

end

end