(*<*)

theory Concrete_heap
imports
  "HOL-Library.Saturated"
  "../Global_Invariants"
begin

(* From 40e16c534243 by Makarius. Doesn't seem to have a huge impact on run time now (2021-01-07) *)
declare subst_all [simp del] [[simproc del: defined_all]]

(*>*)
type_synonym field = "3"
type_synonym mut = "2"
type_synonym payload = "unit"
type_synonym ref = "5"

type_synonym concrete_local_state = "(field, mut, payload, ref) local_state"
type_synonym clsts = "(field, mut, payload, ref) lsts"

abbreviation mut_common_init_state :: concrete_local_state where
  "mut_common_init_state \<equiv> undefined\<lparr> ghost_hs_phase := hp_IdleMarkSweep, ghost_honorary_grey := {}, ghost_honorary_root := {}, roots := {}, W := {} \<rparr>"

context gc_system
begin

abbreviation sys_init_heap :: "ref \<Rightarrow> (field, payload, ref) object option" where
  "sys_init_heap \<equiv>
  [   0 \<mapsto> \<lparr> obj_mark = initial_mark,
             obj_fields = [ 0 \<mapsto> 5 ],
             obj_payload = Map.empty \<rparr>,
      1 \<mapsto> \<lparr> obj_mark = initial_mark,
             obj_fields = Map.empty,
             obj_payload = Map.empty \<rparr>,
      2 \<mapsto> \<lparr> obj_mark = initial_mark,
             obj_fields = Map.empty,
             obj_payload = Map.empty \<rparr>,
      3 \<mapsto> \<lparr> obj_mark = initial_mark,
             obj_fields = [ 0 \<mapsto> 1 , 1 \<mapsto> 2 ],
             obj_payload = Map.empty \<rparr>,
      4 \<mapsto> \<lparr> obj_mark = initial_mark,
             obj_fields = [ 1 \<mapsto> 0 ],
             obj_payload = Map.empty \<rparr>,
      5 \<mapsto> \<lparr> obj_mark = initial_mark,
             obj_fields = Map.empty,
             obj_payload = Map.empty \<rparr>
  ]"

abbreviation mut_init_state0 :: concrete_local_state where
  "mut_init_state0 \<equiv> mut_common_init_state \<lparr> roots := {1, 2, 3} \<rparr>"

abbreviation mut_init_state1 :: concrete_local_state where
  "mut_init_state1 \<equiv> mut_common_init_state \<lparr> roots := {3} \<rparr>"

abbreviation mut_init_state2 :: concrete_local_state where
  "mut_init_state2 \<equiv> mut_common_init_state \<lparr> roots := {2, 5} \<rparr>"

end
(*<*)

end
(*>*)
