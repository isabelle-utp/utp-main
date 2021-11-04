(* Title: UD/UD_Consts.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

The following infrastructure allows for the exclusion of arbitrary 
constants from being unoverloaded during the invocation of the
algorithm associated with the UD.
*)

signature UD_CONSTS =
sig

structure ConstsData : THEORY_DATA
val const_of_key : theory -> Symtab.key -> term option
val update_const : Symtab.key -> term -> theory -> theory
val remove_const : Symtab.key -> theory -> theory
val get_keys : theory -> Symtab.key list

end;

structure UD_Consts : UD_CONSTS =
struct

structure ConstsData = Theory_Data 
  (
    type T = term Symtab.table
    val empty = Symtab.empty
    val extend = I
    val merge = Symtab.merge (K true)
  )
val const_of_key = Symtab.lookup o ConstsData.get
fun update_const k v = ConstsData.map (Symtab.update (k, v))
fun remove_const k = ConstsData.map (Symtab.delete k)
val get_keys = Symtab.keys o ConstsData.get

end;