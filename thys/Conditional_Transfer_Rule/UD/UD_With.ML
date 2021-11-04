(* Title: UD/UD_With.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

Database for the storage of the theorems that provide a relationship 
between the overloaded constants and the unoverloaded constants. 
*)

signature UD_WITH =
sig

structure UDWithData: NAMED_THMS

end;

structure UD_With : UD_WITH =
struct

structure UDWithData = Named_Thms
  (
    val name = \<^binding>\<open>ud_with\<close>
    val description = "Unoverloaded definitions"
  );

end;