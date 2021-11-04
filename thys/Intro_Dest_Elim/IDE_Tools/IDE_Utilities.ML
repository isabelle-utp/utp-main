(* Copyright 2021 (C) Mihails Milehins *)

signature IDE_UTILITIES =
sig

val thm_printer : Proof.context -> bool -> string -> thm list -> unit

end;

structure IDE_Utilities : IDE_UTILITIES =
struct

(* standard theorem printer *)
fun thm_printer ctxt print name thms = 
  Proof_Display.print_results 
    print 
    (Position.thread_data ()) 
    ctxt 
    ((Thm.theoremK, ""), single (name, thms));

end;