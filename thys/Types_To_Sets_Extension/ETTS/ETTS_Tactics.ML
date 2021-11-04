(* Title: ETTS/ETTS_Tactics.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

Implementation of the tactics for the ETTS.
*)

signature ETTS_TACTICS =
sig
val cond_red_tac : 
  Proof.context ->
  term ->
  (Proof.context -> tactic) ->
  thm -> 
  int -> 
  tactic
val id_tac : thm -> int -> tactic
val prem_red : 
  Proof.context -> (term list * (Proof.context -> tactic)) -> thm -> thm
end;

structure ETTS_Tactics : ETTS_TACTICS =
struct                                           

(*an identity tactic*)
fun id_tac assm_thm i = 
  let fun id_tac_impl assm_thm thm = Thm.implies_elim thm assm_thm;
  in SELECT_GOAL (PRIMITIVE (id_tac_impl assm_thm)) i end;

(*a tactic for the elimination of the first premise using a 
user-defined tactic*)
fun cond_red_tac ctxt condt cond_tac thm i =
  Induct.cases_tac ctxt false ((SOME condt) |> single |> single) NONE [] i
  THEN Local_Defs.unfold_tac ctxt (single @{thm not_not})
  THEN SOLVED' 
    (
      SUBPROOF 
        (
          fn {context, prems, ...} => 
            Method.insert_tac context prems 1 
            THEN (cond_tac context)
        ) 
        ctxt
    ) 
    i
  THEN id_tac thm i;

(*automated elimination of premises*)
fun prem_red ctxt tac_spec thm = 
  let

    fun rotate_prems_once thm = Drule.rotate_prems 1 thm
      handle THM _ => thm
    val aterms = #1 tac_spec

    fun prem_red_rec thm condn = 
      let                      
        val prems = Thm.prems_of thm 
        val condt_opt = 
          let
            fun pass_through_spec t = 
              if null aterms orelse member Term.could_unify aterms t  
              then t 
              else raise TERM ("", [])
          in
            prems 
            |> hd
            |> HOLogic.dest_Trueprop
            |> pass_through_spec
            |> HOLogic.mk_not
            |> SOME
            handle 
                TERM _ => NONE
              | Empty => NONE
          end;
        val thm' = rotate_prems_once thm
        val thm'' = case condt_opt of
          SOME condt =>
            let val goalt = Logic.list_implies (tl prems, (Thm.concl_of thm))
            in
              Goal.prove 
                ctxt 
                [] 
                [] 
                goalt 
                (cond_red_tac ctxt condt (#2 tac_spec) thm' 1 |> K)
              handle 
                  ERROR _ => thm'
                | THM _ => thm'
            end
          | NONE => thm'
        val success_flag = 
          not (Thm.full_prop_of thm'' = Thm.full_prop_of thm')
      in
        if success_flag
        then prem_red_rec thm'' (condn - 1)
        else if condn > 1 then prem_red_rec thm' (condn - 1) else thm
      end

    val thm = Local_Defs.unfold ctxt (single @{thm not_not}) thm
    val condn = thm |> Thm.prems_of |> length
    val out_thm = rotate_prems_once (prem_red_rec thm condn) 

  in out_thm end;

end;