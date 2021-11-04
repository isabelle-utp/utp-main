signature CS_UM =
sig

val match_inst_rec :
  (thm -> term) ->
  (thm -> bool) ->
  Proof.context ->
  thm ->
  term ->
  Envir.env list ->
  thm list

val match_inst_list :
  (thm -> term) ->
  (thm -> bool) ->
  Proof.context ->
  thm ->
  term ->
  Envir.env list ->
  thm list

val match_inst :
  (
    (thm -> term) ->
    (thm -> bool) ->
    Proof.context ->
    thm ->
    term ->
    Envir.env list ->
    thm list
  ) ->
  (thm -> term) ->
  (thm -> bool) ->
  Proof.context ->
  thm ->
  term ->
  thm list

end;

structure CS_UM: CS_UM =
struct

local

fun prep_trm ctxt (x, (T, t)) = ((x, T), Thm.cterm_of ctxt t);
fun prep_ty ctxt (x, (S, ty)) = ((x, S), Thm.ctyp_of ctxt ty);

fun um_inst ctxt thm env =
  let
    val tenv = Vartab.dest (Envir.term_env env)
    val tyenv = Vartab.dest (Envir.type_env env)
    val inst = (map (prep_ty ctxt) tyenv, map (prep_trm ctxt) tenv)
  in 
    thm
    |> Drule.instantiate_normalize inst
    |> Drule.eta_contraction_rule
  end;

fun um_inst_rec _ _ _ _ _ _ [] = []
  | um_inst_rec cond pat_fun is_trivial ctxt thm trm (env::envs) =
      let val thm' = um_inst ctxt thm env
      in 
        if cond pat_fun is_trivial thm' trm
        then single thm'
        else um_inst_rec cond pat_fun is_trivial ctxt thm trm envs
      end;

fun um_inst_list cond pat_fun is_trivial ctxt thm trm envs =
  let
    fun um_inst_rec_single env =
      let val thm' = um_inst ctxt thm env
      in
        if cond pat_fun is_trivial thm' trm
        then single thm'
        else []
      end
    val thms = envs |> map um_inst_rec_single |> flat
  in thms end;

fun match_cond pat_fun is_trivial thm' trm =
  (pat_fun thm') aconv trm andalso not (is_trivial thm');

in

(*
The implementation of the following functions incorporates elements of the code 
from the textbook 
"The Isabelle Cookbook: A Gentle Tutorial for Programming Isabelle/ML".
*)
val match_inst_rec = um_inst_rec match_cond;
val match_inst_list = um_inst_list match_cond;
fun match_inst match_inst_impl pat_fun is_trivial ctxt thm trm =
  let
    val univ = Unify.matchers (Context.Proof ctxt) [(pat_fun thm, trm)]
    val envs = Seq.list_of univ
  in match_inst_impl pat_fun is_trivial ctxt thm trm envs end;

end;

end;