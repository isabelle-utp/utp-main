(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: remove_duplicates.thy                                                *)
(* Authors: Frank Zeyda (Teesside, UK) & Simon Foster (York, UK)              *)
(******************************************************************************)
(* LAST REVIEWED: 30 July 2015 *)

section {* Remove Duplicates in Sets *}

theory remove_duplicates
imports Main
begin

text {* Conversion and tactic to remove duplicate elements in sets. *}

subsection {* Conversion *}

ML {*
  fun remove_duplicates_set term =
    let val elems = distinct (op =) (HOLogic.dest_set term) in
      (HOLogic.mk_set (HOLogic.dest_setT (type_of term)) elems)
    end;

  local
  val remove_duplicates_conv_thm =
    Drule.cterm_fun (fn term => HOLogic.mk_Trueprop
      (HOLogic.mk_eq (term, remove_duplicates_set term)));
  in
  fun remove_duplicates_conv cterm =
    let
      val thy = Thm.theory_of_cterm cterm;
      val ctx = Proof_Context.init_global thy;
      val tac = Clasimp.auto_tac ctx;
      val goal = (remove_duplicates_conv_thm cterm);
    in
      Conv.rewr_conv (Local_Defs.meta_rewrite_rule ctx
        (Goal.prove ctx [] [] (Thm.term_of goal) (K tac))) cterm
    end;
  end;
*}

subsection {* Rule and Tactic *}

ML {*
  fun remove_duplicates_rule ctx =
    Conv.fconv_rule
      (Conv.top_conv (K (Conv.try_conv remove_duplicates_conv)) ctx);

  fun remove_duplicates_tac ctx =
    CONVERSION
      (Conv.top_conv (K (Conv.try_conv remove_duplicates_conv)) ctx);
*}

subsection {* Proof Method Setup *}

setup {*
  (Method.setup @{binding remove_duplicates}
    (Scan.succeed (SIMPLE_METHOD' o remove_duplicates_tac))
    "remove duplicate elements in sets")
*}

subsection {* Experiments *}

ML {*
  val t1 = @{cterm "{1, 2, 1, 5, 4, 3, 2, 3, 2} = (X::nat set)"};
  val t2 = @{cterm "{1, 2, 1, 5, 4, 3, 2, 3, 2} = X"};
  val t3 = @{cterm "{x, y, z, x} = X"};
*}

ML {*
  (* Note that for the 2nd case to work, we require Conv.rewr_conv above. *)
  (Conv.top_conv (K (Conv.try_conv remove_duplicates_conv)) @{context}) t1;
  (Conv.top_conv (K (Conv.try_conv remove_duplicates_conv)) @{context}) t2;
  (Conv.top_conv (K (Conv.try_conv remove_duplicates_conv)) @{context}) t3;
*}

ML {*
  (* Note that dest_set and our converserion only works for "closed" sets. *)
  val t1 = @{term "insert (1::nat) (insert (2::nat) {})"};
  val t2 = @{term "insert (1::nat) (insert (2::nat) S)"};
  HOLogic.dest_set t1;
  (* HOLogic.dest_set t2; *)
*}
end
