theory utp_solve_tac
imports utp_alpha_tac "../poly/utp_poly_tac"
begin

ML {*
  fun utp_solve_alpha_simps ctxt =
    ctxt
      addsimps (alphabet.get ctxt)
      addsimps (typing.get ctxt)
      addsimps (defined.get ctxt)
      addsimps (unrest.get ctxt)
      addsimps @{thms var_dist}
      addsimps @{thms alphabet_dist};
*}      

ML {*
  fun utp_solve_evala_simps ctxt =
    ctxt
      addsimps (evala.get ctxt)
      addsimps (typing.get ctxt)
      addsimps (defined.get ctxt)
      addsimps (unrest.get ctxt);
*}      

ML {*
  fun utp_solve_simpset ctxt =
    ctxt
      addsimps (evalp.get ctxt)
      addsimps (evalpp.get ctxt)
      addsimps (closure.get ctxt)
      addsimps (alphabet.get ctxt)
      addsimps (typing.get ctxt)
      addsimps (defined.get ctxt)
      addsimps (unrest.get ctxt);
*}

ML {*
  fun utp_solve_tac thms ctxt i =
    (rtac @{thm EvalA_intro} i ORELSE rtac @{thm EvalA_TautologyA_intro} i ORELSE rtac @{thm EvalA_RefineA_intro} i) 
    THEN (SELECT_GOAL (auto_tac (utp_solve_alpha_simps ctxt)) i)
    THEN TRY (asm_full_simp_tac (utp_solve_evala_simps ctxt) i)
    THEN TRY (rtac @{thm EvalP_intro} i ORELSE rtac @{thm EvalP_Tautology_intro} i ORELSE rtac @{thm EvalP_RefineP_intro} i)
    THEN TRY (asm_full_simp_tac (utp_solve_simpset ctxt) i)
    THEN TRY (SELECT_GOAL (auto_tac ctxt) i)
*}

method_setup utp_solve = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_solve_tac thms ctxt))
*} "proof tactic for alphabetised predicates"

end
