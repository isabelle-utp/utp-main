theory utp_solve_tac
imports utp_alpha_tac utp_poly_tac
begin

ML {*
  fun utp_solve_simpset ctxt =
    ctxt
      addsimps (evala.get ctxt)
      addsimps (evalp.get ctxt)
      addsimps (evalpp.get ctxt)
      addsimps (closure.get ctxt)
      (* Closure alone seems not enough e.g. to simplify (p1 \<or>\<alpha> p2) \<sqsubseteq> p2. *)
      addsimps (alphabet.get ctxt)
      addsimps (typing.get ctxt)
      addsimps (defined.get ctxt)
      addsimps (unrest.get ctxt)
      addsimps @{thms var_dist}
      addsimps @{thms alphabet_dist};
*}

ML {*
  fun utp_solve_tac thms ctxt i =
    CHANGED (asm_full_simp_tac (utp_alpha_simpset ctxt) i)
*}

method_setup utp_solve = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_solve_tac thms ctxt))
*} "proof tactic for alphabetised predicates"

end
