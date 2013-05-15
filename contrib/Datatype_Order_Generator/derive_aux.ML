(* auxiliary functions which might be useful when deriving something for
   datatypes via recursors *)

signature DERIVE_AUX = 
sig 
  (* split_last [a,...,z] -> ([a,...,y],z) *)
  val split_last : 'a list -> 'a list * 'a
  
  (* p1 \<longrightarrow> p2 \<longrightarrow> \<dots> \<longrightarrow> p_n \<longrightarrow> r *)
  val HOLogic_list_implies : term list * term -> term

  (* p1 /\ ... /\ pn *)
  val HOLogic_list_conj : term list -> term

  (* \<forall> x1 ... xn . p *)
  val HOLogic_list_all : term list * term -> term
  
  (* rulifys P1 .. Pn in a thm P1 ==> ... ==> Pn ==> Q *)
  val rulify_only_asm : thm -> thm

  (* instantiates a thm for given terms of given sort *)
  val instantiate' : theory -> sort -> term list -> thm -> thm

(* takes a list of implications, an induction theorem, and a tactic to handle each case,
   and delivers the major implication.
   Example: if imp_list is [([p1 x y, q1 x y], [x,y]), ([p2 x' y', q2 x' y'], [x',y'])]
            and ind_thm is ... ==> P1 x /\ P2 x'
            then it encodes p1 x y ==> q1 x y &&& p2 x' y' ==> q2 x' y'
            which is converted to HOL (! y. p1 x y --> q1 x y) /\ (! y'. p2 x' y' --> q2 x' y')
            which is proven by the instantiated ind_thm where, e.g. P1 = % x. (! y. p1 x y --> q1 x y)
            and where in the IH all HOL-constructs are rulified again.
            As a result, only the first implication is returned: "p1 x y ==> q1 x y"
   Purpose: encountered problems with induct-tac
     - P1 and P2 are two large for internal unification, so they must be provided
     - if P1 and P2 are provided, then one has to use HOL-constructs (for arbitrary choice of y and y')
     - in induct_tac, then the IH are not converted to nice meta-implications/quantifications
*)
  val inductive_thm : theory -> (term list * term list) list -> thm -> sort -> 
      (*                idx    ih_hyps     ih_prems    case_vars    arbi_vars *)
      (Proof.context -> int -> thm list -> thm list -> term list -> term list -> tactic) -> thm

(* delivers a typ substitution which constrains all free type variables in datatype by sort *)
  val typ_subst_for_sort : theory -> Datatype_Aux.info -> sort -> typ -> typ

(* identity and number recursive occurrences of datatypes *)
  val dt_number_recs : Datatype.dtyp list -> int * (int * int) list

(* like print_tac, but is turned off by default to not exceed tracing limit *)
  val my_print_tac : string -> tactic 
end


structure Derive_Aux : DERIVE_AUX =
struct
open Datatype_Aux; open Datatype;

val printing = false
val my_print_tac = if printing then print_tac else (fn _ => Seq.single) 

fun split_last xs = (take (length xs - 1) xs, List.last xs)
fun strip_cases ctac = ctac #> Seq.map snd

(* FIXME: reconsolidate with similar functions in the Isabelle repository and move to HOLogic *)
fun HOLogic_list_implies (prems,r) = fold_rev (fn r => fn p => HOLogic.mk_imp (r,p)) prems r
fun HOLogic_list_conj [] = @{term true}
  | HOLogic_list_conj [x] = x
  | HOLogic_list_conj (x :: xs) = HOLogic.mk_conj (x, HOLogic_list_conj xs)
fun HOLogic_list_all (xs,p) = fold_rev (fn (x,ty) => fn p => HOLogic.mk_all (x,ty,p)) (map dest_Free xs) p

fun rulify_only_asm thm = 
  (@{thm conjI[OF TrueI]} OF [thm]) (* add conj to prohibit rulify in conclusion *)
  |> Object_Logic.rulify (* rulify everything, i.e., by preprocessing only the assms *)
  |> (fn conj => (@{thm conjunct2} OF [conj])) (* drop conjunction again *)

fun instantiate' thy sort vars thm = 
  let 
    val tvars = Thm.prop_of thm |> Term.add_tvars |> (fn x => x []) |> rev
    val inst_tvars = map (fn (n, _) => TFree (fst n,sort) |> ctyp_of thy |> SOME) tvars
    val cvars = map (cterm_of thy #> SOME) vars
  in 
    Drule.instantiate' inst_tvars cvars thm
  end

fun permute_for_ind_thm ps xs ind_thm =
  let 
    val n = length ps
    val vs_p = prop_of ind_thm |> Term.add_vars |> (fn f => f [] |> rev)
    fun number_ih_vars _ [] = []
      | number_ih_vars i (P :: x :: pxs) = ((P,i) :: (x,i+n) :: number_ih_vars (i+1) pxs)
      | number_ih_vars _ _ = error "odd number of vars in ind-thm"
    val vs_c = concl_of ind_thm |> Term.add_vars |> (fn f => f [] |> rev) |> number_ih_vars 0
    val permutation = map (AList.lookup (op =) vs_c #> the) vs_p
  in 
    map (nth (ps @ xs)) permutation 
  end


fun inductive_thm thy (imp_list : (term list * term list) list) ind_thm sort ind_tac = 
  let 
    val imps = map
      (fn (imps,xs) => HOLogic_list_all (tl xs, HOLogic_list_implies (split_last imps)))
      imp_list
    val ind_term = 
      HOLogic_list_conj imps
      |> HOLogic.mk_Trueprop
    val nr_prems = length (hd imp_list |> fst) - 1
    val nr_arbi = length (hd imp_list |> snd) - 1
    val xs = map (snd #> hd) imp_list
    val ps = xs ~~ imps 
      |> map (fn (x,imp) => lambda x imp)
    val insts = permute_for_ind_thm ps xs ind_thm      
    val ind_thm_inst = instantiate' thy sort insts ind_thm 
    val ind_thm' = rulify_only_asm ind_thm_inst
    val xs_strings = map (dest_Free #> fst) xs
    val conjunctive_thm = Goal.prove_global thy xs_strings [] ind_term 
      (fn {context = ctxt, ...} => 
        (
          (DETERM o strip_cases o Induct.induct_tac ctxt false [] [] [] (SOME [ind_thm']) [])
          THEN_ALL_NEW 
          (fn i => Subgoal.SUBPROOF
            (fn {context = ctxt, prems = prems, params = iparams, ...} => 
              let 
                val m = length prems - nr_prems
                val ih_prems = drop m prems
                val ih_hyps = take m prems
                val tparams = map (snd #> term_of) iparams
                val m' = length tparams - nr_arbi
                val arbi_vars = drop m' tparams
                val case_vars = take m' tparams
              in 
                ind_tac ctxt (i-1) ih_hyps ih_prems case_vars arbi_vars 
              end
            ) ctxt i
          )
        ) 1 
      )
    (* extract first conjunct *)
    val first_conj = if length imp_list > 1 then @{thm conjunct1} OF [conjunctive_thm] else conjunctive_thm 
    (* and replace \<longrightarrow> and \<forall> by meta-logic (for those \<longrightarrow> and \<forall> which have been constructed) *)
    val elim_spec = funpow nr_arbi (fn thm => @{thm spec} OF [thm]) first_conj
    val elim_imp = funpow nr_prems (fn thm => @{thm mp} OF [thm]) elim_spec
  in elim_imp end 

fun typ_subst_for_sort thy info sort =
  let 
    val spec = the_spec thy (#descr info |> hd |> (fn (_,(dty_name,_,_)) => dty_name))
    val typ_subst = Term.typ_subst_atomic (spec |> fst |> map (fn (n,s) => (TFree (n,s), TFree (n,sort)))) 
  in typ_subst end

fun dt_number_recs dtys = 
  let 
    fun dtrecs [] j = (j,[]) 
      | dtrecs (DtTFree _ :: dtys) j = dtrecs dtys j
      | dtrecs (DtRec i :: dtys) j = 
          let 
            val (j',ijs) = dtrecs dtys (j+1)
          in (j',(i,j) :: ijs) end
      | dtrecs (DtType (_,dtys1) :: dtys2) j = 
          let 
            val (j',ijs) = dtrecs dtys1 j
            val (j'',ijs') = dtrecs dtys2 j'
          in (j'',ijs @ ijs') end
  in dtrecs dtys 0
end

end
