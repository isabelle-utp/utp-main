fun println x = print (x ^ "\n")

fun file_to_string name = let
  val f = TextIO.openIn name
  val s = TextIO.inputAll f
  val _ = TextIO.closeIn f
in s end


fun print_help () = (
  println("c Usage: " ^ CommandLine.name() ^ "[<options>] <domain> <problem> [<plan>]");
  println("c Options:");
  println("c   --no-wf-checking     Do not check well-formedness.");
  println("c                        No guarantees if input not well-formed")
)

fun verify_plan dom prob plan = let
  val dom = file_to_string dom
  val prob = file_to_string prob
  val plan = file_to_string plan
  open PDDL_Checker_Exported
  val chkres = parse_check_dpp_impl dom prob plan
in
  case chkres of
    Inl msg => println ("s ERROR: " ^ msg)
  | Inr _ => println ("s VERIFIED")  
end

fun verify_plan_assum_wf dom prob plan = let
  val dom = file_to_string dom
  val prob = file_to_string prob
  val plan = file_to_string plan
  open PDDL_Checker_Exported
  val chkres = parse_check_p_impl dom prob plan
in
  case chkres of
    Inl msg => println ("s ERROR: " ^ msg)
  | Inr _ => println ("s (WELLFORMED ==> VERIFIED)")
end


fun check_dom_prob_wf dom prob = let
  val dom = file_to_string dom
  val prob = file_to_string prob
  open PDDL_Checker_Exported
  val chkres = parse_check_dp_impl dom prob
in
  case chkres of
    Inl msg => println ("s ERROR: " ^ msg)
  | Inr _ => println ("s WELLFORMED")  
end


fun 
    process_args [dom,prob] = check_dom_prob_wf dom prob
  | process_args [dom,prob,plan] = verify_plan dom prob plan
  | process_args ["--no-wf-checking",dom,prob,plan] = verify_plan_assum_wf dom prob plan
  | process_args _ = (
      println("s ERROR: Invalid command line arguments");
      print_help()
    )    

fun main () = let
  val args = CommandLine.arguments ();
in
  process_args args
end


val _ = if MLton.isMLton then main() else ()


