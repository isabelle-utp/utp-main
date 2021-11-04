fun println x = print (x ^ "\n")


fun print_help () = (
  println ("Usage: pactrim [option] <file.polys> <file.pac> <file.spec>\n" ^
           "    or pactrim --version\n" ^
           "\n" ^
           "Prints\n" ^
           "s SUCCESSFULL: if everything worked\n" ^
           "s FAILED, but correct PAC: if the PAC file is correct, but\n" ^
           "\tthe spec was not derived\n" ^
           "s PAC FAILED: if the PAC file is incorrect\n" ^
           "\n" ^
           "\n" ^
           "Option:\n" ^
           "--uloop (unsafe loop): use the non-verified loop instead of \n" ^
           "\tthe verified loop. This is faster because the file does not\n" ^
           "\t have to be parsed upfront.")
)

fun readfile istream =
    let val a = TextIO.inputLine istream
    in if a = NONE then [] else valOf a :: readfile istream
    end


fun print_poly [] = (print " + 0")
  | print_poly ((i, m) :: xs) =
    (print (IntInf.toString i ^" * ");
     map print m;
    print_poly xs)
fun print_input_poly (lbl, poly) =
    (println (Int.toString lbl); print_poly poly)

fun parse_polys_file file_name = let
  val istream = TextIO.openIn file_name
  val a = map (fn x =>
                  let val (lbl, poly) = x
                  in
                    (PAC_Checker.nat_of_integer lbl,
                         map (fn (a,b) => (a, PAC_Checker.Int_of_integer b)) poly)
                  end)
              (PAC_Parser.input_polys istream)
  val _ = TextIO.closeIn istream
in
  foldl (fn ((lbl, a), b) => PAC_Checker.pAC_update_impl lbl a b ()) (PAC_Checker.pAC_empty_impl ()) a
end

fun parse_pac_file file_name = let
  val istream = TextIO.openIn file_name
  val a = PAC_Parser.step_polys istream
  val _ = TextIO.closeIn istream
in
  a
end

fun parse_spec_file file_name = let
  val istream = TextIO.openIn file_name
  val poly = PAC_Parser.parse_polynom istream
  val _ = TextIO.closeIn istream
in
  map(fn (a,b) => (a, PAC_Checker.Int_of_integer b)) poly
end

fun print_stat polys_timer pac_timer end_of_init end_of_processing full =
  let
    fun print_timer d t = print ("c " ^ d ^ " (nonGC): " ^
          Time.toString (Time.+ (#usr (#nongc t), #sys (#nongc t))) ^ " s = " ^
          Time.toString (#usr (#nongc t)) ^ " s (usr) " ^
          Time.toString (#sys (#nongc t)) ^ " s (sys)\n");
    fun print_timer_GC d t = print ("c " ^ d ^ ": " ^
          Time.toString (Time.+ (#usr (#gc t), #sys (#gc t))) ^ " s = " ^
          Time.toString (#usr (#gc t)) ^ " s (usr) " ^
          Time.toString (#sys (#gc t)) ^ " s (sys)\n");
    fun print_full_timer d t = print ("c " ^ d ^ "(full): " ^
                                      Time.toString (Time.+(Time.+ (#usr (#gc t), #sys (#gc t)),
                                                      (Time.+ (#usr (#nongc t), #sys (#nongc t))))) ^ " s\n" );
    val clock = Time.toSeconds (#usr (#nongc end_of_processing)) + Time.toSeconds (#sys (#nongc end_of_processing));
     val _ = print "c\nc\nc ***** stats *****\n"
     val _ = print_timer "parsing polys file init" polys_timer
     val _ = print_timer "parsing pac file init" pac_timer
     val _ = print_timer "full init" end_of_init
     val _ = print_timer "time solving" end_of_processing
     val _ = print_timer_GC "time GC" end_of_processing
     val _ = print_full_timer "time solving" end_of_processing
     val _ = print_timer "Overall" full
     val _ = print_timer_GC "overall GC" full
     val _ = print_full_timer "Overall" full
  in
   ()
  end

fun first (a, b) = a
fun second (a, b) = b

fun inside_loop [polys, pac, spec] =
    let
      val init_timer = Timer.startCPUTimer ();
      val problem = parse_polys_file polys;
      val polys_timer = Timer.checkCPUTimes init_timer;
      val timer = Timer.startCPUTimer ();
      val _ = println "c polys parsed\nc ******************"
      val timer = Timer.startCPUTimer ();
      val (spec0 : ((string list * PAC_Checker.int) list)) = parse_spec_file spec;
      val _ = println "c spec parsed";
      val end_of_init = Timer.checkCPUTimes init_timer;
      val timer = Timer.startCPUTimer ();
      val _ = println "c Now checking";
      val spec = PAC_Checker.fully_normalize_poly_impl spec0 ();
      val vars = PAC_Checker.empty_vars_impl ();
      val (b, (vars, polys)) = PAC_Checker.remap_polys_l_impl spec vars problem ();
      val vars = PAC_Checker.union_vars_poly_impl spec0 vars ()
      val state = ref (b, (vars, polys))
      val istream = TextIO.openIn pac
      val _ =
          while (TextIO.lookahead(istream) <> NONE andalso PAC_Checker.is_cfailed (first (!state)) = false)
                do
                let
                  val st = PAC_Parser.parse_step istream;
                  val (b, (vars, a)) = !state;
                in
                  state := PAC_Checker.check_step_impl spec b vars a st ()
                end;
      val (b, _) = !state;
      val _ = if PAC_Checker.is_cfound b then println "s SUCCESSFULL"
              else if (PAC_Checker.is_cfailed b) = false then println "s FAILED, but correct PAC"
              else (println "s PAC FAILED"; println (PAC_Checker.implode (PAC_Checker.the_error b)))
      val end_of_processing = Timer.checkCPUTimes timer
      val full = Timer.checkCPUTimes init_timer
  val _ = print_stat polys_timer polys_timer end_of_init end_of_processing full
    in ()
    end

fun checker [polys, pac, spec] = let
  val init_timer = Timer.startCPUTimer ();
  val problem = parse_polys_file polys;
  val polys_timer = Timer.checkCPUTimes init_timer;
  val timer = Timer.startCPUTimer ();
  val _ = println "c polys parsed\nc ******************"
  val pac : (((string list * PAC_Checker.int) list, string, Uint64.uint64) PAC_Checker.pac_step) list = parse_pac_file pac;
(*  val _ = MLton.share pac; *)
  val _ = println "c pac parsed"
  val pac_timer = Timer.checkCPUTimes timer;
  val timer = Timer.startCPUTimer ();
  val (spec : ((string list * PAC_Checker.int) list)) = parse_spec_file spec;
  val _ = println "c spec parsed";
  val end_of_init = Timer.checkCPUTimes init_timer;
  val timer = Timer.startCPUTimer ();
  val _ = println "c Now checking";
  val (b, _) = PAC_Checker.full_checker_l_impl spec problem pac ();
  val _ = if PAC_Checker.is_cfound b then println "s SUCCESSFULL"
          else if (PAC_Checker.is_cfailed b) = false then println "s FAILED, but correct PAC"
          else (println "s PAC FAILED"; println (PAC_Checker.implode (PAC_Checker.the_error b)))
  val end_of_processing = Timer.checkCPUTimes timer
  val full = Timer.checkCPUTimes init_timer
  val _ = print_stat polys_timer pac_timer end_of_init end_of_processing full
  in
    ()
end
  handle PAC_Parser.Parser_Error err => print("parsing failed with error: " ^ err)

fun process_args [arg, polys, pac, spec] =
    if arg = "--iloop" orelse arg = "--uloop"
    then inside_loop [polys, pac, spec]
    else print_help()
  | process_args [polys, pac, spec] =
    checker [polys, pac, spec]
  | process_args [arg] =
    if arg = "--version" orelse arg = "-v" orelse arg = "-version"
    then println (PAC_Checker.version)
    else print_help()
  | process_args [] = print_help()

fun main () = let
  val args = CommandLine.arguments ();
in
  process_args args
end


val _ = if MLton.isMLton then main() else ()
