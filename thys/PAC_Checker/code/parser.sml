structure PAC_Parser =
struct
(*
fun hashList hashA l = 
    case l
     of nil => 0wx0
      | [a] => 0w1 + hashA a
      | a1::a2::_ => 0w2 + 0w3853 * hashA a1 + 0wx1327 * hashA a2
val hashChar = Word.fromInt o ord

fun hashString s =
    let val res = ref 0wx0;
        val i = ref 0;
    in
      while !i < String.size s
      do
      (res := !res + hashChar (String.sub(s,!i));
       res := !res * 0wx3853;
       i := !i+1);
      !res
    end


val hash : (string list, string list) HashTable.t ref = ref (HashTable.new {hash = hashList hashString, equals = op=});
val hashvar : (string, string) HashTable.t ref = ref (HashTable.new {hash = hashString, equals = op=});
val num_vars = ref 0;

fun share_var t =
    case HashTable.peek (!hashvar, t) of
        SOME t => t
      | NONE =>
        let val new = Int.toString (!num_vars) in
          (num_vars := 1 + !num_vars;
           ignore (HashTable.insertIfNew(!hashvar, t, fn () => new, ignore));
           new)
        end


fun share_term t =
    case HashTable.peek (!hash, t) of
        SOME t => t
      | NONE => 
        (case t of
             [] => []
           | x :: xs =>
             (let
               val xs' = share_term xs;
               val x = share_var x; 
              in
                ignore (HashTable.insertIfNew(!hash, t, fn () => x::xs, ignore));
                x :: xs'
              end
        ));


val share_term = map share_var;
*)

val share_var = fn x => x
val share_term = fn x => x;

                                                            
exception Parser_Error of string

  fun is_digit c = c >= #"0" andalso c <= #"9";
  fun is_zero c = (c = #"0");
  fun digit_of_char c = Char.ord c - Char.ord #"0";

  fun is_alpha c =
      c >= #"a" andalso c <= #"z"
      orelse c >= #"A" andalso c <= #"Z";

  fun is_space c =
      c = #" " orelse c = #"\t" orelse c = #"\n" orelse c = #"\r";

  fun is_separator c =
      c = #"*" orelse c = #"," orelse c = #";" orelse c = #"+" orelse c = #"-";

  fun print2 a = ();
  fun rev2 a = rev a;

  fun skip_spaces istream =
      (print2 "skip space";
       if TextIO.lookahead(istream) = SOME #" "
      then (TextIO.input1(istream); skip_spaces istream)
      else ())


  (* string_num is a very imperative to do the parser. We use is for 'string' until we need real
  'strings'. Once we need them (to convert them to a number), we convert them via slices.

   Compared to a string, it could also avoid allocating memory, although that does not seem to
   happen.
  *)
  val resizable_str = ref (ArraySlice.slice(Array.tabulate (10, fn _ => #" "), 0, NONE));
  fun double_string_size () =
      let
        fun new_val c =  if c >= ArraySlice.length (!resizable_str) then #" " else ArraySlice.sub(!resizable_str, c)
        val c = ArraySlice.slice(Array.tabulate(2*ArraySlice.length (!resizable_str), new_val),0,NONE)
      in
        resizable_str := c
      end
  fun extract (arr, s, l) = ArraySlice.vector (ArraySlice.subslice (arr, s, l))
  fun parse_natural istream =
      let
        val _ = print2 "parse_number\n"
        val i = ref (0);
        val seen_one_digit = ref false;
        fun parse_aux () =
            let val c = TextIO.lookahead istream
            in
              if (is_space (valOf c) orelse is_separator (valOf c) orelse not (is_digit (valOf c)))
              then (print2 ("number sep = '" ^ String.implode [(valOf c)] ^"'"))
              else
                case TextIO.input1(istream) of
                    NONE => raise Parser_Error "no number found"
                  | SOME c =>
                    ( (*print2 (String.implode [c] ^ " to be put at position" ^ Int.toString (!i));*)
                     seen_one_digit := true;
                     if !i < ArraySlice.length (!resizable_str) - 1
                     then () else double_string_size ();
                     ArraySlice.update(!resizable_str, !i, c);
                     i := !i + 1;
                     parse_aux ())
            end
      in
        (parse_aux ();
         if !seen_one_digit = false
         then raise Parser_Error ("no number digit")
         else
           (print2 (extract(!resizable_str, 0, SOME (!i)) ^"\n");
            (valOf (IntInf.fromString ((extract(!resizable_str, 0, SOME (!i))))))))
      end

  fun parse_nat istream =
      let
        val _ = print2 "parse_nat\n"
        val num = ref 0;
        val seen_one_digit = ref false;
        fun parse_aux () =
            let val c = TextIO.lookahead istream
            in
              if (is_space (valOf c) orelse is_separator (valOf c))
              then (print2 ("number sep = '" ^ String.implode [(valOf c)] ^ "'"))
              else
                case TextIO.input1(istream) of
                    NONE => raise Parser_Error "no number found"
                  | SOME c =>
                    if is_digit c
                    then (seen_one_digit := true;
                          num := !num* 10 + digit_of_char c;
                          parse_aux ())
                    else raise Parser_Error ("no number found, found " ^ String.implode [c])
            end
      in
        (parse_aux ();
         if !seen_one_digit = false
         then raise Parser_Error ("no number digit")
         else Uint64.fromInt (IntInf.fromInt(!num)))
      end

  fun parse_var istream =
      let
        val _ = print2 "parse_var\n"
        val i = ref 0;
        fun parse_aux () =
            let val c = TextIO.lookahead istream
            in
              if (is_space (valOf c) orelse is_separator (valOf c))
              then (print2 ("var sep = '" ^ String.implode [(valOf c)] ^ "'"))
              else
                case TextIO.input1(istream) of
                    NONE => raise Parser_Error "no char found"
                  | SOME c =>
                     (if !i < ArraySlice.length (!resizable_str) - 1
                     then () else double_string_size ();
                     ArraySlice.update(!resizable_str, !i, c);
                     i := !i + 1;
                     parse_aux ())
            end
      in
        (parse_aux ();
         if !i = 0
         then raise Parser_Error "no variable found"
         else
           (print2 (extract(!resizable_str, 0, SOME (!i)));
             (extract(!resizable_str, 0, SOME (!i)))))
      end;

  fun parse_vars_only_monom istream = (* can start with /*/ *)
      let
        val _ = print2 "parse_vars_only_monom\n"
        val vars = ref [];
        fun parse_aux () =
            let
              val _ = skip_spaces istream;
            in
              if TextIO.lookahead(istream) = SOME #"," orelse TextIO.lookahead(istream) = SOME #";"
                 orelse TextIO.lookahead(istream) = SOME #"-" orelse TextIO.lookahead(istream) = SOME #"+"
              then (print2 ("parse_vars_only_monom, sep =" ^ String.implode [valOf (TextIO.lookahead(istream))] ^ "\n"))
              else if TextIO.lookahead(istream) = SOME #"*"
              then
                (ignore (TextIO.input1(istream));
                 vars := parse_var istream :: (!vars);
                 parse_aux ())
              else
                (vars := parse_var istream :: (!vars);
                 parse_aux ())
            end
      in
        parse_aux ();
        share_term (rev2 (!vars))
      end;

  fun parse_full_monom istream =
      let
        val _ = print2 "parse_full_monom\n"
        val num = ref 1;
        val vars = ref [];
        val next_token = ref NONE;
        val _ = skip_spaces istream;
      in
        (
          next_token := TextIO.lookahead(istream);
          print2 ("parse_full_monom/next token 1 = '" ^String.implode [valOf (!next_token)] ^ "'\n");
          (case !next_token of
               SOME #"-" =>
               (ignore (TextIO.input1 istream);
                num := ~1)
             | SOME #"+" => ignore (TextIO.input1 istream)
             | _ => ());
          skip_spaces istream;
          next_token := TextIO.lookahead(istream);
          print2 ("parse_full_monom/next token 2 = '" ^String.implode [valOf (!next_token)] ^ "'\n");
          if !next_token <> NONE andalso is_digit (valOf (!next_token))
          then num := !num * parse_natural istream
          else ();
          vars := parse_vars_only_monom istream;
          next_token := TextIO.lookahead(istream);
          print2 ("parse_full_monom/next token 3 = '" ^String.implode [valOf (!next_token)] ^ "'\n");
          (!vars, !num)
        )
      end;

  fun parse_comma istream () =
      let
        val c1 = TextIO.input1(istream);
        val c2 = skip_spaces istream;
      in
        if valOf c1 <> #","
        then raise Parser_Error ("unrecognised ',', found '" ^ String.implode [valOf c1] ^ "'")
        else ()
      end

          
  fun parse_polynom istream : (string list * IntInf.int) list =
      let
        val _ = print2 "parse_poly\n"
        val monoms = ref [];
        fun parse_aux () =
            if TextIO.lookahead(istream) = SOME #"," orelse TextIO.lookahead(istream) = SOME #";"
            then print2 ("parse_poly finished"  ^ String.implode [valOf (TextIO.lookahead(istream))] ^ "\n")
            else (monoms := parse_full_monom istream :: !monoms;
                 parse_aux ())
      in
        (parse_aux ();
        rev2 (!monoms))
      end

  fun parse_rule istream =
      let val del = ref false;
          val _ = skip_spaces istream;
      in
        case TextIO.input1(istream) of
            SOME #"d" => (print2 "rule d:\n"; "d")
          | SOME #"+" =>
            (ignore (TextIO.input1 istream); print2 "rule +:\n"; "+:")
          | SOME #"*" =>
            (ignore (TextIO.input1 istream); print2 "rule *:\n";"*:")
          | SOME #"=" =>
            (print2 "rule =\n"; "=")
          | SOME c => raise Parser_Error ("unrecognised rule '" ^ String.implode [c] ^ "'")
      end

  fun parse_EOL istream () =
      let
        val c1 = TextIO.input1(istream);
        val _ = skip_spaces istream;
        val c2 = TextIO.input1(istream);
        fun f () =
          (case TextIO.lookahead istream of
               SOME #"\n" => (ignore (TextIO.input1 istream); f ())
             | _ => ())
      in
        if c1 <> NONE andalso c2 <> NONE andalso (valOf c1 <> #";" orelse valOf c2 <> #"\n")
        then raise Parser_Error ("unrecognised EOL '" ^ String.implode [valOf c1, valOf c2] ^ "'")
        else f ()
      end
 
  fun parse_step istream =
      let
        val lbl = parse_nat istream;
        val _ = print2 ("label = " ^ IntInf.toString (Uint64.toInt lbl));
        val rule = parse_rule istream;
        val _ = print2 ("rule = " ^ rule);
      in
        if  rule = "+:"
        then
          let
            val _ = skip_spaces istream;
            val src1 = parse_natural istream;
            val _ = parse_comma istream ();
            val src2 = parse_natural istream;
            val _ = parse_comma istream ();
            val poly = parse_polynom istream;
            val _ = parse_EOL istream ();
          in
            (PAC_Checker.Add (src1, src2,
                                   lbl,
                                   (map (fn (a,b) => (a, PAC_Checker.Int_of_integer b)) poly)))
          end
        else if rule = "*:"
        then
          let
            val _ = skip_spaces istream;
            val src1 = parse_natural istream;
            val _ = parse_comma istream ();
            val src2 = parse_polynom istream;
            val _ = parse_comma istream ();
            val poly = parse_polynom istream;
            val _ = parse_EOL istream ();
          in
           (PAC_Checker.Mult (src1,
                                       (map (fn (a,b) => (a, PAC_Checker.Int_of_integer b)) src2),
                                  lbl,
                                  (map (fn (a,b) => (a, PAC_Checker.Int_of_integer b)) poly)))
          end
        else if rule = "d"
        then
          let
            val _ = skip_spaces istream;
            val _ = parse_EOL istream ();
          in
            (PAC_Checker.Del (lbl))
          end
        else if rule = "="
        then
          let
            val _ = skip_spaces istream;
            val var = parse_var istream;
            val _ = parse_comma istream ();
            val ext = parse_polynom istream;
            val _ = parse_EOL istream ();
          in
           (PAC_Checker.Extension (lbl, var,
                                       (map (fn (a,b) => (a, PAC_Checker.Int_of_integer b)) ext)))
          end
        else raise Parser_Error ("unrecognised rule '" ^ rule ^ "'")
      end

  fun step_polys istream =
      let
        val polys = ref [];
        fun parse_aux () =
            if TextIO.lookahead(istream) = NONE
            then rev (!polys)
            else (polys := parse_step istream :: (!polys);
                  skip_spaces istream;
                  parse_EOL istream;
                  skip_spaces istream;
                  parse_aux ())
      in
        parse_aux ()
      end

  fun input_poly istream : IntInf.int * (string list * IntInf.int) list =
      let val a = parse_natural istream
          val _ = skip_spaces istream
          val b = (parse_polynom istream)
          val _ = print2 ("parsed " ^ IntInf.toString a ^"\n")
      in (a,b) end

  fun input_polys istream =
      let
        val polys = ref [];
        fun parse_aux () =
            if TextIO.lookahead(istream) = NONE
            then rev (!polys)
            else (polys := input_poly istream :: (!polys);
                  parse_EOL istream ();
                  parse_aux ())
      in
        parse_aux ()
      end

end
