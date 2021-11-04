

(* TODO: segment registers *)

datatype Operand =
           (*  size (in bytes)   segment           offset   base     index    scale *)
    Mem of (   int             * string option   * int    * string * string * int)
  | Reg of string
  | Imm of LargeInt.int

datatype Instr = Instr of (LargeInt.int * LargeInt.int * string * Operand option * Operand option * Operand option)

(* PRETTY PRINTING *)
fun pp_option NONE = ""
  | pp_option (SOME s) = s

fun
  pp_mem_size 1 = "BYTE PTR"
| pp_mem_size 2 = "WORD PTR"
| pp_mem_size 4 = "DWORD PTR"
| pp_mem_size 8 = "QWORD PTR"
| pp_mem_size 16 = "XMMWORD PTR"
| pp_mem_size n = "SIZEDIR " ^ Int.toString (n*8) ^ " PTR"

fun pp_operand (Mem (si,segment,offset,base, index, scale)) =
    pp_mem_size si ^ " " ^ pp_option segment ^ ":[" ^ Int.toString offset ^ " + " ^ base ^ " + " ^ index ^ " * " ^ Int.toString scale ^ "]"
| pp_operand (Reg r) = r
| pp_operand (Imm i) = Int.toString i

fun pp_operands [] = ""
  | pp_operands (NONE::_) = ""
  | pp_operands [SOME op1] = pp_operand op1
  | pp_operands [SOME op1,NONE] = pp_operand op1
  | pp_operands (SOME op1::op2::ops) = pp_operand op1 ^ ", " ^ pp_operands (op2::ops)

fun pp_instr (Instr (a,si,m,op1,op2,op3)) =
  LargeInt.toString a ^ ": " ^ m ^ " " ^ pp_operands [op1,op2,op3] ^ "  (" ^ LargeInt.toString si ^ ")"

val intFromHexString = StringCvt.scanString (LargeInt.scan StringCvt.HEX) o Substring.string

fun intFromHexString_forced s =
    case intFromHexString s of
         SOME i => i
       | NONE => raise Fail ("Could not convert string '" ^ Substring.string s ^ "' to int.")

fun is_whitespace c = (c = #" " orelse c = #"\t"  orelse c = #"\n")

fun trim str =
  let val (_,x) = Substring.splitl is_whitespace str
      val (y,_) = Substring.splitr is_whitespace x in
    y
  end;

(* PARSING *)

val registers = [
  "rip",
  "rax", "eax", "ax", "ah", "al",
  "rbx", "ebx", "bx", "bh", "bl",
  "rcx", "ecx", "cx", "ch", "cl",
  "rdx", "edx", "dx", "dh", "dl",
  "rbp", "ebp", "bp", "bpl",
  "rsp", "esp", "sp", "spl",
  "rdi", "edi", "di", "dil",
  "rsi", "esi", "si", "sil",
  "r15", "r15d", "r15w", "r15b",
  "r14", "r14d", "r14w", "r14b",
  "r13", "r13d", "r13w", "r13b",
  "r12", "r12d", "r12w", "r12b",
  "r11", "r11d", "r11w", "r11b",
  "r10", "r10d", "r10w", "r10b",
  "r9", "r9d", "r9w", "r9b",
  "r8", "r8d", "r8w", "r8b",

  "xmm0","xmm1","xmm2","xmm3","xmm4","xmm5","xmm6","xmm7","xmm8",
  "xmm9","xmm10","xmm11","xmm12","xmm13","xmm14","xmm15"
]

fun is_register str = List.find (fn (str') => String.compare (Substring.string str,str') = EQUAL) registers <> NONE

fun overwrite_str "" s = s
| overwrite_str s "" = s
| overwrite_str _  s = s

fun overwrite_str_option NONE s = s
| overwrite_str_option s NONE = s
| overwrite_str_option _ s     = s

fun max x y = if x >= y then x else y

fun overwrite_Mem (Mem (si,seg,off,base,ind,sc)) (Mem (si',seg',off',base',ind',sc')) =
  Mem (max si si',overwrite_str_option seg seg',max off off',overwrite_str base base',overwrite_str ind ind',max sc sc')

fun parse_operand_address_between_brackets_inner str =
  if is_register str then
    Mem (0,NONE,0,Substring.string str,"",0) (* base *)
  else
    let val tokens = map trim (Substring.tokens (fn c => c = #"*") str) in
      if length tokens = 1 then
        case intFromHexString str of
          SOME i => Mem (0,NONE,i,"","",0) (* offset *)
          | NONE => raise Fail ("Don't know how to parse operand part:" ^ Substring.string str)
      else if length tokens = 2 then
        if is_register (nth tokens 0) then
          Mem (0,NONE,0,"",Substring.string (nth tokens 0),intFromHexString_forced (nth tokens 1)) (* index * scale *)
        else if is_register (nth tokens 1) then
          Mem (0,NONE,0,"",Substring.string (nth tokens 1),intFromHexString_forced (nth tokens 0)) (* scale * index *)
        else
          raise Fail ("Don't know how to parse operand part:" ^ Substring.string str)
      else
        raise Fail ("Don't know how to parse operand part:" ^ Substring.string str)
    end

fun parse_operand_address_between_brackets_sum si segment_reg str =
  let val tokens = map trim (Substring.tokens (fn c => c = #"+") str) in
    fold (overwrite_Mem o parse_operand_address_between_brackets_inner)
         tokens
         (Mem (si,segment_reg ,0,"","",0))
  end;


fun parse_operand_address_between_brackets_sub si segment_reg str =
  let val (lhs,num) = Substring.splitl (fn c => c <> #"-") str;
      val (Mem (x0,x1,_,x3,x4,x5)) = parse_operand_address_between_brackets_sum si segment_reg lhs in
    Mem (x0,x1,intFromHexString_forced num,x3,x4,x5)
   end

fun parse_operand_address_between_brackets si segment_reg str =
  let val (_,num) = Substring.splitl (fn c => c <> #"-") str in
    if Substring.isEmpty num then
      parse_operand_address_between_brackets_sum si segment_reg str
    else
      parse_operand_address_between_brackets_sub si segment_reg str
      end

fun skip_brackets str =
  let val (x,y) = Substring.splitAt (trim str,1)
      val (z,_) = Substring.splitl (fn c => c <> #"]") y in
    if Substring.compare (x,Substring.full "[") = EQUAL then
      z
    else
      raise Fail ("Expecting non-empty bracketed string preceded with colon or an immediate in hex-format, but got: " ^ Substring.string str)
  end;

fun parse_operand_address_bracketed si segment_reg str =
  case intFromHexString str of
      SOME imm => Mem (si,segment_reg,imm,"", "",0)
    | NONE => parse_operand_address_between_brackets si segment_reg (skip_brackets str)

fun tail str =
  case Substring.getc str of
      NONE => raise Fail ("Expecting non-empty string, but got: " ^ Substring.string str)
    | SOME (_,s) => s;

fun parse_operand_address si str =
  case Substring.splitl (fn c => c <> #":") str of
      (before_colon, after_colon) =>
          if Substring.isEmpty after_colon then
            parse_operand_address_bracketed si NONE before_colon
          else
            parse_operand_address_bracketed si (SOME (Substring.string (trim before_colon))) (tail after_colon);

fun parse_operand str' =
  let val str = trim str' in
    if Substring.isPrefix "BYTE PTR" str then
      parse_operand_address 1 (snd (Substring.splitAt (str,8)))
    else if Substring.isPrefix "WORD PTR" str then
      parse_operand_address 2 (snd (Substring.splitAt (str,8)))
    else if Substring.isPrefix "DWORD PTR" str then
      parse_operand_address 4 (snd (Substring.splitAt (str,9)))
    else if Substring.isPrefix "QWORD PTR" str then
      parse_operand_address 8 (snd (Substring.splitAt (str,9)))
    else if Substring.isPrefix "XMMWORD PTR" str then
      parse_operand_address 16 (snd (Substring.splitAt (str,11)))
    else if Substring.isPrefix "[" str then (* happens in case of a LEA instruction *)
      parse_operand_address 0 str
    else if List.find (fn (str') => String.compare (Substring.string str,str') = EQUAL) registers <> NONE then
      Reg (Substring.string str)
    else
      case intFromHexString str of
          NONE => raise Fail ("Cannot read hex number in string: " ^ (Substring.string str))
        | SOME imm => Imm imm
  end;

fun parse_operands str =
  let val tokens = map trim (Substring.tokens (fn c => c = #",") (trim str))
      val ops = map parse_operand tokens in
    case ops of
        [] => (NONE,NONE,NONE)
      | [op1] => (SOME op1,NONE,NONE)
      | [op1,op2] => (SOME op1,SOME op2,NONE)
      | [op1,op2,op3] => (SOME op1,SOME op2,SOME op3)
      | _ => raise Fail ("Unexpected number of operands in : " ^ Substring.string str)
  end;

fun remove_comment str =
  let val (str0,str1) = Substring.splitl (fn c => c <> #"#" andalso c <> #"<") str
  in
    if Substring.isEmpty str1 then str0 else Substring.trimr 1 str0
  end

fun parse_external_func a si str =
  let val (m,func)  = Substring.splitl (fn c => c <> #" ") str
      val func_name =  Substring.string (trim func)
  in
    Instr (a, si, Substring.string m, SOME (Reg func_name), NONE, NONE)
  end

fun parse_normal_instr a si str =
  let val (_,rem1)      = Substring.splitl (fn c => c =  #":" orelse c = #" ") str
      val (m,rem2)      = Substring.splitl (fn c => c <> #" ") rem1
      val (op1,op2,op3) = parse_operands rem2 in
    Instr (a, si, Substring.string m, op1,op2,op3)
  end;

fun parse_instr si str =
  let val str'          = remove_comment (Substring.full str)
      val (addr,rem0)   = Substring.splitl (fn c => c <> #":") str'
      val a             = intFromHexString_forced (Substring.full ("0x" ^ Substring.string (trim addr)))
  in
    if Substring.isPrefix "EXTERNAL_FUNCTION" (trim (tail (rem0))) then
      parse_external_func a si (trim (tail (rem0)))
    else
      parse_normal_instr a si rem0
  end;

fun read_instr_addr str =
  let val instr = parse_instr 0 str
      val (Instr (a,_,_,_,_,_)) = instr in
    a
  end

(* EMBEDDING INTO HOL *)

val mk_nat = HOLogic.mk_number @{typ nat}
val mk_string = HOLogic.mk_string
fun mk_word_typ_from_num s = Syntax.read_typ @{context} ("num \<Rightarrow> " ^ Int.toString s ^ " word")
fun mk_word_typ s = Syntax.read_typ @{context} (Int.toString s ^ " word")

fun mk_word i b =
  if i=0 then
    Const ("Groups.zero_class.zero", mk_word_typ b)
  else if i=1 then
    Const ("Groups.one_class.one", mk_word_typ b)
  else if i < 0 then
    Syntax.read_term @{context} ("uminus :: " ^ Int.toString b ^ " word \<Rightarrow> " ^ Int.toString b ^ " word")
      $ (Const ("Num.numeral_class.numeral", mk_word_typ_from_num b) $ HOLogic.mk_numeral (0 - i))
  else
    Const ("Num.numeral_class.numeral", mk_word_typ_from_num b) $ HOLogic.mk_numeral i

fun mk_operand (Mem (8,segment,offset,base,index,scale)) =
  @{term "qword_ptr"} $ HOLogic.mk_prod (mk_word offset 64,
                         HOLogic.mk_prod (mk_string base,
                          HOLogic.mk_prod (mk_string index, mk_nat scale)))
 | mk_operand (Mem (4,segment,offset,base,index,scale)) =
  @{term "dword_ptr"} $ HOLogic.mk_prod (mk_word offset 64,
                         HOLogic.mk_prod (mk_string base,
                          HOLogic.mk_prod (mk_string index, mk_nat scale)))
 | mk_operand (Mem (2,segment,offset,base,index,scale)) =
  @{term "word_ptr"} $ HOLogic.mk_prod (mk_word offset 64,
                         HOLogic.mk_prod (mk_string base,
                          HOLogic.mk_prod (mk_string index, mk_nat scale)))
 | mk_operand (Mem (1,segment,offset,base,index,scale)) =
  @{term "byte_ptr"} $ HOLogic.mk_prod (mk_word offset 64,
                         HOLogic.mk_prod (mk_string base,
                          HOLogic.mk_prod (mk_string index, mk_nat scale)))
 | mk_operand (Mem (si,segment,offset,base,index,scale)) =
  @{term Mem} $ mk_nat si $ mk_word offset 64 $ mk_string base $ mk_string index $ mk_nat scale
 | mk_operand (Reg reg) =
  @{term Reg} $ mk_string reg
 | mk_operand (Imm imm) =
  @{term Imm} $ mk_word imm 256

fun mk_operand_option NONE       = @{term "None :: Operand option"}
  | mk_operand_option (SOME op1) = @{term "Some :: Operand \<Rightarrow> Operand option"} $ mk_operand op1

fun mk_instr (Instr (_,_,"EXTERNAL_FUNCTION",SOME (Reg f),NONE,NONE)) lthy =
  let val def = Syntax.read_term (Local_Theory.target_of lthy) ("EXTERNAL_FUNCTION_" ^ f) in
    if fastype_of def = (@{typ state} --> @{typ state}) then
      @{term ExternalFunc} $ def
    else
      raise Fail ("Unknown external function: " ^ f ^ "; expecting a function named EXTERNAL_FUNCTION_" ^ f ^ " in locale unknowns of type state \<Rightarrow> state")
  end
| mk_instr (Instr (a,si,m,op1,op2,op3)) _ =
  @{term Instr} $ mk_string m $ mk_operand_option op1 $ mk_operand_option op2 $ mk_operand_option op3 $ mk_word (a+si) 64

(*
  Make a definition in HOL with name "name" and as body "value".
  Value can be any HOL term, e.g.,:
      HOLogic.mk_number @{typ nat} 42
  Note that HOL terms can be produced using antiquotations, e.g.,
      @{term "42::nat"}
  does the same as the above code.
*)
fun mk_definition name value lthy = let
  val binding = Binding.name name
  val (_, lthy) = Local_Theory.define ((binding, NoSyn), ((Thm.def_binding binding, []), value)) lthy
  val _ = tracing ("Added definition: " ^ (Local_Theory.full_name lthy binding))
  in
    lthy
  end


fun main localename assembly lthy = let
  (* Build a locale name *)
  val _ = not (Long_Name.is_qualified localename) orelse raise Fail ("Given localename looks like qualified Isabelle ID: " ^ localename)
  val _ = localename <> "" orelse raise Fail ("Given localename is illegal")

  (* The locale fixes a variable called "fetch" of type "64 word \<Longrightarrow> I" *)
  val fixes_fetch = Element.Fixes [( Binding.name "fetch" , SOME (@{typ "64 word => I"}), NoSyn)]

  (* the locale contains a list of assumptions, one for each instruction. They are given the [simp] attribute. *)
  val simp_attrib = Attrib.internal (fn (_) => Simplifier.simp_add)
  fun mk_assume thm_name term =  ((Binding.name thm_name, [simp_attrib]), [term]);
  val mk_fetch = Free ("fetch", @{typ "64 word => I"})
  fun mk_fetch_equality_assume si str =
    let val instr = parse_instr si str
        val (Instr (a,_,_,_,_,_)) = instr
        val asm_name = "fetch_" ^ LargeInt.toString a
        val eq_term = HOLogic.mk_eq (mk_fetch $ mk_word a 64, mk_instr instr lthy)
    in
      mk_assume asm_name (HOLogic.Trueprop $ eq_term, [])
    end

  fun mk_fetch_equality_assumes [] = []
    | mk_fetch_equality_assumes [str] = [mk_fetch_equality_assume 1 str]
    | mk_fetch_equality_assumes (str0::str1::strs) = (mk_fetch_equality_assume (read_instr_addr str1 - read_instr_addr str0) str0) :: mk_fetch_equality_assumes (str1::strs)


  val assembly = String.tokens (fn c => c = #"\n") assembly |>
    List.filter (Substring.full #> remove_comment #> Substring.explode #> List.all Char.isSpace #> not)
  val loc_bindings = Binding.name localename
  val loc_elems = [fixes_fetch,Element.Assumes (mk_fetch_equality_assumes assembly)]
  val thy = Local_Theory.exit_global lthy
  val loc_expr : (string, term) Expression.expr = [(Locale.intern thy "unknowns",(("",false),(Expression.Named [], [])))]
  val (_,lthy) = Expression.add_locale loc_bindings loc_bindings [] (loc_expr,[]) loc_elems thy
  val _ = tracing ("Added locale: " ^ localename ^ " with a fetch function for " ^ Int.toString (length assembly) ^ " instructions. To get started, execute:\n\ncontext " ^ localename ^ "\nbegin\n   find_theorems fetch\nend\n")

  in
   lthy
  end




(*
  Add the command "x86_64_parser" to the Isabelle syntax.
  Its argument is parsed by Parse.text, which simply returns
  the text. The parsed text is given to the "main" function.
*)

val _ =
    Outer_Syntax.local_theory
      \<^command_keyword>\<open>x86_64_parser\<close>
      "Generate a locale from a list of assembly instructions."
      (Parse.text -- Parse.text >> (fn (localename, assembly) => main localename assembly))
