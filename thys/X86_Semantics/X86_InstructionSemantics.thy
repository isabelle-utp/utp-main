(*  Title:       X86 instruction semantics and basic block symbolic execution
    Authors:     Freek Verbeek, Abhijith Bharadwaj, Joshua Bockenek, Ian Roessle, Timmy Weerwag, Binoy Ravindran
    Year:        2020
    Maintainer:  Freek Verbeek (freek@vt.edu)
*)

section "Instruction Semantics"

theory X86_InstructionSemantics
  imports State
begin

text \<open>A datatype for storing instructions. Note that we add a special kind of meta-instruction, called
      ExternalFunc. A call to an external function can manually be mapped to a manually supplied state 
      transformation function.\<close>
datatype I = 
    Instr string "Operand option" "Operand option" "Operand option" "64 word"
  | ExternalFunc "state \<Rightarrow> state"

text \<open>A datatype for the result of floating point comparisons.\<close>
datatype FP_Order = FP_Unordered | FP_GT | FP_LT | FP_EQ


abbreviation "instr_next i \<equiv> case i of (Instr _ _ _ _ a') \<Rightarrow> a'"

locale unknowns =
  fixes unknown_addsd     :: "64 word \<Rightarrow> 64 word \<Rightarrow> 64 word"
    and unknown_subsd     :: "64 word \<Rightarrow> 64 word \<Rightarrow> 64 word"
    and unknown_mulsd     :: "64 word \<Rightarrow> 64 word \<Rightarrow> 64 word"
    and unknown_divsd     :: "64 word \<Rightarrow> 64 word \<Rightarrow> 64 word"
    and unknown_ucomisd   :: "64 word \<Rightarrow> 64 word \<Rightarrow> FP_Order"
    and unknown_semantics :: "I \<Rightarrow> state \<Rightarrow> state"
    and unknown_flags     :: "string \<Rightarrow> string \<Rightarrow> bool" 
begin

text \<open>
  The semantics below are intended to be overapproximative and incomplete.
  This is achieved using locale ``unknowns''.
  Any place where semantics is \emph{not} modelled, it is mapped to a universally quantified uninterpreted function
  from that locale. We do not make use of @{const undefined}, since that could be used to prove that the semantics
  of two undefined behaviors are equivalent. 
  For example:
  \begin{itemize}
  \item Only a subset of instructions has semantics. In case of an unknown instruction $i$,
        the function @{term semantics} below will result in @{term "unknown_semantics i"}.
  \item Not all flags have been defined. In case a flag is read whose semantics is not defined below,
        the read will resolve to @{term "unknown_flags i f"}. Note that if the semantics of an instruction do
        not set flags, an overapproximative semantics such as below imply that the instruction indeed
        does not modify flags. In order words, if we were uncertain we would assign unknown values to flags.
  \item Not all operations have been defined. For example, floating points operations have no executable
        semantics, but are mapped to uninterpreted functions such as @{term unknown_addsd}.
  \end{itemize}
\<close>



text \<open>Moves\<close>

definition semantics_MOV :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_MOV op1 op2 \<sigma> \<equiv>
          let src = operand_read \<sigma> op2 in
             operand_write op1 src \<sigma>"

abbreviation MOV
  where "MOV op1 op2 \<equiv> Instr ''mov'' (Some op1) (Some op2) None"

abbreviation MOVABS
  where "MOVABS op1 op2 \<equiv> Instr ''movabs'' (Some op1) (Some op2) None"

abbreviation MOVAPS
  where "MOVAPS op1 op2 \<equiv> Instr ''movaps'' (Some op1) (Some op2) None"

abbreviation MOVZX
  where "MOVZX op1 op2 \<equiv> Instr ''movzx'' (Some op1) (Some op2) None"

abbreviation MOVDQU
  where "MOVDQU op1 op2 \<equiv> Instr ''movdqu'' (Some op1) (Some op2) None"

definition semantics_MOVD :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_MOVD op1 op2 \<sigma> \<equiv>
          let src = ucast(operand_read \<sigma> op2)::32word in
             operand_write op1 (ucast src) \<sigma>"

abbreviation MOVD
  where "MOVD op1 op2 \<equiv> Instr ''movd'' (Some op1) (Some op2) None"

fun isXMM :: "Operand \<Rightarrow> bool"
  where "isXMM (Reg r) = (take 3 r = ''xmm'')"
  | "isXMM _ = False"

definition semantics_MOVSD :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_MOVSD op1 op2 \<sigma> \<equiv>
    if isXMM op1 \<and> isXMM op2 then
      let src = \<langle>0,64\<rangle>operand_read \<sigma> op2;
          dst = \<langle>64,128\<rangle>operand_read \<sigma> op1 in
             operand_write op1 (overwrite 0 64 dst src) \<sigma>
     else
      let src = \<langle>0,64\<rangle>operand_read \<sigma> op2 in
         operand_write op1 src \<sigma>"

abbreviation MOVSD
  where "MOVSD op1 op2 \<equiv> Instr ''movsd'' (Some op1) (Some op2) None"

abbreviation MOVQ
  where "MOVQ op1 op2 \<equiv> Instr ''movq'' (Some op1) (Some op2) None"


text \<open> lea/push/pop/call/ret/leave \<close>

definition semantics_LEA :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_LEA op1 op2 \<sigma> \<equiv>
          case op2 of Mem si offset base index scale \<Rightarrow>
            operand_write op1 (ucast (resolve_address \<sigma> offset base index scale)) \<sigma>"

abbreviation LEA
  where "LEA op1 op2 \<equiv> Instr ''lea'' (Some op1) (Some op2) None"

definition semantics_PUSH :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_PUSH op1 \<sigma> \<equiv>
          let src = operand_read \<sigma> op1;
              si  = operand_size op1;
              rsp = ucast (ucast(reg_read \<sigma> ''rsp'') - of_nat si :: 64 word) in
             operand_write (QWORD PTR [''rsp'']\<^sub>1) src (operand_write (Reg ''rsp'') rsp \<sigma>)"

abbreviation PUSH
  where "PUSH op1 \<equiv> Instr ''push'' (Some op1) None None"

definition semantics_POP :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_POP op1 \<sigma> \<equiv>
          let si  = operand_size op1;
              src = operand_read \<sigma> (QWORD PTR [''rsp'']\<^sub>1);
              rsp = ucast (ucast(reg_read \<sigma> ''rsp'') + of_nat si::64 word) in
             operand_write op1 src (operand_write (Reg ''rsp'') rsp \<sigma>)"

abbreviation POP
  where "POP op1 \<equiv> Instr ''pop'' (Some op1) None None"

definition semantics_CALL :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_CALL op1 \<sigma> \<equiv>
        let src = ucast (operand_read \<sigma> op1) in
           (state_update (setRip src) o semantics_PUSH (Reg ''rip'')) \<sigma>"

definition semantics_RET :: "state \<Rightarrow> state"
  where "semantics_RET \<sigma> \<equiv>
          let a   = ucast (operand_read \<sigma> (QWORD PTR [''rsp'']\<^sub>1));
              rsp = ucast (reg_read \<sigma> ''rsp'') + 8 :: 64 word in
             (state_update (setRip a) o operand_write (Reg ''rsp'') (ucast rsp)) \<sigma>"

abbreviation RET
  where "RET \<equiv> Instr ''ret'' None None None"

definition semantics_LEAVE :: "state \<Rightarrow> state"
  where "semantics_LEAVE \<equiv> semantics_POP (Reg ''rbp'') o semantics_MOV (Reg ''rsp'') (Reg ''rbp'')"

abbreviation LEAVE
  where "LEAVE op1 \<equiv> Instr ''pop'' (Some op1) None None"

text \<open>Generic operators \<close>

definition unop :: "('a ::len word \<Rightarrow> 'a::len word) \<Rightarrow> 
                     ('a::len word  \<Rightarrow> string \<Rightarrow> bool) \<Rightarrow>
                      Operand \<Rightarrow> state \<Rightarrow> state"
  where "unop f g op1 \<sigma> \<equiv>
          let si  = operand_size op1;
              dst = ucast (operand_read \<sigma> op1)::'a::len word in
             operand_write op1 (ucast (f dst)) (\<sigma> with [setFlags (g dst)])"

definition binop :: "('a::len word \<Rightarrow> 'a ::len word \<Rightarrow> 'a::len word) \<Rightarrow>
                     ('a::len word \<Rightarrow> 'a::len word  \<Rightarrow> string \<Rightarrow> bool) \<Rightarrow>
                      Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "binop f g op1 op2 \<sigma> \<equiv>
          let dst = ucast (operand_read \<sigma> op1)::'a::len word;
              src = ucast (operand_read \<sigma> op2)::'a::len word in
             operand_write op1 (ucast (f dst src)) (\<sigma> with [setFlags (g dst src)])"

definition unop_no_flags :: "('a ::len word \<Rightarrow> 'a::len word) \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "unop_no_flags f op1 \<sigma> \<equiv>
          let dst = ucast (operand_read \<sigma> op1)::'a::len word in
             operand_write op1 (ucast (f dst)) \<sigma>"

definition binop_flags :: "('a::len word \<Rightarrow> 'a::len word  \<Rightarrow> string \<Rightarrow> bool) \<Rightarrow>
                      Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "binop_flags g op1 op2 \<sigma> \<equiv>
          let si  = operand_size op1;
              dst = ucast (operand_read \<sigma> op1)::'a::len word;
              src = ucast (operand_read \<sigma> op2)::'a::len word in
            \<sigma> with [setFlags (g dst src)]"

definition binop_no_flags :: "('a::len word \<Rightarrow> 'a ::len word \<Rightarrow> 'a::len word) \<Rightarrow>
                      Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "binop_no_flags f op1 op2 \<sigma> \<equiv>
          let si  = operand_size op1;
              dst = ucast (operand_read \<sigma> op1)::'a::len word;
              src = ucast (operand_read \<sigma> op2)::'a::len word in
            operand_write op1 (ucast (f dst src)) \<sigma>"

definition binop_XMM :: "(64 word \<Rightarrow> 64 word \<Rightarrow> 64 word) \<Rightarrow> Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "binop_XMM f op1 op2 \<sigma> \<equiv>
          let dst = ucast (operand_read \<sigma> op1)::64word;
              src = ucast (operand_read \<sigma> op2)::64word in
            operand_write op1 (ucast (overwrite 0 64 dst (f dst src))) \<sigma>"

text \<open>Arithmetic\<close>

definition ADD_flags :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> string \<Rightarrow> bool"
  where "ADD_flags w0 w1 flag \<equiv> case flag of
    ''zf'' \<Rightarrow> w0 + w1 = 0
  | ''cf'' \<Rightarrow> unat w0 + unat w1 \<ge> 2^(LENGTH('a))
  | ''of'' \<Rightarrow> (w0 <s 0 \<longleftrightarrow> w1 <s 0) \<and> \<not>(w0 <s 0 \<longleftrightarrow> w0+w1 <s 0)
  | ''sf'' \<Rightarrow> w0 + w1 <s 0
  | f      \<Rightarrow> unknown_flags ''ADD'' f"

definition semantics_ADD :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_ADD op1 \<equiv> 
           if operand_size op1 = 32 then binop ((+)::256 word \<Rightarrow> _ \<Rightarrow> _) ADD_flags op1
      else if operand_size op1 = 16 then binop ((+)::128 word \<Rightarrow> _ \<Rightarrow> _) ADD_flags op1
      else if operand_size op1 = 8  then binop ((+)::64  word \<Rightarrow> _ \<Rightarrow> _) ADD_flags op1
      else if operand_size op1 = 4  then binop ((+)::32  word \<Rightarrow> _ \<Rightarrow> _) ADD_flags op1
      else if operand_size op1 = 2  then binop ((+)::16  word \<Rightarrow> _ \<Rightarrow> _) ADD_flags op1
      else if operand_size op1 = 1  then binop ((+)::8   word \<Rightarrow> _ \<Rightarrow> _) ADD_flags op1
      else undefined"

abbreviation ADD
  where "ADD op1 op2 \<equiv> Instr ''add'' (Some op1) (Some op2) None"


definition INC_flags :: "256 word \<Rightarrow> ('a::len word \<Rightarrow> string \<Rightarrow> bool)"
  where "INC_flags cf w0 flag \<equiv> case flag of
    ''zf'' \<Rightarrow> w0 + 1 = 0
  | ''cf'' \<Rightarrow> cf \<noteq> 0
  | ''of'' \<Rightarrow> 0 <=s w0 \<and> w0+1 <s 0
  | ''sf'' \<Rightarrow> w0 + 1 <s 0
  | f      \<Rightarrow> unknown_flags ''INC'' f"

definition semantics_INC :: "Operand \<Rightarrow> state \<Rightarrow> state" 
  where "semantics_INC op1 \<sigma> \<equiv> 
    let cf = flag_read \<sigma> ''cf'' in
           if operand_size op1 = 32 then unop ((+) (1::256 word)) (INC_flags cf) op1 \<sigma>
      else if operand_size op1 = 16 then unop ((+) (1::128 word)) (INC_flags cf) op1 \<sigma>
      else if operand_size op1 = 8  then unop ((+) (1::64  word)) (INC_flags cf) op1 \<sigma>
      else if operand_size op1 = 4  then unop ((+) (1::32  word)) (INC_flags cf) op1 \<sigma>
      else if operand_size op1 = 2  then unop ((+) (1::16  word)) (INC_flags cf) op1 \<sigma>
      else if operand_size op1 = 1  then unop ((+) (1::8   word)) (INC_flags cf) op1 \<sigma>
      else undefined"

abbreviation INC
  where "INC op1 \<equiv> Instr ''inc'' (Some op1) None None"

definition DEC_flags :: "256 word \<Rightarrow> ('a::len word \<Rightarrow> string \<Rightarrow> bool)"
  where "DEC_flags cf w0 flag \<equiv> case flag of
    ''zf'' \<Rightarrow> w0 = 1
  | ''cf'' \<Rightarrow> cf \<noteq> 0
  | ''of'' \<Rightarrow> w0 <s 0 \<and> 0 <=s w0 - 1
  | ''sf'' \<Rightarrow> w0 - 1 <s 0
  | f      \<Rightarrow> unknown_flags ''DEC'' f"

definition semantics_DEC :: "Operand \<Rightarrow> state \<Rightarrow> state" 
  where "semantics_DEC op1 \<sigma> \<equiv> 
    let cf = flag_read \<sigma> ''cf'' in
           if operand_size op1 = 32 then unop (\<lambda> w . w - 1::256 word) (DEC_flags cf) op1 \<sigma>
      else if operand_size op1 = 16 then unop (\<lambda> w . w - 1::128 word) (DEC_flags cf) op1 \<sigma>
      else if operand_size op1 = 8  then unop (\<lambda> w . w - 1::64  word) (DEC_flags cf) op1 \<sigma>
      else if operand_size op1 = 4  then unop (\<lambda> w . w - 1::32  word) (DEC_flags cf) op1 \<sigma>
      else if operand_size op1 = 2  then unop (\<lambda> w . w - 1::16  word) (DEC_flags cf) op1 \<sigma>
      else if operand_size op1 = 1  then unop (\<lambda> w . w - 1::8   word) (DEC_flags cf) op1 \<sigma>
      else undefined"

abbreviation DEC
  where "DEC op1 \<equiv> Instr ''dec'' (Some op1) None None"

definition NEG_flags :: "('a::len word \<Rightarrow> string \<Rightarrow> bool)"
  where "NEG_flags w0 flag \<equiv> case flag of
    ''zf'' \<Rightarrow> w0 = 0
  | ''cf'' \<Rightarrow> w0 \<noteq> 0
  | ''sf'' \<Rightarrow> - w0 <s 0
  | ''of'' \<Rightarrow> msb (- w0) \<and> msb w0
  | f      \<Rightarrow> unknown_flags ''NEG'' f"


definition semantics_NEG :: "Operand \<Rightarrow> state \<Rightarrow> state" 
  where "semantics_NEG op1 \<sigma> \<equiv> 
           if operand_size op1 = 32 then unop (\<lambda> w0 . - (w0::256 word)) NEG_flags op1 \<sigma>
      else if operand_size op1 = 16 then unop (\<lambda> w0 . - (w0::128 word)) NEG_flags op1 \<sigma>
      else if operand_size op1 = 8  then unop (\<lambda> w0 . - (w0::64  word)) NEG_flags op1 \<sigma>
      else if operand_size op1 = 4  then unop (\<lambda> w0 . - (w0::32  word)) NEG_flags op1 \<sigma>
      else if operand_size op1 = 2  then unop (\<lambda> w0 . - (w0::16  word)) NEG_flags op1 \<sigma>
      else if operand_size op1 = 1  then unop (\<lambda> w0 . - (w0::8   word)) NEG_flags op1 \<sigma>
      else undefined"

abbreviation NEG
  where "NEG op1 \<equiv> Instr ''neg'' (Some op1) None None"

definition SUB_flags :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> string  \<Rightarrow> bool"
  where "SUB_flags w0 w1 flag \<equiv> case flag of
    ''zf'' \<Rightarrow> w0 = w1
  | ''cf'' \<Rightarrow> w0 < w1
  | ''sf'' \<Rightarrow> w0 - w1 <s 0
  | ''of'' \<Rightarrow> (msb w0 \<noteq> msb w1) \<and> (msb (w0 - w1) = msb w1)
  | f      \<Rightarrow> unknown_flags ''SUB'' f"

definition semantics_SUB :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_SUB op1 \<equiv> 
           if operand_size op1 = 32 then binop ((-)::256 word \<Rightarrow> _ \<Rightarrow> _) SUB_flags op1
      else if operand_size op1 = 16 then binop ((-)::128 word \<Rightarrow> _ \<Rightarrow> _) SUB_flags op1
      else if operand_size op1 = 8  then binop ((-)::64  word \<Rightarrow> _ \<Rightarrow> _) SUB_flags op1
      else if operand_size op1 = 4  then binop ((-)::32  word \<Rightarrow> _ \<Rightarrow> _) SUB_flags op1
      else if operand_size op1 = 2  then binop ((-)::16  word \<Rightarrow> _ \<Rightarrow> _) SUB_flags op1
      else if operand_size op1 = 1  then binop ((-)::8   word \<Rightarrow> _ \<Rightarrow> _) SUB_flags op1
      else undefined"

abbreviation SUB
  where "SUB op1 op2 \<equiv> Instr ''sub'' (Some op1) (Some op2) None"

definition sbb :: "'b::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  where "sbb cf dst src \<equiv> dst - (src + ucast cf)"

definition SBB_flags :: "'b::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word \<Rightarrow> string  \<Rightarrow> bool"
  where "SBB_flags cf dst src flag \<equiv> case flag of
    ''zf'' \<Rightarrow> sbb cf dst src = 0
  | ''cf'' \<Rightarrow> dst < src + ucast cf
  | ''sf'' \<Rightarrow> sbb cf dst src <s 0
  | ''of'' \<Rightarrow> (msb dst \<noteq> msb (src + ucast cf)) \<and> (msb (sbb cf dst src) = msb (src + ucast cf))
  | f      \<Rightarrow> unknown_flags ''SBB'' f"

definition semantics_SBB :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_SBB op1 op2 \<sigma> \<equiv> 
    let cf = flag_read \<sigma> ''cf'' in
           if operand_size op1 = 32 then binop (sbb cf::256 word \<Rightarrow> _ \<Rightarrow> _) (SBB_flags cf) op1 op2 \<sigma>
      else if operand_size op1 = 16 then binop (sbb cf::128 word \<Rightarrow> _ \<Rightarrow> _) (SBB_flags cf) op1 op2 \<sigma>
      else if operand_size op1 = 8  then binop (sbb cf::64  word \<Rightarrow> _ \<Rightarrow> _) (SBB_flags cf) op1 op2 \<sigma>
      else if operand_size op1 = 4  then binop (sbb cf::32  word \<Rightarrow> _ \<Rightarrow> _) (SBB_flags cf) op1 op2 \<sigma>
      else if operand_size op1 = 2  then binop (sbb cf::16  word \<Rightarrow> _ \<Rightarrow> _) (SBB_flags cf) op1 op2 \<sigma>
      else if operand_size op1 = 1  then binop (sbb cf::8   word \<Rightarrow> _ \<Rightarrow> _) (SBB_flags cf) op1 op2 \<sigma>
      else undefined"

abbreviation SBB
  where "SBB op1 op2 \<equiv> Instr ''sbb'' (Some op1) (Some op2) None"

definition adc :: "'b::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  where "adc cf dst src \<equiv> dst + (src + ucast cf)"

definition ADC_flags :: "'b::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word \<Rightarrow> string  \<Rightarrow> bool"
  where "ADC_flags cf dst src flag \<equiv> case flag of
    ''zf'' \<Rightarrow> adc cf dst src = 0
  | ''cf'' \<Rightarrow> unat dst + unat src + unat cf \<ge> 2^(LENGTH('a))
  | ''of'' \<Rightarrow> (dst <s 0 \<longleftrightarrow> src + ucast cf <s 0) \<and> \<not>(dst <s 0 \<longleftrightarrow> adc cf dst src <s 0)
  | ''sf'' \<Rightarrow> adc cf dst src <s 0
  | f      \<Rightarrow> unknown_flags ''ADC'' f"


definition semantics_ADC :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_ADC op1 op2 \<sigma> \<equiv> 
    let cf = flag_read \<sigma> ''cf'' in
           if operand_size op1 = 32 then binop (adc cf::256 word \<Rightarrow> _ \<Rightarrow> _) (ADC_flags cf) op1 op2 \<sigma>
      else if operand_size op1 = 16 then binop (adc cf::128 word \<Rightarrow> _ \<Rightarrow> _) (ADC_flags cf) op1 op2 \<sigma>
      else if operand_size op1 = 8  then binop (adc cf::64  word \<Rightarrow> _ \<Rightarrow> _) (ADC_flags cf) op1 op2 \<sigma>
      else if operand_size op1 = 4  then binop (adc cf::32  word \<Rightarrow> _ \<Rightarrow> _) (ADC_flags cf) op1 op2 \<sigma>
      else if operand_size op1 = 2  then binop (adc cf::16  word \<Rightarrow> _ \<Rightarrow> _) (ADC_flags cf) op1 op2 \<sigma>
      else if operand_size op1 = 1  then binop (adc cf::8   word \<Rightarrow> _ \<Rightarrow> _) (ADC_flags cf) op1 op2 \<sigma>
      else undefined"

abbreviation ADC
  where "ADC op1 op2 \<equiv> Instr ''adc'' (Some op1) (Some op2) None"


definition write_MUL_result :: "string \<Rightarrow> string \<Rightarrow> 'a::len word \<Rightarrow> _ \<Rightarrow> state \<Rightarrow> state"
  where "write_MUL_result rh rl result flgs \<sigma> \<equiv> 
        let si = LENGTH('a) div 2 in
          operand_write (Reg rh) (ucast (\<langle>si,2*si\<rangle>result))
            (operand_write (Reg rl) (ucast (\<langle>0,si\<rangle>result))
              (\<sigma> with [setFlags flgs]))"

definition MUL_flags :: "'a::len word \<Rightarrow> string \<Rightarrow> bool"
  where "MUL_flags result flag \<equiv> case flag of
        ''cf'' \<Rightarrow> (\<langle>LENGTH('a) div 2,LENGTH('a)\<rangle>result) \<noteq> 0
      | ''of'' \<Rightarrow> (\<langle>LENGTH('a) div 2,LENGTH('a)\<rangle>result) \<noteq> 0
      | f      \<Rightarrow> unknown_flags ''MUL'' f"


definition IMUL_flags :: "'a::len word \<Rightarrow> string \<Rightarrow> bool"
  where "IMUL_flags result flag \<equiv> case flag of
        ''cf'' \<Rightarrow> (\<langle>LENGTH('a) div 2,LENGTH('a)\<rangle>result) \<noteq> (if result !! (LENGTH('a) div 2 - 1) then 2^(LENGTH('a) div 2)-1 else 0)
      | ''of'' \<Rightarrow> (\<langle>LENGTH('a) div 2,LENGTH('a)\<rangle>result) \<noteq> (if result !! (LENGTH('a) div 2 - 1) then 2^(LENGTH('a) div 2)-1 else 0)
      | f      \<Rightarrow> unknown_flags ''IMUL'' f"


(*
  Assumes LENGTH('a) is twice the size of the operands, e.g.:
    unop_MUL TYPE(16) True ''al'' (Reg ''r15b'') \<sigma>
*)
definition unop_MUL :: "'a::len itself \<Rightarrow> bool \<Rightarrow> string \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "unop_MUL _ signd op1_reg op2 \<sigma> \<equiv>
          let cast = (if signd then scast else ucast);
              dst  = cast (operand_read \<sigma> (Reg op1_reg))::'a::len word;
              src  = cast (operand_read \<sigma> op2)::'a::len word;
              prod = dst * src;
              flgs = (if signd then IMUL_flags else MUL_flags) prod in
            if LENGTH('a) = 16 then
              write_MUL_result ''ah'' op1_reg prod flgs \<sigma>
            else if LENGTH('a) = 32 then
              write_MUL_result ''dx'' op1_reg prod flgs \<sigma>
            else if LENGTH('a) = 64 then
              write_MUL_result ''edx'' op1_reg  prod flgs \<sigma>
            else if LENGTH('a) = 128 then
              write_MUL_result ''rdx'' op1_reg prod flgs \<sigma>
            else
              undefined"

definition semantics_MUL :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_MUL op2 \<equiv> 
           if operand_size op2 = 8 then unop_MUL TYPE(128) False ''rax'' op2
      else if operand_size op2 = 4 then unop_MUL TYPE(64)  False ''eax'' op2
      else if operand_size op2 = 2 then unop_MUL TYPE(32)  False ''ax''  op2
      else if operand_size op2 = 1 then unop_MUL TYPE(16)  False ''al''  op2
      else undefined"

abbreviation MUL
  where "MUL op1 \<equiv> Instr ''mul'' (Some op1) None None"

definition semantics_IMUL1 :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_IMUL1 op2 \<equiv> 
           if operand_size op2 = 8 then unop_MUL TYPE(128) True ''rax'' op2
      else if operand_size op2 = 4 then unop_MUL TYPE(64)  True ''eax'' op2
      else if operand_size op2 = 2 then unop_MUL TYPE(32)  True ''ax''  op2
      else if operand_size op2 = 1 then unop_MUL TYPE(16)  True ''al''  op2
      else undefined"

abbreviation IMUL1
  where "IMUL1 op1 \<equiv> Instr ''imul'' (Some op1) None None"

definition ternop_IMUL :: "'a::len itself \<Rightarrow> Operand \<Rightarrow> Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "ternop_IMUL _ op1 op2 op3 \<sigma> \<equiv>
          let src1 = scast (operand_read \<sigma> op2)::'a::len word;
              src2 = scast (operand_read \<sigma> op3)::'a::len word;
              prod = src1 * src2;
              flgs = IMUL_flags prod in
            (operand_write op1 (ucast (\<langle>0,LENGTH('a) div 2\<rangle>prod))
                (\<sigma> with [setFlags flgs]))"

definition semantics_IMUL2 :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_IMUL2 op1 op2 \<equiv> 
           if operand_size op1 = 8 then ternop_IMUL TYPE(128) op1 op1 op2
      else if operand_size op1 = 4 then ternop_IMUL TYPE(64)  op1 op1 op2
      else if operand_size op1 = 2 then ternop_IMUL TYPE(32)  op1 op1 op2
      else if operand_size op1 = 1 then ternop_IMUL TYPE(16)  op1 op1 op2
      else undefined"

abbreviation IMUL2
  where "IMUL2 op1 op2 \<equiv> Instr ''imul'' (Some op1) (Some op2) None"

definition semantics_IMUL3 :: "Operand \<Rightarrow> Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_IMUL3 op1 op2 op3 \<equiv> 
           if operand_size op1 = 8 then ternop_IMUL TYPE(128) op1 op2 op3
      else if operand_size op1 = 4 then ternop_IMUL TYPE(64)  op1 op2 op3
      else if operand_size op1 = 2 then ternop_IMUL TYPE(32)  op1 op2 op3
      else if operand_size op1 = 1 then ternop_IMUL TYPE(16)  op1 op2 op3
      else undefined"

abbreviation IMUL3
  where "IMUL3 op1 op2 op3 \<equiv> Instr ''imul'' (Some op1) (Some op2) (Some op3)"

definition SHL_flags :: "nat \<Rightarrow> ('a::len word \<Rightarrow> string \<Rightarrow> bool)"
  where "SHL_flags n dst flag \<equiv> case flag of
        ''cf'' \<Rightarrow> dst !! (LENGTH('a) - n) 
      | ''of'' \<Rightarrow> dst !! (LENGTH('a) - n - 1) \<noteq> dst !! (LENGTH('a) - n)
      | ''zf'' \<Rightarrow> (dst << n) = 0
      | ''sf'' \<Rightarrow> dst !! (LENGTH('a) - n - 1)
      | f      \<Rightarrow> unknown_flags ''SHL'' f"

definition semantics_SHL :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state" 
  where "semantics_SHL op1 op2 \<sigma> \<equiv> 
    let src = unat (operand_read \<sigma> op2) in
           if operand_size op1 = 32 then unop (\<lambda> w . w << src::256 word) (SHL_flags src) op1 \<sigma>
      else if operand_size op1 = 16 then unop (\<lambda> w . w << src::128 word) (SHL_flags src) op1 \<sigma>
      else if operand_size op1 = 8  then unop (\<lambda> w . w << src::64  word) (SHL_flags src) op1 \<sigma>
      else if operand_size op1 = 4  then unop (\<lambda> w . w << src::32  word) (SHL_flags src) op1 \<sigma>
      else if operand_size op1 = 2  then unop (\<lambda> w . w << src::16  word) (SHL_flags src) op1 \<sigma>
      else if operand_size op1 = 1  then unop (\<lambda> w . w << src::8   word) (SHL_flags src) op1 \<sigma>
      else undefined"

abbreviation SHL
  where "SHL op1 op2 \<equiv> Instr ''shl'' (Some op1) (Some op2) None"

abbreviation SAL
  where "SAL op1 op2 \<equiv> Instr ''sal'' (Some op1) (Some op2) None"

definition SHR_flags :: "nat \<Rightarrow> ('a::len word \<Rightarrow> string \<Rightarrow> bool)"
  where "SHR_flags n dst flag \<equiv> case flag of
        ''cf'' \<Rightarrow> dst !! (n - 1) 
      | ''of'' \<Rightarrow> msb dst
      | ''zf'' \<Rightarrow> (dst >> n) = 0
      | f      \<Rightarrow> unknown_flags ''SHR'' f"

definition semantics_SHR :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state" 
  where "semantics_SHR op1 op2 \<sigma> \<equiv> 
    let src = unat (operand_read \<sigma> op2) in
           if operand_size op1 = 32 then unop (\<lambda> w . w >> src::256 word) (SHR_flags src) op1 \<sigma>
      else if operand_size op1 = 16 then unop (\<lambda> w . w >> src::128 word) (SHR_flags src) op1 \<sigma>
      else if operand_size op1 = 8  then unop (\<lambda> w . w >> src::64  word) (SHR_flags src) op1 \<sigma>
      else if operand_size op1 = 4  then unop (\<lambda> w . w >> src::32  word) (SHR_flags src) op1 \<sigma>
      else if operand_size op1 = 2  then unop (\<lambda> w . w >> src::16  word) (SHR_flags src) op1 \<sigma>
      else if operand_size op1 = 1  then unop (\<lambda> w . w >> src::8   word) (SHR_flags src) op1 \<sigma>
      else undefined"

abbreviation SHR
  where "SHR op1 op2 \<equiv> Instr ''shr'' (Some op1) (Some op2) None"

definition SAR_flags :: "nat \<Rightarrow> ('a::len word \<Rightarrow> string \<Rightarrow> bool)"
  where "SAR_flags n dst flag \<equiv> case flag of
        ''cf'' \<Rightarrow> dst !! (n - 1) 
      | ''of'' \<Rightarrow> False
      | ''zf'' \<Rightarrow> (dst >>> n) = 0
      | f      \<Rightarrow> unknown_flags ''SAR'' f"


definition semantics_SAR :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state" 
  where "semantics_SAR op1 op2 \<sigma> \<equiv> 
    let src = unat (operand_read \<sigma> op2) in
           if operand_size op1 = 32 then unop (\<lambda> w . w >>> src::256 word) (SAR_flags src) op1 \<sigma>
      else if operand_size op1 = 16 then unop (\<lambda> w . w >>> src::128 word) (SAR_flags src) op1 \<sigma>
      else if operand_size op1 = 8  then unop (\<lambda> w . w >>> src::64  word) (SAR_flags src) op1 \<sigma>
      else if operand_size op1 = 4  then unop (\<lambda> w . w >>> src::32  word) (SAR_flags src) op1 \<sigma>
      else if operand_size op1 = 2  then unop (\<lambda> w . w >>> src::16  word) (SAR_flags src) op1 \<sigma>
      else if operand_size op1 = 1  then unop (\<lambda> w . w >>> src::8   word) (SAR_flags src) op1 \<sigma>
      else undefined"

abbreviation SAR
  where "SAR op1 op2 \<equiv> Instr ''sar'' (Some op1) (Some op2) None"


definition shld :: "'b::len itself \<Rightarrow> nat \<Rightarrow> 'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  where "shld _ n dst src \<equiv>
    let dstsrc  = (ucast dst << LENGTH('a)) OR (ucast src :: 'b word);
        shifted = \<langle>LENGTH('a),LENGTH('a)*2\<rangle>(dstsrc << n) in
      ucast shifted"

definition SHLD_flags :: "'b::len itself \<Rightarrow> nat \<Rightarrow> ('a::len word \<Rightarrow> 'a::len word \<Rightarrow> string \<Rightarrow> bool)"
  where "SHLD_flags b n src dst flag \<equiv> case flag of
        ''cf'' \<Rightarrow> dst !! (LENGTH('a) - n) 
      | ''of'' \<Rightarrow> dst !! (LENGTH('a) - n - 1) \<noteq> dst !! (LENGTH('a) - n)
      | ''zf'' \<Rightarrow> shld b n dst src = 0
      | ''sf'' \<Rightarrow> dst !! (LENGTH('a) - n - 1) \<comment> \<open>msb (shld n dst src)\<close>
      | f      \<Rightarrow> unknown_flags ''SHLD'' f"

definition semantics_SHLD :: "Operand \<Rightarrow> Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_SHLD op1 op2 op3 \<sigma> \<equiv> 
    let src2 = unat (operand_read \<sigma> op3) in
           if operand_size op1 = 32 then binop (shld (TYPE(512)) src2 ::256 word \<Rightarrow> _ \<Rightarrow> _) (SHLD_flags (TYPE(512)) src2) op1 op2 \<sigma>
      else if operand_size op1 = 16 then binop (shld (TYPE(256)) src2 ::128 word \<Rightarrow> _ \<Rightarrow> _) (SHLD_flags (TYPE(256)) src2) op1 op2 \<sigma>
      else if operand_size op1 = 8  then binop (shld (TYPE(128)) src2 ::64  word \<Rightarrow> _ \<Rightarrow> _) (SHLD_flags (TYPE(128)) src2) op1 op2 \<sigma>
      else if operand_size op1 = 4  then binop (shld (TYPE(64))  src2 ::32  word \<Rightarrow> _ \<Rightarrow> _) (SHLD_flags (TYPE(64))  src2) op1 op2 \<sigma>
      else if operand_size op1 = 2  then binop (shld (TYPE(32))  src2 ::16  word \<Rightarrow> _ \<Rightarrow> _) (SHLD_flags (TYPE(32))  src2) op1 op2 \<sigma>
      else if operand_size op1 = 1  then binop (shld (TYPE(16))  src2 ::8   word \<Rightarrow> _ \<Rightarrow> _) (SHLD_flags (TYPE(16))  src2) op1 op2 \<sigma>
      else undefined"



definition ROL_flags :: "nat \<Rightarrow> ('a::len word \<Rightarrow> string \<Rightarrow> bool)" (*TODO check for unaffected flags *)
  where "ROL_flags n dst flag \<equiv> case flag of
        ''cf'' \<Rightarrow> dst !! (LENGTH('a) - n) 
      | ''of'' \<Rightarrow> dst !! (LENGTH('a) - n - 1) \<noteq> dst !! (LENGTH('a) - n)
      | f      \<Rightarrow> unknown_flags ''ROL'' f"

definition semantics_ROL :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state" 
  where "semantics_ROL op1 op2 \<sigma> \<equiv> 
    let src = unat (operand_read \<sigma> op2) in
           if operand_size op1 = 32 then unop (word_rotl src::256 word\<Rightarrow>_) (ROL_flags src) op1 \<sigma>
      else if operand_size op1 = 16 then unop (word_rotl src::128 word\<Rightarrow>_) (ROL_flags src) op1 \<sigma>
      else if operand_size op1 = 8  then unop (word_rotl src::64  word\<Rightarrow>_) (ROL_flags src) op1 \<sigma>
      else if operand_size op1 = 4  then unop (word_rotl src::32  word\<Rightarrow>_) (ROL_flags src) op1 \<sigma>
      else if operand_size op1 = 2  then unop (word_rotl src::16  word\<Rightarrow>_) (ROL_flags src) op1 \<sigma>
      else if operand_size op1 = 1  then unop (word_rotl src::8   word\<Rightarrow>_) (ROL_flags src) op1 \<sigma>
      else undefined"

abbreviation ROL
  where "ROL op1 op2 \<equiv> Instr ''rol'' (Some op1) (Some op2) None"

definition ROR_flags :: "nat \<Rightarrow> ('a::len word \<Rightarrow> string \<Rightarrow> bool)"
  where "ROR_flags n dst flag \<equiv> case flag of
        ''cf'' \<Rightarrow> dst !! (n - 1) 
      | ''of'' \<Rightarrow> msb (word_rotr n dst) \<noteq> (word_rotr n dst !! (LENGTH('a)-2))
      | f      \<Rightarrow> unknown_flags ''ROR'' f"

definition semantics_ROR :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state" 
  where "semantics_ROR op1 op2 \<sigma> \<equiv> 
    let src = unat (operand_read \<sigma> op2) in
           if operand_size op1 = 32 then unop (word_rotr src::256 word\<Rightarrow>_) (ROR_flags src) op1 \<sigma>
      else if operand_size op1 = 16 then unop (word_rotr src::128 word\<Rightarrow>_) (ROR_flags src) op1 \<sigma>
      else if operand_size op1 = 8  then unop (word_rotr src::64  word\<Rightarrow>_) (ROR_flags src) op1 \<sigma>
      else if operand_size op1 = 4  then unop (word_rotr src::32  word\<Rightarrow>_) (ROR_flags src) op1 \<sigma>
      else if operand_size op1 = 2  then unop (word_rotr src::16  word\<Rightarrow>_) (ROR_flags src) op1 \<sigma>
      else if operand_size op1 = 1  then unop (word_rotr src::8   word\<Rightarrow>_) (ROR_flags src) op1 \<sigma>
      else undefined"

abbreviation ROR
  where "ROR op1 op2 \<equiv> Instr ''ror'' (Some op1) (Some op2) None"

text \<open> flag-related \<close>

definition semantics_CMP :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_CMP op1 \<equiv> 
           if operand_size op1 = 32 then binop_flags (SUB_flags::256 word \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _) op1
      else if operand_size op1 = 16 then binop_flags (SUB_flags::128 word \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _) op1
      else if operand_size op1 = 8  then binop_flags (SUB_flags::64  word \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _) op1
      else if operand_size op1 = 4  then binop_flags (SUB_flags::32  word \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _) op1
      else if operand_size op1 = 2  then binop_flags (SUB_flags::16  word \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _) op1
      else if operand_size op1 = 1  then binop_flags (SUB_flags::8   word \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _) op1
      else undefined"

abbreviation CMP
  where "CMP op1 op2 \<equiv> Instr ''cmp'' (Some op1) (Some op2) None"

definition logic_flags :: "('a::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word) \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word \<Rightarrow> string  \<Rightarrow> bool"
  where "logic_flags logic_op w0 w1 flag \<equiv> case flag of
    ''zf'' \<Rightarrow> logic_op w0 w1 = 0
  | ''cf'' \<Rightarrow> False
  | ''of'' \<Rightarrow> False
  | ''sf'' \<Rightarrow> msb (logic_op w0 w1)
  | f      \<Rightarrow> unknown_flags ''logic'' f"

definition semantics_TEST :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_TEST op1 \<equiv> 
           if operand_size op1 = 32 then binop_flags (logic_flags ((AND)::256 word \<Rightarrow> _ \<Rightarrow> _)) op1
      else if operand_size op1 = 16 then binop_flags (logic_flags ((AND)::128 word \<Rightarrow> _ \<Rightarrow> _)) op1
      else if operand_size op1 = 8  then binop_flags (logic_flags ((AND)::64  word \<Rightarrow> _ \<Rightarrow> _)) op1
      else if operand_size op1 = 4  then binop_flags (logic_flags ((AND)::32  word \<Rightarrow> _ \<Rightarrow> _)) op1
      else if operand_size op1 = 2  then binop_flags (logic_flags ((AND)::16  word \<Rightarrow> _ \<Rightarrow> _)) op1
      else if operand_size op1 = 1  then binop_flags (logic_flags ((AND)::8   word \<Rightarrow> _ \<Rightarrow> _)) op1
      else undefined"

abbreviation TEST
  where "TEST op1 op2 \<equiv> Instr ''test'' (Some op1) (Some op2) None"


text \<open> sign extension \<close>
definition mov_sign_extension :: "('a::len) itself \<Rightarrow> ('b::len) itself \<Rightarrow> Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "mov_sign_extension _ _ op1 op2 \<sigma> \<equiv>
          let src = ucast (operand_read \<sigma> op2)::'b word in
             operand_write op1 (ucast (scast src::'a word)) \<sigma>"

definition semantics_MOVSXD :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_MOVSXD op1 op2 \<equiv>
      if (operand_size op1, operand_size op2) = (8,4) then
         mov_sign_extension (TYPE(64)) (TYPE(32)) op1 op2
      else if (operand_size op1, operand_size op2) = (8,2) then
         mov_sign_extension (TYPE(64)) (TYPE(16)) op1 op2
      else if (operand_size op1, operand_size op2) = (8,1) then
         mov_sign_extension (TYPE(64)) (TYPE(8)) op1 op2
      else if (operand_size op1, operand_size op2) = (4,2) then
         mov_sign_extension (TYPE(32)) (TYPE(16)) op1 op2
      else if (operand_size op1, operand_size op2) = (4,1) then
         mov_sign_extension (TYPE(32)) (TYPE(8)) op1 op2
      else if (operand_size op1, operand_size op2) = (2,1) then
         mov_sign_extension (TYPE(16)) (TYPE(8)) op1 op2
      else
        undefined"

abbreviation MOVSXD
  where "MOVSXD op1 op2 \<equiv> Instr ''movsxd'' (Some op1) (Some op2) None"

abbreviation MOVSX
  where "MOVSX op1 op2 \<equiv> Instr ''movsx'' (Some op1) (Some op2) None"

definition semantics_CDQE :: "state \<Rightarrow> state"
  where "semantics_CDQE \<equiv> semantics_MOVSXD (Reg ''rax'') (Reg ''eax'')"

abbreviation CDQE
  where "CDQE \<equiv> Instr ''cdqe'' None None None"

definition semantics_CDQ :: "state \<Rightarrow> state"
  where "semantics_CDQ \<sigma> \<equiv>
          let src = ucast (operand_read \<sigma> (Reg ''eax'')) :: 32 word in
             operand_write (Reg ''edx'') (ucast (\<langle>32,64\<rangle>(scast src::64 word))) \<sigma>"

abbreviation CDQ
  where "CDQ \<equiv> Instr ''cdq'' None None None"

definition semantics_CQO :: "state \<Rightarrow> state"
  where "semantics_CQO \<sigma> \<equiv>
          let src = ucast (operand_read \<sigma> (Reg ''rax'')) :: 64 word in
             operand_write (Reg ''rdx'') (ucast (\<langle>64,128\<rangle>(scast src::128 word))) \<sigma>"

abbreviation CQO
  where "CQO \<equiv> Instr ''cqo'' None None None"


text \<open>logic\<close>
definition semantics_AND :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_AND op1 op2 \<sigma> \<equiv> 
           if operand_size op1 = 32 then binop ((AND)::256 word \<Rightarrow> _ \<Rightarrow> _) (logic_flags ((AND)::256 word \<Rightarrow> _ \<Rightarrow> _)) op1 op2 \<sigma>
      else if operand_size op1 = 16 then binop ((AND)::128 word \<Rightarrow> _ \<Rightarrow> _) (logic_flags ((AND)::128 word \<Rightarrow> _ \<Rightarrow> _)) op1 op2 \<sigma>
      else if operand_size op1 = 8  then binop ((AND)::64  word \<Rightarrow> _ \<Rightarrow> _) (logic_flags ((AND)::64  word \<Rightarrow> _ \<Rightarrow> _)) op1 op2 \<sigma>
      else if operand_size op1 = 4  then binop ((AND)::32  word \<Rightarrow> _ \<Rightarrow> _) (logic_flags ((AND)::32  word \<Rightarrow> _ \<Rightarrow> _)) op1 op2 \<sigma>
      else if operand_size op1 = 2  then binop ((AND)::16  word \<Rightarrow> _ \<Rightarrow> _) (logic_flags ((AND)::16  word \<Rightarrow> _ \<Rightarrow> _)) op1 op2 \<sigma>
      else if operand_size op1 = 1  then binop ((AND)::8   word \<Rightarrow> _ \<Rightarrow> _) (logic_flags ((AND)::8   word \<Rightarrow> _ \<Rightarrow> _)) op1 op2 \<sigma>
      else undefined"

abbreviation AND'
  where "AND' op1 op2 \<equiv> Instr ''and'' (Some op1) (Some op2) None"

definition semantics_OR :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_OR op1 op2 \<sigma> \<equiv> 
           if operand_size op1 = 32 then binop ((OR)::256 word \<Rightarrow> _ \<Rightarrow> _) (logic_flags ((OR)::256 word \<Rightarrow> _ \<Rightarrow> _)) op1 op2 \<sigma>
      else if operand_size op1 = 16 then binop ((OR)::128 word \<Rightarrow> _ \<Rightarrow> _) (logic_flags ((OR)::128 word \<Rightarrow> _ \<Rightarrow> _)) op1 op2 \<sigma>
      else if operand_size op1 = 8  then binop ((OR)::64  word \<Rightarrow> _ \<Rightarrow> _) (logic_flags ((OR)::64  word \<Rightarrow> _ \<Rightarrow> _)) op1 op2 \<sigma>
      else if operand_size op1 = 4  then binop ((OR)::32  word \<Rightarrow> _ \<Rightarrow> _) (logic_flags ((OR)::32  word \<Rightarrow> _ \<Rightarrow> _)) op1 op2 \<sigma>
      else if operand_size op1 = 2  then binop ((OR)::16  word \<Rightarrow> _ \<Rightarrow> _) (logic_flags ((OR)::16  word \<Rightarrow> _ \<Rightarrow> _)) op1 op2 \<sigma>
      else if operand_size op1 = 1  then binop ((OR)::8   word \<Rightarrow> _ \<Rightarrow> _) (logic_flags ((OR)::8   word \<Rightarrow> _ \<Rightarrow> _)) op1 op2 \<sigma>
      else undefined"

abbreviation OR'
  where "OR' op1 op2 \<equiv> Instr ''or'' (Some op1) (Some op2) None"

definition semantics_XOR :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_XOR op1 op2 \<sigma> \<equiv> 
           if operand_size op1 = 32 then binop ((XOR)::256 word \<Rightarrow> _ \<Rightarrow> _) (logic_flags ((XOR)::256 word \<Rightarrow> _ \<Rightarrow> _)) op1 op2 \<sigma>
      else if operand_size op1 = 16 then binop ((XOR)::128 word \<Rightarrow> _ \<Rightarrow> _) (logic_flags ((XOR)::128 word \<Rightarrow> _ \<Rightarrow> _)) op1 op2 \<sigma>
      else if operand_size op1 = 8  then binop ((XOR)::64  word \<Rightarrow> _ \<Rightarrow> _) (logic_flags ((XOR)::64  word \<Rightarrow> _ \<Rightarrow> _)) op1 op2 \<sigma>
      else if operand_size op1 = 4  then binop ((XOR)::32  word \<Rightarrow> _ \<Rightarrow> _) (logic_flags ((XOR)::32  word \<Rightarrow> _ \<Rightarrow> _)) op1 op2 \<sigma>
      else if operand_size op1 = 2  then binop ((XOR)::16  word \<Rightarrow> _ \<Rightarrow> _) (logic_flags ((XOR)::16  word \<Rightarrow> _ \<Rightarrow> _)) op1 op2 \<sigma>
      else if operand_size op1 = 1  then binop ((XOR)::8   word \<Rightarrow> _ \<Rightarrow> _) (logic_flags ((XOR)::8   word \<Rightarrow> _ \<Rightarrow> _)) op1 op2 \<sigma>
      else undefined"

abbreviation XOR'
  where "XOR' op1 op2 \<equiv> Instr ''xor'' (Some op1) (Some op2) None"

definition semantics_XORPS :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_XORPS op1 \<equiv> 
           if operand_size op1 = 32 then binop_no_flags ((XOR)::256 word \<Rightarrow> _ \<Rightarrow> _) op1
      else if operand_size op1 = 16 then binop_no_flags ((XOR)::128 word \<Rightarrow> _ \<Rightarrow> _) op1
      else if operand_size op1 = 8  then binop_no_flags ((XOR)::64  word \<Rightarrow> _ \<Rightarrow> _) op1
      else if operand_size op1 = 4  then binop_no_flags ((XOR)::32  word \<Rightarrow> _ \<Rightarrow> _) op1
      else if operand_size op1 = 2  then binop_no_flags ((XOR)::16  word \<Rightarrow> _ \<Rightarrow> _) op1
      else if operand_size op1 = 1  then binop_no_flags ((XOR)::8   word \<Rightarrow> _ \<Rightarrow> _) op1
      else undefined"

abbreviation XORPS
  where "XORPS op1 op2 \<equiv> Instr ''xorps'' (Some op1) (Some op2) None"

definition semantics_NOT :: "Operand \<Rightarrow> state \<Rightarrow> state" 
  where "semantics_NOT op1 \<sigma> \<equiv> 
           if operand_size op1 = 32 then unop_no_flags (not::256 word\<Rightarrow>_) op1 \<sigma>
      else if operand_size op1 = 16 then unop_no_flags (not::128 word\<Rightarrow>_) op1 \<sigma>
      else if operand_size op1 = 8  then unop_no_flags (not::64  word\<Rightarrow>_) op1 \<sigma>
      else if operand_size op1 = 4  then unop_no_flags (not::32  word\<Rightarrow>_) op1 \<sigma>
      else if operand_size op1 = 2  then unop_no_flags (not::16  word\<Rightarrow>_) op1 \<sigma>
      else if operand_size op1 = 1  then unop_no_flags (not::8   word\<Rightarrow>_) op1 \<sigma>
      else undefined"

abbreviation NOT'
  where "NOT' op1 \<equiv> Instr ''not'' (Some op1) None None"

text \<open> jumps \<close>
datatype FlagExpr = Flag string | FE_NOT FlagExpr | FE_AND FlagExpr FlagExpr | FE_OR FlagExpr FlagExpr | FE_EQ FlagExpr FlagExpr

primrec readFlagExpr :: "FlagExpr \<Rightarrow> state \<Rightarrow> bool"
  where
    "readFlagExpr (Flag f) \<sigma> = (flag_read \<sigma> f = 1)"
  | "readFlagExpr (FE_NOT fe) \<sigma> = (\<not>readFlagExpr fe \<sigma>)"
  | "readFlagExpr (FE_AND fe0 fe1) \<sigma> = (readFlagExpr fe0 \<sigma> \<and> readFlagExpr fe1 \<sigma>)"
  | "readFlagExpr (FE_OR fe0 fe1) \<sigma> = (readFlagExpr fe0 \<sigma> \<or> readFlagExpr fe1 \<sigma>)"
  | "readFlagExpr (FE_EQ fe0 fe1) \<sigma> = (readFlagExpr fe0 \<sigma> \<longleftrightarrow> readFlagExpr fe1 \<sigma>)"

definition semantics_cond_jump :: "FlagExpr \<Rightarrow> 64 word \<Rightarrow> state \<Rightarrow> state"
  where "semantics_cond_jump fe a \<sigma> \<equiv>
          let fv = readFlagExpr fe \<sigma> in
             if fv then state_update (setRip a) \<sigma> else \<sigma>"

definition semantics_JMP :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_JMP op1 \<sigma> \<equiv>
          let a = ucast (operand_read \<sigma> op1) in
            state_update (setRip a) \<sigma>"

abbreviation JMP
  where "JMP op1 \<equiv> Instr ''jmp'' (Some op1) None None"

definition semantics_JO :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_JO op1 \<sigma> \<equiv>
          let a = ucast (operand_read \<sigma> op1) in
             semantics_cond_jump (Flag ''of'') a \<sigma>"

abbreviation JO
  where "JO op1 \<equiv> Instr ''jo'' (Some op1) None None"

definition semantics_JNO :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_JNO op1 \<sigma> \<equiv>
          let a = ucast (operand_read \<sigma> op1) in
             semantics_cond_jump (FE_NOT (Flag ''of'')) a \<sigma>"

abbreviation JNO
  where "JNO op1 \<equiv> Instr ''jno'' (Some op1) None None"

definition semantics_JS :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_JS op1 \<sigma> \<equiv>
          let a = ucast (operand_read \<sigma> op1) in
             semantics_cond_jump (Flag ''sf'') a \<sigma>"

abbreviation JS
  where "JS op1 \<equiv> Instr ''js'' (Some op1) None None"

definition semantics_JNS :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_JNS op1 \<sigma> \<equiv>
          let a = ucast (operand_read \<sigma> op1) in
             semantics_cond_jump (FE_NOT (Flag ''sf'')) a \<sigma>"

abbreviation JNS
  where "JNS op1 \<equiv> Instr ''jns'' (Some op1) None None"

definition semantics_JE :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_JE op1 \<sigma> \<equiv>
          let a = ucast (operand_read \<sigma> op1) in
             semantics_cond_jump (Flag ''zf'') a \<sigma>"

abbreviation JE
  where "JE op1 \<equiv> Instr ''je'' (Some op1) None None"

abbreviation JZ
  where "JZ op1 \<equiv> Instr ''jz'' (Some op1) None None"

definition semantics_JNE :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_JNE op1 \<sigma> \<equiv>
          let a = ucast (operand_read \<sigma> op1) in
             semantics_cond_jump (FE_NOT (Flag ''zf'')) a \<sigma>"

abbreviation JNE
  where "JNE op1 \<equiv> Instr ''jne'' (Some op1) None None"

abbreviation JNZ
  where "JNZ op1 \<equiv> Instr ''jnz'' (Some op1) None None"

definition semantics_JB :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_JB op1 \<sigma> \<equiv>
          let a = ucast (operand_read \<sigma> op1) in
             semantics_cond_jump (Flag ''cf'') a \<sigma>"

abbreviation JB
  where "JB op1 \<equiv> Instr ''jb'' (Some op1) None None"

abbreviation JNAE
  where "JNAE op1 \<equiv> Instr ''jnae'' (Some op1) None None"

abbreviation JC
  where "JC op1 \<equiv> Instr ''jc'' (Some op1) None None"

definition semantics_JNB :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_JNB op1 \<sigma> \<equiv>
          let a = ucast (operand_read \<sigma> op1) in
             semantics_cond_jump (FE_NOT (Flag ''cf'')) a \<sigma>"

abbreviation JNB
  where "JNB op1 \<equiv> Instr ''jnb'' (Some op1) None None"

abbreviation JAE
  where "JAE op1 \<equiv> Instr ''jae'' (Some op1) None None"

abbreviation JNC
  where "JNC op1 \<equiv> Instr ''jnc'' (Some op1) None None"

definition semantics_JBE :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_JBE op1 \<sigma> \<equiv>
          let a = ucast (operand_read \<sigma> op1) in
             semantics_cond_jump (FE_OR (Flag ''cf'') (Flag ''zf'')) a \<sigma>"

abbreviation JBE
  where "JBE op1 \<equiv> Instr ''jbe'' (Some op1) None None"

abbreviation JNA
  where "JNA op1 \<equiv> Instr ''jna'' (Some op1) None None"

definition semantics_JA :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_JA op1 \<sigma> \<equiv>
          let a = ucast (operand_read \<sigma> op1) in
             semantics_cond_jump (FE_AND (FE_NOT (Flag ''cf'')) (FE_NOT (Flag ''zf''))) a \<sigma>"

abbreviation JA
  where "JA op1 \<equiv> Instr ''ja'' (Some op1) None None"

abbreviation JNBE
  where "JNBE op1 \<equiv> Instr ''jnbe'' (Some op1) None None"

definition semantics_JL :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_JL op1 \<sigma> \<equiv>
          let a = ucast (operand_read \<sigma> op1) in
             semantics_cond_jump (FE_NOT (FE_EQ (Flag ''sf'') (Flag ''of''))) a \<sigma>"

abbreviation JL
  where "JL op1 \<equiv> Instr ''jl'' (Some op1) None None"

abbreviation JNGE
  where "JNGE op1 \<equiv> Instr ''jnge'' (Some op1) None None"

definition semantics_JGE :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_JGE op1 \<sigma> \<equiv>
          let a = ucast (operand_read \<sigma> op1) in
             semantics_cond_jump (FE_EQ (Flag ''sf'') (Flag ''of'')) a \<sigma>"

abbreviation JGE
  where "JGE op1 \<equiv> Instr ''jge'' (Some op1) None None"

abbreviation JNL
  where "JNL op1 \<equiv> Instr ''jnl'' (Some op1) None None"

definition semantics_JLE :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_JLE op1 \<sigma> \<equiv>
          let a = ucast (operand_read \<sigma> op1) in
             semantics_cond_jump (FE_OR (Flag ''zf'') (FE_NOT (FE_EQ (Flag ''sf'') (Flag ''of'')))) a \<sigma>"

abbreviation JLE
  where "JLE op1 \<equiv> Instr ''jle'' (Some op1) None None"

abbreviation JNG
  where "JNG op1 \<equiv> Instr ''jng'' (Some op1) None None"

definition semantics_JG :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_JG op1 \<sigma> \<equiv>
          let a = ucast (operand_read \<sigma> op1) in
             semantics_cond_jump (FE_AND (FE_NOT (Flag ''zf'')) (FE_EQ (Flag ''sf'') (Flag ''of''))) a \<sigma>"

abbreviation JG
  where "JG op1 \<equiv> Instr ''jg'' (Some op1) None None"

abbreviation JNLE
  where "JNLE op1 \<equiv> Instr ''jnle'' (Some op1) None None"


text \<open> setXX \<close>
definition semantics_setXX :: "FlagExpr \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_setXX fe op1 \<sigma> \<equiv>
          let fv = readFlagExpr fe \<sigma> in
             operand_write op1 (fromBool fv) \<sigma>"

abbreviation semantics_SETO :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_SETO \<equiv> semantics_setXX (Flag ''of'')"

abbreviation SETO
  where "SETO op1 \<equiv> Instr ''seto'' (Some op1) None None"

abbreviation semantics_SETNO :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_SETNO \<equiv> semantics_setXX (FE_NOT (Flag ''of''))"

abbreviation SETNO
  where "SETNO op1 \<equiv> Instr ''setno'' (Some op1) None None"

abbreviation semantics_SETS :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_SETS \<equiv> semantics_setXX (Flag ''sf'')"

abbreviation SETS
  where "SETS op1 \<equiv> Instr ''sets'' (Some op1) None None"

abbreviation semantics_SETNS :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_SETNS \<equiv> semantics_setXX (FE_NOT (Flag ''sf''))"

abbreviation SETNS
  where "SETNS op1 \<equiv> Instr ''setns'' (Some op1) None None"

abbreviation semantics_SETE :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_SETE \<equiv> semantics_setXX (Flag ''zf'')"

abbreviation SETE
  where "SETE op1 \<equiv> Instr ''sete'' (Some op1) None None"

abbreviation SETZ
  where "SETZ op1 \<equiv> Instr ''setz'' (Some op1) None None"

abbreviation semantics_SETNE :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_SETNE \<equiv> semantics_setXX (FE_NOT (Flag ''zf''))"

abbreviation SETNE
  where "SETNE op1 \<equiv> Instr ''setne'' (Some op1) None None"

abbreviation SETNZ
  where "SETNZ op1 \<equiv> Instr ''setnz'' (Some op1) None None"

abbreviation semantics_SETB :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_SETB \<equiv> semantics_setXX (Flag ''cf'')"

abbreviation SETB
  where "SETB op1 \<equiv> Instr ''setb'' (Some op1) None None"

abbreviation SETNAE
  where "SETNAE op1 \<equiv> Instr ''setnae'' (Some op1) None None"

abbreviation SETC
  where "SETC op1 \<equiv> Instr ''setc'' (Some op1) None None"

abbreviation semantics_SETNB :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_SETNB \<equiv> semantics_setXX (FE_NOT (Flag ''cf''))"

abbreviation SETNB
  where "SETNB op1 \<equiv> Instr ''setnb'' (Some op1) None None"

abbreviation SETAE
  where "SETAE op1 \<equiv> Instr ''setae'' (Some op1) None None"

abbreviation SETNC
  where "SETNC op1 \<equiv> Instr ''setnc'' (Some op1) None None"

abbreviation semantics_SETBE :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_SETBE \<equiv> semantics_setXX (FE_OR (Flag ''cf'') (Flag ''zf''))"

abbreviation SETBE
  where "SETBE op1 \<equiv> Instr ''setbe'' (Some op1) None None"

abbreviation SETNA
  where "SETNA op1 \<equiv> Instr ''setna'' (Some op1) None None"

abbreviation semantics_SETA :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_SETA \<equiv> semantics_setXX (FE_AND (FE_NOT (Flag ''cf'')) (FE_NOT (Flag ''zf'')))"

abbreviation SETA
  where "SETA op1 \<equiv> Instr ''seta'' (Some op1) None None"

abbreviation SETNBE
  where "SETNBE op1 \<equiv> Instr ''setnbe'' (Some op1) None None"

abbreviation semantics_SETL :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_SETL \<equiv> semantics_setXX (FE_NOT (FE_EQ (Flag ''sf'') (Flag ''of'')))"

abbreviation SETL
  where "SETL op1 \<equiv> Instr ''setl'' (Some op1) None None"

abbreviation SETNGE
  where "SETNGE op1 \<equiv> Instr ''setnge'' (Some op1) None None"

abbreviation semantics_SETGE :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_SETGE \<equiv> semantics_setXX (FE_EQ (Flag ''sf'') (Flag ''of''))"

abbreviation SETGE
  where "SETGE op1 \<equiv> Instr ''setge'' (Some op1) None None"

abbreviation SETNL
  where "SETNL op1 \<equiv> Instr ''setnl'' (Some op1) None None"

abbreviation semantics_SETLE :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_SETLE \<equiv> semantics_setXX (FE_OR (Flag ''zf'') (FE_NOT (FE_EQ (Flag ''sf'') (Flag ''of''))))"

abbreviation SETLE
  where "SETLE op1 \<equiv> Instr ''setle'' (Some op1) None None"

abbreviation SETNG
  where "SETNG op1 \<equiv> Instr ''setng'' (Some op1) None None"

abbreviation semantics_SETG :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_SETG \<equiv> semantics_setXX (FE_AND (FE_NOT (Flag ''zf'')) (FE_EQ (Flag ''sf'') (Flag ''of'')))"

abbreviation SETG
  where "SETG op1 \<equiv> Instr ''setg'' (Some op1) None None"

abbreviation SETNLE
  where "SETNLE op1 \<equiv> Instr ''setnle'' (Some op1) None None"


text \<open> conditional moves \<close>

primrec cmov
  where 
    "cmov True dst src = src"
  | "cmov False dst src = dst"

definition semantics_CMOV :: "FlagExpr \<Rightarrow> Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_CMOV fe op1 op2 \<sigma> \<equiv>
          let fv = readFlagExpr fe \<sigma>;
              dst = operand_read \<sigma> op1;
              src = operand_read \<sigma> op2 in
            operand_write op1 (cmov fv dst src) \<sigma>"

abbreviation "semantics_CMOVNE \<equiv> semantics_CMOV (FE_NOT (Flag ''zf''))"

abbreviation CMOVNE
  where "CMOVNE op1 op2 \<equiv> Instr ''movne'' (Some op1) (Some op2) None"

abbreviation "semantics_CMOVNS \<equiv> semantics_CMOV (FE_NOT (Flag ''sf''))"

abbreviation CMOVNS
  where "CMOVNS op1 op2 \<equiv> Instr ''movns'' (Some op1) (Some op2) None"


text \<open>Floating Point\<close>
definition semantics_ADDSD :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_ADDSD \<equiv> binop_XMM unknown_addsd"

definition semantics_SUBSD :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_SUBSD \<equiv> binop_XMM unknown_subsd"

definition semantics_MULSD :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_MULSD \<equiv> binop_XMM unknown_mulsd"

definition semantics_DIVSD :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_DIVSD \<equiv> binop_XMM unknown_divsd"

definition UCOMISD_flags :: "64 word \<Rightarrow> 64 word \<Rightarrow> string \<Rightarrow> bool"
  where "UCOMISD_flags w0 w1 f \<equiv> 
  if f \<in> {''zf'',''pf'',''cf''} then case unknown_ucomisd w0 w1 of
      FP_Unordered \<Rightarrow> True
    | FP_GT        \<Rightarrow> False
    | FP_LT        \<Rightarrow> f = ''cf''
    | FP_EQ        \<Rightarrow> f = ''zf''
  else
    unknown_flags ''UCOMISD'' f"

definition semantics_UCOMISD :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_UCOMISD \<equiv> binop_flags UCOMISD_flags"


abbreviation ADDSD
  where "ADDSD op1 op2 \<equiv> Instr ''addsd'' (Some op1) (Some op2) None"

abbreviation SUBSD
  where "SUBSD op1 op2 \<equiv> Instr ''subsd'' (Some op1) (Some op2) None"

abbreviation MULSD
  where "MULSD op1 op2 \<equiv> Instr ''mulsd'' (Some op1) (Some op2) None"

abbreviation DIVSD
  where "DIVSD op1 op2 \<equiv> Instr ''divsd'' (Some op1) (Some op2) None"

abbreviation UCOMISD
  where "UCOMISD op1 op2 \<equiv> Instr ''ucomisd'' (Some op1) (Some op2) None"



(* SIMD *)

definition simd_32_128 :: "(32 word \<Rightarrow> 32 word \<Rightarrow> 32 word) \<Rightarrow> 128 word \<Rightarrow> 128 word \<Rightarrow> 128 word" 
  where "simd_32_128 f dst src \<equiv> 
            ((ucast (\<langle>0,32\<rangle>(f (ucast (\<langle>96,128\<rangle>dst)) (ucast (\<langle>96,128\<rangle>src))))) << 96) OR
            ((ucast (\<langle>0,32\<rangle>(f (ucast (\<langle>64,96\<rangle>dst))  (ucast (\<langle>64,96\<rangle>src))))) << 64)  OR
            ((ucast (\<langle>0,32\<rangle>(f (ucast (\<langle>32,64\<rangle>dst))  (ucast (\<langle>32,64\<rangle>src))))) << 32)  OR
             (ucast (\<langle>0,32\<rangle>(f (ucast (\<langle>0,32\<rangle>dst))   (ucast (\<langle>0,32\<rangle>src)))))"

abbreviation semantics_PADDD :: "Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_PADDD \<equiv> binop_no_flags (simd_32_128 (+))"

abbreviation PADDD
  where "PADDD op1 op2 \<equiv> Instr ''paddd'' (Some op1) (Some op2) None"

definition pshufd :: "128 word \<Rightarrow> 8 word \<Rightarrow> 128 word"
  where "pshufd src n \<equiv> ((\<langle>0,32\<rangle>(src >> (unat (\<langle>6,8\<rangle>n)*32))) << 96) OR
                        ((\<langle>0,32\<rangle>(src >> (unat (\<langle>4,6\<rangle>n)*32))) << 64) OR
                        ((\<langle>0,32\<rangle>(src >> (unat (\<langle>2,4\<rangle>n)*32))) << 32) OR
                        ((\<langle>0,32\<rangle>(src >> (unat (\<langle>0,2\<rangle>n)*32))))"

lemmas pshufd_numeral[simp] = pshufd_def[of "numeral n"] for n
lemmas pshufd_0[simp] = pshufd_def[of 0]
lemmas pshufd_1[simp] = pshufd_def[of 1]

definition semantics_PSHUFD :: "Operand \<Rightarrow> Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_PSHUFD op1 op2 op3 \<sigma> \<equiv> 
    let src = ucast (operand_read \<sigma> op2);
        n   = ucast (operand_read \<sigma> op3) in
      operand_write op1 (ucast (pshufd src n)) \<sigma>"

abbreviation PSHUFD
  where "PSHUFD op1 op2 op3 \<equiv> Instr ''pshufd'' op1 op2 op3"

definition semantics_PEXTRD :: "Operand \<Rightarrow> Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_PEXTRD op1 op2 op3 \<sigma> \<equiv>
          let src = operand_read \<sigma> op2;
              n   = unat (operand_read \<sigma> op3) mod 4 in
             operand_write op1 (ucast ((\<langle>0,32\<rangle>(src >> n*32)))) \<sigma>"

abbreviation PEXTRD
  where "PEXTRD op1 op2 op3 \<equiv> Instr ''pextrd'' op1 op2 op3"

definition semantics_PINSRD :: "Operand \<Rightarrow> Operand \<Rightarrow> Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_PINSRD op1 op2 op3 \<sigma> \<equiv>
          let dst = ucast (operand_read \<sigma> op1)::128 word;
              src = ucast (operand_read \<sigma> op2)::128 word;
              n   = unat (operand_read \<sigma> op3) mod 4;
              m   = 0xFFFFFFFF << (n * 32) :: 128 word;
              t   = (src << (n *32)) AND m in
             operand_write op1 (ucast ((dst AND NOT m) OR t)) \<sigma>"

abbreviation PINSRD
  where "PINSRD op1 op2 op3 \<equiv> Instr ''pinsrd'' op1 op2 op3"


(* remainder *)



definition bswap :: "32 word \<Rightarrow> 32 word"
  where "bswap w \<equiv> ((\<langle>0,8\<rangle>w) << 24) OR ((\<langle>8,16\<rangle>w) << 16) OR ((\<langle>16,24\<rangle>w) << 8) OR (\<langle>24,32\<rangle>w)"

lemmas bswap_numeral[simp] = bswap_def[of "numeral n"] for n
lemmas bswap_0[simp] = bswap_def[of 0]
lemmas bswap_1[simp] = bswap_def[of 1]

definition semantics_BSWAP :: "Operand \<Rightarrow> state \<Rightarrow> state"
  where "semantics_BSWAP \<equiv> unop_no_flags bswap"

abbreviation BSWAP
  where "BSWAP op1 \<equiv> Instr ''bswap'' op1 None None"



definition semantics_NOP :: "state \<Rightarrow> state"
  where "semantics_NOP \<equiv> id"

abbreviation NOP0
  where "NOP0 \<equiv> Instr ''nop'' None None None"

abbreviation NOP1
  where "NOP1 op1 \<equiv> Instr ''nop'' (Some op1) None None"

abbreviation NOP2
  where "NOP2 op1 op2 \<equiv> Instr ''nop'' (Some op1) (Some op2) None"

abbreviation NOP3
  where "NOP3 op1 op2 op3 \<equiv> Instr ''nop'' (Some op1) (Some op2) (Some op3)"



definition semantics
  where "semantics i \<equiv>
  case i of
    (Instr ''mov''     (Some op1) (Some op2) _ _)          \<Rightarrow> semantics_MOV op1 op2
  | (Instr ''movabs''  (Some op1) (Some op2) _ _)          \<Rightarrow> semantics_MOV op1 op2
  | (Instr ''movaps''  (Some op1) (Some op2) _ _)          \<Rightarrow> semantics_MOV op1 op2
  | (Instr ''movdqu''  (Some op1) (Some op2) _ _)          \<Rightarrow> semantics_MOV op1 op2
  | (Instr ''movd''    (Some op1) (Some op2) _ _)          \<Rightarrow> semantics_MOVD op1 op2
  | (Instr ''movzx''   (Some op1) (Some op2) _ _)          \<Rightarrow> semantics_MOV op1 op2
  | (Instr ''movsd''   (Some op1) (Some op2) _ _)          \<Rightarrow> semantics_MOVSD op1 op2
  | (Instr ''movq''    (Some op1) (Some op2) _ _)          \<Rightarrow> semantics_MOVSD op1 op2
  | (Instr ''lea''     (Some op1) (Some op2) _ _)          \<Rightarrow> semantics_LEA op1 op2
  | (Instr ''push''    (Some op1) _          _ _)          \<Rightarrow> semantics_PUSH op1
  | (Instr ''pop''     (Some op1) _          _ _)          \<Rightarrow> semantics_POP op1
  | (Instr ''ret''     _ _ _ _)                            \<Rightarrow> semantics_RET
  | (Instr ''call''    (Some op1) _ _ _)                   \<Rightarrow> semantics_CALL op1
  | (Instr ''leave''   _ _ _ _)                            \<Rightarrow> semantics_LEAVE
  \<comment> \<open>arithmetic\<close>                                           
  | (Instr ''add''     (Some op1) (Some op2)  _ _)         \<Rightarrow> semantics_ADD op1 op2
  | (Instr ''inc''     (Some op1) _           _ _)         \<Rightarrow> semantics_INC op1
  | (Instr ''dec''     (Some op1) _           _ _)         \<Rightarrow> semantics_DEC op1
  | (Instr ''neg''     (Some op1) _           _ _)         \<Rightarrow> semantics_NEG op1
  | (Instr ''sub''     (Some op1) (Some op2)  _ _)         \<Rightarrow> semantics_SUB op1 op2
  | (Instr ''sbb''     (Some op1) (Some op2)  _ _)         \<Rightarrow> semantics_SBB op1 op2
  | (Instr ''adc''     (Some op1) (Some op2)  _ _)         \<Rightarrow> semantics_ADC op1 op2
  | (Instr ''mul''     (Some op1) _ _ _)                   \<Rightarrow> semantics_MUL op1 
  | (Instr ''imul''    (Some op1) None _ _)                \<Rightarrow> semantics_IMUL1 op1 
  | (Instr ''imul''    (Some op1) (Some op2) None _)       \<Rightarrow> semantics_IMUL2 op1 op2
  | (Instr ''imul''    (Some op1) (Some op2) (Some op3) _) \<Rightarrow> semantics_IMUL3 op1 op2 op3
  | (Instr ''shl''     (Some op1) (Some op2) None _)       \<Rightarrow> semantics_SHL op1 op2
  | (Instr ''sal''     (Some op1) (Some op2) None _)       \<Rightarrow> semantics_SHL op1 op2
  | (Instr ''shr''     (Some op1) (Some op2) None _)       \<Rightarrow> semantics_SHR op1 op2
  | (Instr ''sar''     (Some op1) (Some op2) None _)       \<Rightarrow> semantics_SAR op1 op2
  | (Instr ''shld''    (Some op1) (Some op2) (Some op3) _) \<Rightarrow> semantics_SHLD op1 op2 op3
  | (Instr ''rol''     (Some op1) (Some op2) None _)       \<Rightarrow> semantics_ROL op1 op2
  | (Instr ''ror''     (Some op1) (Some op2) None _)       \<Rightarrow> semantics_ROR op1 op2
  \<comment> \<open>flag-related\<close>
  | (Instr ''cmp''     (Some op1) (Some op2)  _ _)         \<Rightarrow> semantics_CMP op1 op2
  | (Instr ''test''    (Some op1) (Some op2)  _ _)         \<Rightarrow> semantics_TEST op1 op2
  \<comment> \<open>sign-extension\<close>                                       
  | (Instr ''movsxd''  (Some op1) (Some op2)  _ _)         \<Rightarrow> semantics_MOVSXD op1 op2
  | (Instr ''movsx''   (Some op1) (Some op2)  _ _)         \<Rightarrow> semantics_MOVSXD op1 op2
  | (Instr ''cdqe''    (Some op1) (Some op2)  _ _)         \<Rightarrow> semantics_CDQE
  | (Instr ''cdq''     (Some op1) (Some op2)  _ _)         \<Rightarrow> semantics_CDQ
  | (Instr ''cqo''     (Some op1) (Some op2)  _ _)         \<Rightarrow> semantics_CQO
  \<comment> \<open>logic\<close>
  | (Instr ''and''     (Some op1) (Some op2)  _ _)         \<Rightarrow> semantics_AND op1 op2
  | (Instr ''or''      (Some op1) (Some op2)  _ _)         \<Rightarrow> semantics_OR  op1 op2
  | (Instr ''xor''     (Some op1) (Some op2)  _ _)         \<Rightarrow> semantics_XOR op1 op2
  | (Instr ''xorps''   (Some op1) (Some op2)  _ _)         \<Rightarrow> semantics_XORPS op1 op2
  | (Instr ''not''     (Some op1) _  _ _)                  \<Rightarrow> semantics_NOT op1
  \<comment> \<open>jumps\<close>
  | (Instr ''jmp''     (Some op1) None  _ _)               \<Rightarrow> semantics_JMP op1
  | (Instr ''jo''      (Some op1) None  _ _)               \<Rightarrow> semantics_JO op1
  | (Instr ''jno''     (Some op1) None  _ _)               \<Rightarrow> semantics_JNO op1
  | (Instr ''js''      (Some op1) None  _ _)               \<Rightarrow> semantics_JS op1
  | (Instr ''jns''     (Some op1) None  _ _)               \<Rightarrow> semantics_JNS op1
  | (Instr ''je''      (Some op1) None  _ _)               \<Rightarrow> semantics_JE op1
  | (Instr ''jz''      (Some op1) None  _ _)               \<Rightarrow> semantics_JE op1
  | (Instr ''jne''     (Some op1) None  _ _)               \<Rightarrow> semantics_JNE op1
  | (Instr ''jnz''     (Some op1) None  _ _)               \<Rightarrow> semantics_JNE op1
  | (Instr ''jb''      (Some op1) None  _ _)               \<Rightarrow> semantics_JB op1
  | (Instr ''jnae''    (Some op1) None  _ _)               \<Rightarrow> semantics_JB op1
  | (Instr ''jc''      (Some op1) None  _ _)               \<Rightarrow> semantics_JB op1
  | (Instr ''jnb''     (Some op1) None  _ _)               \<Rightarrow> semantics_JNB op1
  | (Instr ''jae''     (Some op1) None  _ _)               \<Rightarrow> semantics_JNB op1
  | (Instr ''jnc''     (Some op1) None  _ _)               \<Rightarrow> semantics_JNB op1
  | (Instr ''jbe''     (Some op1) None  _ _)               \<Rightarrow> semantics_JBE op1
  | (Instr ''jna''     (Some op1) None  _ _)               \<Rightarrow> semantics_JBE op1
  | (Instr ''ja''      (Some op1) None  _ _)               \<Rightarrow> semantics_JA op1
  | (Instr ''jnbe''    (Some op1) None  _ _)               \<Rightarrow> semantics_JA op1
  | (Instr ''jl''      (Some op1) None  _ _)               \<Rightarrow> semantics_JL op1
  | (Instr ''jnge''    (Some op1) None  _ _)               \<Rightarrow> semantics_JL op1
  | (Instr ''jge''     (Some op1) None  _ _)               \<Rightarrow> semantics_JGE op1
  | (Instr ''jnl''     (Some op1) None  _ _)               \<Rightarrow> semantics_JGE op1
  | (Instr ''jle''     (Some op1) None  _ _)               \<Rightarrow> semantics_JLE op1
  | (Instr ''jng''     (Some op1) None  _ _)               \<Rightarrow> semantics_JLE op1
  | (Instr ''jg''      (Some op1) None  _ _)               \<Rightarrow> semantics_JG op1
  | (Instr ''jnle''    (Some op1) None  _ _)               \<Rightarrow> semantics_JG op1
  \<comment> \<open>setXX\<close>
  | (Instr ''seto''    (Some op1) None  _ _)               \<Rightarrow> semantics_SETO op1
  | (Instr ''setno''   (Some op1) None  _ _)               \<Rightarrow> semantics_SETNO op1
  | (Instr ''sets''    (Some op1) None  _ _)               \<Rightarrow> semantics_SETS op1
  | (Instr ''setns''   (Some op1) None  _ _)               \<Rightarrow> semantics_SETNS op1
  | (Instr ''sete''    (Some op1) None  _ _)               \<Rightarrow> semantics_SETE op1
  | (Instr ''setz''    (Some op1) None  _ _)               \<Rightarrow> semantics_SETE op1
  | (Instr ''setne''   (Some op1) None  _ _)               \<Rightarrow> semantics_SETNE op1
  | (Instr ''setnz''   (Some op1) None  _ _)               \<Rightarrow> semantics_SETNE op1
  | (Instr ''setb''    (Some op1) None  _ _)               \<Rightarrow> semantics_SETB op1
  | (Instr ''setnae''  (Some op1) None  _ _)               \<Rightarrow> semantics_SETB op1
  | (Instr ''setc''    (Some op1) None  _ _)               \<Rightarrow> semantics_SETB op1
  | (Instr ''setnb''   (Some op1) None  _ _)               \<Rightarrow> semantics_SETNB op1
  | (Instr ''setae''   (Some op1) None  _ _)               \<Rightarrow> semantics_SETNB op1
  | (Instr ''setnc''   (Some op1) None  _ _)               \<Rightarrow> semantics_SETNB op1
  | (Instr ''setbe''   (Some op1) None  _ _)               \<Rightarrow> semantics_SETBE op1
  | (Instr ''setna''   (Some op1) None  _ _)               \<Rightarrow> semantics_SETBE op1
  | (Instr ''seta''    (Some op1) None  _ _)               \<Rightarrow> semantics_SETA op1
  | (Instr ''setnbe''  (Some op1) None  _ _)               \<Rightarrow> semantics_SETA op1
  | (Instr ''setl''    (Some op1) None  _ _)               \<Rightarrow> semantics_SETL op1
  | (Instr ''setnge''  (Some op1) None  _ _)               \<Rightarrow> semantics_SETL op1
  | (Instr ''setge''   (Some op1) None  _ _)               \<Rightarrow> semantics_SETGE op1
  | (Instr ''setnl''   (Some op1) None  _ _)               \<Rightarrow> semantics_SETGE op1
  | (Instr ''setle''   (Some op1) None  _ _)               \<Rightarrow> semantics_SETLE op1
  | (Instr ''setng''   (Some op1) None  _ _)               \<Rightarrow> semantics_SETLE op1
  | (Instr ''setg''    (Some op1) None  _ _)               \<Rightarrow> semantics_SETG op1
  | (Instr ''setnle''  (Some op1) None  _ _)               \<Rightarrow> semantics_SETG op1
  \<comment> \<open>conditional moves\<close>
  | (Instr ''cmovne''  (Some op1) (Some op2)  _ _)         \<Rightarrow> semantics_CMOVNE op1 op2
  | (Instr ''cmovns''  (Some op1) (Some op2)  _ _)         \<Rightarrow> semantics_CMOVNS op1 op2
  \<comment> \<open>floating point (double)\<close>                                           
  | (Instr ''addsd''   (Some op1) (Some op2)  _ _)         \<Rightarrow> semantics_ADDSD op1 op2
  | (Instr ''subsd''   (Some op1) (Some op2)  _ _)         \<Rightarrow> semantics_SUBSD op1 op2
  | (Instr ''mulsd''   (Some op1) (Some op2)  _ _)         \<Rightarrow> semantics_MULSD op1 op2
  | (Instr ''divsd''   (Some op1) (Some op2)  _ _)         \<Rightarrow> semantics_DIVSD op1 op2
  | (Instr ''ucomisd'' (Some op1) (Some op2)  _ _)         \<Rightarrow> semantics_UCOMISD op1 op2
  \<comment> \<open>simd\<close>
  | (Instr ''paddd''   (Some op1) (Some op2) _ _)          \<Rightarrow> semantics_PADDD op1 op2
  | (Instr ''pshufd''  (Some op1) (Some op2) (Some op3) _) \<Rightarrow> semantics_PSHUFD op1 op2 op3
  | (Instr ''pextrd''  (Some op1) (Some op2) (Some op3) _) \<Rightarrow> semantics_PEXTRD op1 op2 op3
  | (Instr ''pinsrd''  (Some op1) (Some op2) (Some op3) _) \<Rightarrow> semantics_PINSRD op1 op2 op3
  \<comment> \<open>remainder\<close>
  | (Instr ''nop''     _ _ _ _)                            \<Rightarrow> semantics_NOP
  | (Instr ''bswap''   (Some op1) _ _ _)                   \<Rightarrow> semantics_BSWAP op1
  \<comment> \<open>external function\<close>
  | (ExternalFunc f) \<Rightarrow> f
  | i \<Rightarrow> unknown_semantics i"


text \<open>A step function. In X86. the RIP register is incremented before the instruction is executed.
      This is important, e.g., when RIP is used in a jump address.\<close>
definition step :: "I \<Rightarrow> state \<Rightarrow> state" 
  where "step i \<sigma> \<equiv> 
    let \<sigma>' = \<sigma> with [setRip (instr_next i)] in
      semantics i \<sigma>'"


text \<open>All simplification rules used during symbolic execution.\<close>
lemmas semantics_simps = 
      Let_def unop_def unop_no_flags_def binop_def binop_flags_def binop_no_flags_def binop_XMM_def
      semantics_def mov_sign_extension_def simd_32_128_def
      write_MUL_result_def unop_MUL_def ternop_IMUL_def sbb_def adc_def shld_def

      semantics_MOV_def semantics_MOVSD_def semantics_MOVD_def semantics_CMOV_def
      semantics_LEA_def semantics_PUSH_def semantics_POP_def
      semantics_RET_def semantics_CALL_def semantics_LEAVE_def
      semantics_ADD_def semantics_INC_def semantics_DEC_def semantics_NEG_def semantics_SUB_def
      semantics_SBB_def semantics_ADC_def
      semantics_MUL_def semantics_IMUL1_def semantics_IMUL2_def semantics_IMUL3_def
      semantics_SHL_def semantics_SHR_def semantics_SAR_def semantics_SHLD_def
      semantics_ROL_def semantics_ROR_def
      semantics_CMP_def semantics_TEST_def
      semantics_MOVSXD_def semantics_CDQE_def semantics_CDQ_def semantics_CQO_def
      semantics_AND_def semantics_OR_def semantics_XOR_def semantics_XORPS_def semantics_NOT_def
      semantics_cond_jump_def semantics_JMP_def
      semantics_JO_def semantics_JNO_def semantics_JS_def semantics_JNS_def
      semantics_JE_def semantics_JNE_def semantics_JB_def semantics_JNB_def
      semantics_JBE_def semantics_JA_def semantics_JL_def semantics_JGE_def 
      semantics_JLE_def semantics_JG_def
      semantics_setXX_def 
      semantics_ADDSD_def semantics_SUBSD_def semantics_MULSD_def semantics_DIVSD_def semantics_UCOMISD_def
      semantics_NOP_def semantics_BSWAP_def semantics_PSHUFD_def semantics_PEXTRD_def semantics_PINSRD_def

      SUB_flags_def ADD_flags_def INC_flags_def DEC_flags_def NEG_flags_def MUL_flags_def IMUL_flags_def
      SHL_flags_def SHR_flags_def SAR_flags_def SHLD_flags_def logic_flags_def UCOMISD_flags_def


end
end