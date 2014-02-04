(******************************************************************************)
(* Project: CML model for Isabelle/UTP                                        *)
(* File: BitRegister_procs.thy                                                *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* CML Dwarf Signal Example with Procedures *}

(*<*)
theory BitRegister_procs
imports 
  "../utp_cml"
begin
(*>*)

text {* The ``bit-register'' is a simple process which performs
arithmetic calculations on a byte state variable. It detects overflow
and underflow if and when it occurs and informs the user. A byte is
represented as a integer with the invariant that the value must be
between 0 and 255.*}

definition 
  "Byte \<equiv> \<parallel>@int inv n == (^n^ >= 0) and (^n^ <= 255)\<parallel>"

declare Byte_def [cmlty_defs]

text {* We can now prove some simple membership theorems for
\texttt{Byte}. For instance the following lemma states that 1 is 
a \texttt{Byte}: *}

lemma Byte_1: 
  "|1 hasType @Byte| = |true|"
  by (cml_tac)

text {* We discharge this theorem by application of \textsf{cml\_tac},
a tactic for solving logical tautologies over CML
expressions. Internally this compiles the expression down to a HOL
expression and then uses standard Isabelle rules to discharge
it. Likewise we can show that 64 is a \texttt{Byte}: *}

lemma Byte_64: 
  "|64 hasType @Byte| = |true|"
  by (cml_tac)

text {* In contrast, 512 is not a \texttt{Byte} as it is over 255, as
shown below: *}

lemma not_Byte_512:
  "|512 hasType @Byte| = |false|"
  by (cml_tac)

text {* The bit-register has two functions: \texttt{oflow} for
detecting overflow caused by a summation, and \texttt{uflow} for
detecting underflow caused by a substraction. Both take a pair of
integers and return a boolean if over/underflow occurs. Functions 
in CML are desugared to lambda terms . *}

definition 
  "oflow = |lambda d @ (^d^.#1 + ^d^.#2) > 255|"

(*<*)declare oflow_def [cmlfun_defs](*>*)

definition 
  "uflow = |lambda d @ (^d^.#1 - ^d^.#2) < 0|"

(*<*)declare uflow_def [cmlfun_defs](*>*)

text {* For example an overflow can occur if we try to add together
200 and 100, as proved below: *}

lemma oflow_ex1:
  "|oflow(200,100)| = |true|"
  by (cml_tac)

text {* On the other hand it is fine to add 150 and 100: *}

lemma oflow_ex2:
  "|oflow(150,100)| = |false|"
  by (cml_tac)

text {* Next we declare the channels for the bit-register, of which
there are seven. Channels in CML can carry data so they all take a
type to specify this. Channels which carry no data simply carry the
unit type \texttt{()}. \texttt{init} is used to signal that the
bit-register should initialise. \texttt{overflow} and
\texttt{underflow} are used to communicate errors during a
calculation. \texttt{read} and \texttt{load} are used to read the
contents of the state and write a new values,
respectively. \texttt{add} and \texttt{sub} are used to signal an
addition or subtraction should be executed. *}

definition "init = MkChanD ''init'' \<parallel>()\<parallel>"
definition "overflow = MkChanD ''overflow'' \<parallel>()\<parallel>"
definition "underflow = MkChanD ''underflow'' \<parallel>()\<parallel>"
definition "read = MkChanD ''read'' \<parallel>@Byte\<parallel>"
definition "load = MkChanD ''load'' \<parallel>@Byte\<parallel>"
definition "add = MkChanD ''add'' \<parallel>@Byte\<parallel>"
definition "sub = MkChanD ''add'' \<parallel>@Byte\<parallel>"

declare init_def [cmlchan_defs]
declare overflow_def [cmlchan_defs]
declare underflow_def [cmlchan_defs]
declare read_def [cmlchan_defs]
declare load_def [cmlchan_defs]
declare add_def [cmlchan_defs]
declare sub_def [cmlchan_defs]

text {* We use an Isabelle locale to create a new namespace for the
\texttt{RegisterProc}. *}

locale RegisterProc
begin

text {* The single state variable, \texttt{reg}, holds the current
value of the calculation. *}

abbreviation "reg \<equiv> MkVarD ''reg'' \<parallel>@Byte\<parallel>"

definition "RegisterProc_inv = `\<lparr> $reg hasType @Byte \<rparr> \<turnstile> \<lparr> $reg\<acute> hasType @Byte \<rparr>`"

declare RegisterProc_inv_def [cmlproc_defs]

text {* Now we declare the operations of the
bit-register. \texttt{INIT} initialises the state variables to 0. *}

definition "pre_INIT = (\<lambda> inp. |true| )"

declare pre_INIT_def [cmlop_defs]

definition "post_INIT = (\<lambda> inp outp. |true| )"

declare post_INIT_def [cmlop_defs]

definition "body_INIT inp = {: reg := 0 :}"

declare body_INIT_def [cmlop_defs]

definition "INIT = CMLOpO \<parallel>()\<parallel> \<parallel>()\<parallel> pre_INIT post_INIT body_INIT"

declare INIT_def [cmlop_defs]

lemma INIT_sat_inv:
  "RegisterProc_inv \<sqsubseteq> `call INIT[]`"
  apply (unfold_cml)
  apply (rule DesignD_refine)
  apply (force intro:refine)
  apply (rule AndP_refines_2)
  apply (rule AssignR_refine_alt)
  apply (simp_all add:closure typing defined unrest usubst) 
  apply (cml_tac)
done

text {* \texttt{LOAD} sets the register to a particular value. *}

definition "pre_LOAD(inp)        = |true|"

declare pre_LOAD_def [cmlop_defs]

definition "post_LOAD(inp)(outp) = |true|"

declare post_LOAD_def [cmlop_defs]

definition "body_LOAD(inp)       = {: reg := @inp.#1 :}"

declare body_LOAD_def [cmlop_defs]

definition "LOAD = CMLOpO \<parallel>@Byte*()\<parallel> \<parallel>()\<parallel> pre_LOAD post_LOAD body_LOAD"

declare LOAD_def [cmlop_defs]

lemma LOAD_sat_inv:
  "`\<lparr>&x hasType @Byte\<rparr>` \<Longrightarrow> RegisterProc_inv \<sqsubseteq> `call LOAD[&x]`"
  apply (unfold_cml)
  apply (rule DesignD_refine)
  apply (cml_tac)
  apply (rule AndP_refines_2)
  apply (rule AssignR_refine_alt)
  apply (simp_all add:usubst closure typing defined unrest)
done

text {* The \texttt{READ} operation returns the value of reg *}

definition "pre_READ(inp) = |true|"

declare pre_READ_def [cmlop_defs]

definition "post_READ inp outp = |true|"

declare post_READ_def [cmlop_defs]

definition "body_READ inp = {: return $reg :}"

declare body_READ_def [cmlop_defs]

definition "READ = CMLOpO \<parallel>()\<parallel> \<parallel>@Byte\<parallel> pre_READ post_READ body_READ"

declare READ_def [cmlop_defs]

lemma READ_sat_inv: 
  "RegisterProc_inv \<sqsubseteq> `call READ[]`"
  apply (unfold_cml)
  apply (rule DesignD_refine)
  apply (cml_tac)
  apply (rule SkipR_transport_refine)
  apply (rule VTautHideT_unrest)
oops

text {* \texttt{ADD} adds the given value to the register, under the
assumption that an overflow will not occur. *}

definition "pre_ADD(inp) = |not oflow($reg, @inp.#1)|"

declare pre_ADD_def [cmlop_defs]

definition "post_ADD inp outp = |true|"

declare post_ADD_def [cmlop_defs]

definition "body_ADD inp = {: reg := $reg + @inp.#1 :}"

declare body_ADD_def [cmlop_defs]

definition "ADD = CMLOpO \<parallel>@Byte*()\<parallel> \<parallel>()\<parallel> pre_ADD post_ADD body_ADD"

declare ADD_def [cmlop_defs]

lemma ADD_sat_inv: 
  "RegisterProc_inv \<sqsubseteq> `call ADD[&x]`"
  apply (unfold_cml)
  apply (rule DesignD_refine)
oops

text {* \texttt{SUBTR} subtracts the given value from the register,
under the assumption that an underflow will not occur. *}

definition "pre_SUBTR(inp) = |not uflow($reg, @inp.#1)|"

declare pre_SUBTR_def [cmlop_defs]

definition "post_SUBTR inp outp = |true|"

declare post_SUBTR_def [cmlop_defs]

definition "body_SUBTR inp = {: reg := $reg - @inp.#1 :}"

declare body_SUBTR_def [cmlop_defs]

definition "SUBTR = CMLOpO \<parallel>@Byte*()\<parallel> \<parallel>()\<parallel> pre_SUBTR post_SUBTR body_SUBTR"

declare SUBTR_def [cmlop_defs]

lemma SUBTR_sat_inv: 
  "RegisterProc_inv \<sqsubseteq> `call SUBTR[&x]`"
  apply (unfold_cml)
  apply (rule DesignD_refine)
oops

text {* Then we create the actual \texttt{REG} process. It can be
thought of as a calculator which waits for particular buttons to be
pressed, and suitably responds. If a \texttt{load} message is
received, the value input is loaded into the the register. If a
\texttt{read} is requested then the current value of the register is
sent. If an \texttt{add} or \texttt{subtract} is request, a guarded
action is performed. If the calculation would cause an overflow or
underflow, the message \texttt{overflow} or \texttt{underflow} is
communicated and the current state is reset. Otherwise the calculation
is carried out and the state updated. *}

definition "REG =
  `\<mu> REG. ((load?(i) -> call LOAD[&i]) ; REG)
          [] (read!($reg) -> REG)
          [] (add?(i) -> 
             (  ([\<lparr>oflow($reg, ^i^)\<rparr>] & (overflow -> (call INIT[] ; REG))) 
             [] ([\<lparr>not oflow($reg, ^i^)\<rparr>] & (call ADD[&i] ; REG))))
          [] (sub?(i) -> 
             (  ([\<lparr>uflow($reg, ^i^)\<rparr>] & (underflow -> (call INIT[] ; REG))) 
             [] ([\<lparr>not uflow($reg, ^i^)\<rparr>] & (call SUBTR[&i] ; REG))))`"

declare REG_def [cmlact_defs]

text {* Finally we have the main action of the process, which waits
for an \texttt{init} signal, and then initialises the register and
begins the recursive behaviour described by \texttt{REG}. *}

definition
  "MainAction = `init -> (call INIT[] ; REG)`"

declare MainAction_def [cmlact_defs]

(*<*)
end

end
(*>*)