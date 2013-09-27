(******************************************************************************)
(* Project: CML model for Isabelle/UTP                                        *)
(* File: BitRegister.thy                                                      *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* CML Dwarf Signal Example *}

(*<*)
theory BitRegister
imports 
  "../utp_cml"
begin
(*>*)

text {* The ``bit-register'' is a simple process which performs
arithmetic calculations on a byte state variable. It detects overflow
and underflow if and when it occurs and informs the user. A byte is
represented as a integer with the invariant that the value must be
between 0 and 255. *}

abbreviation 
  "Byte \<equiv> \<parallel>@int inv n == (^n^ >= 0) and (^n^ <= 255)\<parallel>"

text {* The bit-register has two functions: \texttt{oflow} for
detecting overflow caused by a summation, and \texttt{uflow} for
detecting underflow caused by a substraction. Both take a pair of
integers and return a boolean if over/underflow occurs. Functions 
in CML are desugared to lambda terms . *}

definition 
  "oflow = |lambda d @ (^d^.#1 + ^d^.#2) > 255|"

definition 
  "uflow = |lambda d @ (^d^.#1 - ^d^.#2) < 0|"

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

text {* We use an Isabelle locale to create a new namespace for the
\texttt{RegisterProc}. *}

locale RegisterProc
begin

text {* The single state variable, \texttt{reg}, holds the current
value of the calculation. *}

abbreviation "reg \<equiv> MkVarD ''reg'' \<parallel>@Byte\<parallel>"

text {* Now we declare the operations of the
bit-register. \texttt{INIT} initialises the state variables to 0. *}

definition "INIT = 
  `true \<turnstile> (reg :=\<^sub>D 0)`"

text {* \texttt{LOAD} sets the register to a particular value. *}

definition "LOAD(i) =
  `true \<turnstile> (reg := ^i^)`"

(* Can't implement the READ operation -- what is the semantics of return? *)

text {* \texttt{ADD} adds the given value to the register, under the
assumption that an overflow will not occur. *}

definition "ADD(i) =
  `\<lparr> not oflow($reg, ^i^) \<rparr> \<turnstile> reg := $reg + ^i^`"

text {* \texttt{SUBTR} subtracts the given value from the register,
under the assumption that an underflow will not occur. *}

definition "SUBTR(i) =
  `\<lparr> not uflow($reg, ^i^) \<rparr> \<turnstile> reg := ($reg - ^i^)`"

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
  `\<mu> REG. ((load?(i) -> LOAD(&i)) ; REG)
          [] (read!($reg) -> REG)
          [] (add?(i) -> 
             (  ([\<lparr>oflow($reg, ^i^)\<rparr>] & (overflow -> (INIT() ; REG))) 
             [] ([\<lparr>not oflow($reg, ^i^)\<rparr>] & (ADD(^i^) ; REG))))
          [] (sub?(i) -> 
             (  ([\<lparr>uflow($reg, ^i^)\<rparr>] & (underflow -> (INIT() ; REG))) 
             [] ([\<lparr>not uflow($reg, ^i^)\<rparr>] & (SUBTR(^i^) ; REG))))`"

text {* Finally we have the main action of the process, which waits
for an \texttt{init} signal, and then initialises the register and
begins the recursive behaviour described by \texttt{REG}. *}

definition
  "MainAction = `init -> (INIT() ; REG)`"

lemma MkVarD_PUNDASHED [closure]:
  "MkVarD n a \<in> PUNDASHED"
  by (simp add:MkVarD_def PUNDASHED_def PVAR_VAR_MkPVAR)

lemma NumD_defined [defined]:
  "\<D> (NumD n)"
  by (simp add:NumD_def defined)

lemma UNREST_PEXPR_NumD [unrest]:
  "vs \<sharp> NumD n"
  by (metis NumD_def UNREST_LitPE)

(*
lemma "\<lbrakk> x \<in> UNDASHED; v \<rhd>\<^sub>e x; x \<notin> vs; x\<acute> \<notin> vs; vs \<sharp> v; vs \<sharp> v\<acute> \<rbrakk> \<Longrightarrow> vs \<sharp> (x :=\<^sub>R v)"
  apply (simp add:AssignR_alt_def)
  apply (rule unrest)
  apply (rule unrest)
  apply (rule unrest)
  apply (simp_all)
  apply (rule unrest)
  apply (simp ad
*)



lemma INIT_idem:
  "INIT ; INIT = INIT"
  apply (simp add:INIT_def)
  apply (subst DesignD_composition_wp)
  apply (simp_all add:closure unrest wp)
  apply (simp add:closure defined typing unrest)
  defer
  apply (simp add: AssignR_idem_simple closure unrest typing defined)
  apply (simp add:closure)
  apply (simp add:unrest typing)
  apply (simp add:unrest typing)
  apply (simp add:unrest typing defined)
  apply (simp)
  nitpick
  apply (rule unrest)



  thm DesignD_composi
  apply (rule DesignD_composition)
  apply (utp_rel_auto_tac)

(*<*)
end

end
(*>*)