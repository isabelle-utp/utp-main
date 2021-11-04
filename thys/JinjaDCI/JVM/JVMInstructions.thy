(*  Title:      JinjaDCI/JVM/JVMInstructions.thy

    Author:     Gerwin Klein, Susannah Mansky
    Copyright   2000 Technische Universitaet Muenchen, 2019-20 UIUC

    Based on the Jinja theory JVM/JVMInstructions.thy by Gerwin Klein
*)

section \<open> Instructions of the JVM \<close>


theory JVMInstructions imports JVMState begin


datatype 
  instr = Load nat                  \<comment> \<open>load from local variable\<close>
        | Store nat                 \<comment> \<open>store into local variable\<close>
        | Push val                  \<comment> \<open>push a value (constant)\<close>
        | New cname                 \<comment> \<open>create object\<close>
        | Getfield vname cname      \<comment> \<open>Fetch field from object\<close>
        | Getstatic cname vname cname     \<comment> \<open>Fetch static field from class\<close>
        | Putfield vname cname      \<comment> \<open>Set field in object    \<close>
        | Putstatic cname vname cname     \<comment> \<open>Set static field in class\<close>
        | Checkcast cname           \<comment> \<open>Check whether object is of given type\<close>
        | Invoke mname nat          \<comment> \<open>inv. instance meth of an object\<close>
        | Invokestatic cname mname nat    \<comment> \<open>inv. static method of a class\<close>
        | Return                    \<comment> \<open>return from method\<close>
        | Pop                       \<comment> \<open>pop top element from opstack\<close>
        | IAdd                      \<comment> \<open>integer addition\<close>
        | Goto int                  \<comment> \<open>goto relative address\<close>
        | CmpEq                     \<comment> \<open>equality comparison\<close>
        | IfFalse int               \<comment> \<open>branch if top of stack false\<close>
        | Throw                     \<comment> \<open>throw top of stack as exception\<close>

type_synonym
  bytecode = "instr list"

type_synonym
  ex_entry = "pc \<times> pc \<times> cname \<times> pc \<times> nat" 
  \<comment> \<open>start-pc, end-pc, exception type, handler-pc, remaining stack depth\<close>

type_synonym
  ex_table = "ex_entry list"

type_synonym
  jvm_method = "nat \<times> nat \<times> bytecode \<times> ex_table"
   \<comment> \<open>max stacksize\<close>
   \<comment> \<open>number of local variables. Add 1 + no. of parameters to get no. of registers\<close>
   \<comment> \<open>instruction sequence\<close>
   \<comment> \<open>exception handler table\<close>

type_synonym
  jvm_prog = "jvm_method prog"

(*<*)
translations
  (type) "bytecode" <= (type) "instr list"
  (type) "ex_entry" <= (type) "nat \<times> nat \<times> char list \<times> nat \<times> nat"
  (type) "ex_table" <= (type) "ex_entry list"
  (type) "jvm_method"   <= (type) "nat \<times> nat \<times> bytecode \<times> ex_table"
  (type) "jvm_prog" <= (type) "jvm_method prog"
(*>*)

end
