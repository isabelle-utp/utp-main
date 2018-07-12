section \<open> Chemical Model \<close>

theory Chemical
imports "RoboChart-Untimed.StateMachine"
begin

subsection \<open> Type Declarations \<close>

typedecl Chem
type_synonym Intensity = real

subsection \<open> Enumerated Types \<close>

datatype Angle = Left | Right | Back | Front
datatype Status = noGas | gasD

subsection \<open> Data Types \<close>

record GasSensor =
  c :: Chem
  i :: Intensity

subsection \<open> Functions \<close>

consts goreq     :: "Intensity \<times> Intensity \<Rightarrow> bool"
consts analysis  :: "GasSensor list \<Rightarrow> Status"

consts intensity :: "GasSensor list \<Rightarrow> Intensity"

consts location  :: "GasSensor list \<Rightarrow> real"

end