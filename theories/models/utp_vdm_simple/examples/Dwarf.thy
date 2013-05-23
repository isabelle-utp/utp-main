theory Dwarf
imports 
  "../utp_vdm_types"
  "../utp_vdm_functions"
begin

abbreviation "L1 \<equiv> ''L1''"
abbreviation "L2 \<equiv> ''L2''"
abbreviation "L3 \<equiv> ''L3''"

abbreviation "LampId   \<equiv> &<L1> | <L2> | <L3>&"
abbreviation "Signal   \<equiv> &@set of @LampId&"
abbreviation "dark     \<equiv> *{}*"
abbreviation "stop     \<equiv> *{<L1>, <L2>}*"
abbreviation "warning  \<equiv> *{<L1>, <L3>}*"
abbreviation "drive    \<equiv> *{<L2>, <L3>}*"

syntax
  "_vexpr_vexpr"  :: "'a vdme \<Rightarrow> vexpr" ("@_")

translations
  "_vexpr_vexpr x" => "x"

abbreviation "ProperState \<equiv> &@Signal inv ps == (!ps! in set {@dark, @stop, @warning, @drive})&"


end