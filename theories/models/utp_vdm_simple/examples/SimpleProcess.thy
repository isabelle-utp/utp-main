theory SimpleProcess
imports 
  "../utp_vdm"
begin

definition "a = MkChanD ''a'' \<parallel>@int\<parallel>"
definition "b = MkChanD ''b'' \<parallel>@int\<parallel>"

locale Simple
begin

abbreviation "v \<equiv> MkVarD ''v'' \<parallel>@int\<parallel>"

definition ExistsWP :: "('a::VALUE VAR \<Rightarrow> 'a WF_PREDICATE) \<Rightarrow> 'a WF_PREDICATE" where
"ExistsWP P = (let v = SOME x. UNREST {x} (P x) in ExistsP {v} (P v))"

definition "ACT1 = `\<exists> v. a.($v) \<rightarrow> b.($v * 2) \<rightarrow> SKIP`"
definition "ACT2 = `a.(5) \<rightarrow> SKIP`"

end
