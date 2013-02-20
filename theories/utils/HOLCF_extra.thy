theory HOLCF_extra
imports 
  HOLCF 
  "~~/src/HOL/HOLCF/Library/HOL_Cpo"
  "HOLCF_extra/Tr_Logic" 
  "HOLCF_extra/Cfun_Partial" 
  "HOLCF_extra/Cset"
begin

instantiation lift :: (countable) countable
begin

instance
  apply (intro_classes)
  apply (rule_tac x="\<lambda> x. case x of (Def y) \<Rightarrow> 1 + to_nat y | \<bottom> \<Rightarrow> 0" in exI)
  apply (rule injI)
  apply (case_tac x, case_tac[!] y)
  apply (auto)
done
end

primrec down :: "'a u \<Rightarrow> 'a" where
"down (Iup x) = x"

primrec Undef :: "'a lift \<Rightarrow> 'a" where
"Undef (Def x) = x"

lemma down_up [simp]: "down (up\<cdot>x) = x"
  by (simp add:up_def beta_cfun cont_Iup)

end
