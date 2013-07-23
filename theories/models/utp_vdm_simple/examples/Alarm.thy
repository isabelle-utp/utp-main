theory Alarm
imports "../utp_vdm"
begin

abbreviation "Period   \<equiv> \<parallel>@nat\<parallel>\<^sub>t"
abbreviation "ExpertId \<equiv> \<parallel>@nat\<parallel>\<^sub>t"
abbreviation "Qualification \<equiv> \<parallel><''Elec''> | <''Mech''> | <''Bio''> | <''Chem''>\<parallel>\<^sub>t"

record Alarm_raw =
  alarmtext :: "char list"
  quali     :: "quote fset fset"

definition "Alarm = (UNIV :: Alarm_raw set)"

record Expert_raw =
  expertid :: nat
  quali    :: "quote fset"

instantiation Expert_raw_ext :: (vbasic) vbasic
begin

definition "Inject_Expert_raw_ext x = Inject_rec ''Expert_raw'' x Rep_Expert_raw_ext"
definition "Type_Expert_raw_ext x = Type_rec ''Expert_raw'' x Rep_Expert_raw_ext"

instance
  apply (intro_classes)
  apply (auto simp add:Inject_Expert_raw_ext_def Type_Expert_raw_ext_def Type_rec_def Inject_rec_def Rep_Expert_raw_ext_inject image_def)
  apply (rule_tac x="Abs_Expert_raw_ext (the (Project xa))" in exI)
  apply (simp add: Abs_Expert_raw_ext_inverse[simplified])
done
end

instantiation Expert_raw_ext :: (DEFINED) DEFINED
begin

definition Defined_Expert_raw_ext :: "'a Expert_raw_scheme \<Rightarrow> bool" where
"Defined_Expert_raw_ext x = True"

instance ..

end

definition "Expert = {ex. quali ex \<noteq> \<lbrace>\<rbrace>}"

definition "Schedule = \<parallel>(@map @Period to @set of @Expert) 
                         inv sch == forall x & true\<parallel>\<^sub>t"


abbreviation "Alarm \<equiv> \<parallel>x inv\<parallel>\<^sub>t"
