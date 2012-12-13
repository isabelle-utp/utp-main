theory utp_vdm_sorts
imports utp_vdm_inject
begin

instantiation vval :: VALUE_SORT
begin

definition Defined_vval :: "vval \<Rightarrow> bool" where "Defined_vval x = (x \<noteq> \<bottom>)"

instance ..

end


lemma Defined_bot [simp]: "\<D> (\<bottom> :: vval) \<longleftrightarrow> False"
  by (simp add:Defined_vval_def)

lemma Defined_bval [simp]: "\<D> (InjVB x)"
  by (simp add:Defined_vval_def InjVB_def InjB_def)

instantiation vval :: BOT_SORT
begin

definition bot_vval :: vval where "bot_vval = \<bottom>"
definition less_eq_vval :: "vval \<Rightarrow> vval \<Rightarrow> bool" where
"less_eq_vval \<equiv> op \<sqsubseteq>"

definition less_vval :: "vval \<Rightarrow> vval \<Rightarrow> bool" where
"less_vval x y \<equiv> (x \<sqsubseteq> y) \<and> \<not> (y \<sqsubseteq> x)"

instance
  apply (intro_classes)
  apply (simp_all add:bot_vval_def less_eq_vval_def less_vval_def)
  apply (metis rev_below_trans)
  apply (metis below_antisym)
done
end

subsection {* Function sort instantiation *}


instantiation vval :: FUNCTION_SORT
begin

definition MkFunc_vval where "MkFunc_vval f = FuncV\<cdot>(\<Lambda>! x. f x)"
definition DestFunc_vval where "DestFunc_vval f \<equiv> \<lambda> x. (sfun_rep\<cdot>(ProjFuncV\<cdot>f))\<cdot>x"
definition IsFunc_vval :: "(vval \<Rightarrow> vval) \<Rightarrow> bool" where
"IsFunc_vval f \<equiv> cont f \<and> f \<bottom> = \<bottom> \<and> (\<exists>x. x \<noteq> \<bottom> \<and> f x \<noteq> \<bottom>)"

instance
  apply (intro_classes)
  apply (simp add:MkFunc_vval_def DestFunc_vval_def IsFunc_vval_def)
  apply (auto simp add:Defined_vval_def IsFunc_vval_def MkFunc_vval_def sfun_eq_iff)
  apply (metis Abs_cfun_inverse2 Rep_cfun_strict app_strict)
done
end

subsection {* Int sort instantiation *}

instantiation vval :: INT_SORT
begin

definition MkInt_vval where "MkInt_vval (x::int) = InjVB x"
definition DestInt_vval where "DestInt_vval x = (ProjVB x :: int)"

instance 
  by (intro_classes, simp_all add:MkInt_vval_def DestInt_vval_def)
end

subsection {* Bool sort instantiation *}

instantiation vval :: BOOL_SORT
begin

definition MkBool_vval where "MkBool_vval (x::bool) = InjVB x"
definition DestBool_vval where "DestBool_vval x = (ProjVB x :: bool)"

instance 
  by (intro_classes, simp_all add:MkBool_vval_def DestBool_vval_def)
end

subsection {* Char sort instantiation *}

instantiation vval :: CHAR_SORT
begin

definition MkChar_vval where "MkChar_vval (x::char) = InjVB x"
definition DestChar_vval where "DestChar_vval x = (ProjVB x :: char)"

instance 
  by (intro_classes, simp_all add:MkChar_vval_def DestChar_vval_def)
end

subsection {* String sort instantiation *}

instantiation vval :: STRING_SORT
begin

definition MkStr_vval where "MkStr_vval (x::string) = InjVB x"
definition DestStr_vval where "DestStr_vval x = (ProjVB x :: string)"

instance 
  by (intro_classes, simp_all add:MkStr_vval_def DestStr_vval_def)
end

end