section\<open>Variables\<close>
text\<open>Variables can either be inputs or registers. Here we define the \texttt{vname} datatype which
allows us to write expressions in terms of variables and case match during evaluation. We also make
the \texttt{vname} datatype a member of linorder such that we can establish a linear order on
arithmetic expressions, guards, and subsequently transitions.\<close>

theory VName
imports Main
begin

text_raw\<open>\snip{vnametype}{1}{2}{%\<close>
datatype vname = I nat | R nat
text_raw\<open>}%endsnip\<close>

instantiation vname :: linorder begin
text_raw\<open>\snip{vnameorder}{1}{2}{%\<close>
fun less_vname :: "vname \<Rightarrow> vname \<Rightarrow> bool" where
  "(I n1) < (R n2) = True" |
  "(R n1) < (I n2) = False" |
  "(I n1) < (I n2) = (n1 < n2)" |
  "(R n1) < (R n2) = (n1 < n2)"
text_raw\<open>}%endsnip\<close>

definition less_eq_vname :: "vname \<Rightarrow> vname \<Rightarrow> bool" where
  "less_eq_vname v1 v2 = (v1 < v2 \<or> v1 = v2)"
declare less_eq_vname_def [simp]

instance
  apply standard
      apply (metis (full_types) dual_order.asym less_eq_vname_def less_vname.simps(2) less_vname.simps(3) less_vname.simps(4) vname.exhaust)
     apply simp
  subgoal for x y z
    apply (induct x y rule: less_vname.induct)
       apply (metis less_eq_vname_def less_vname.elims(2) less_vname.elims(3) vname.simps(4))
      apply simp
     apply (metis less_eq_vname_def less_trans less_vname.elims(3) less_vname.simps(3) vname.simps(4))
    by (metis le_less_trans less_eq_vname_def less_imp_le_nat less_vname.elims(2) less_vname.simps(4) vname.simps(4))
   apply (metis dual_order.asym less_eq_vname_def less_vname.elims(2) less_vname.simps(3) less_vname.simps(4))
   subgoal for x y
     by (induct x y rule: less_vname.induct, auto)
   done
end

end
