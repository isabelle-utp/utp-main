subsection\<open>Value Lexorder\<close>

text\<open>This theory defines a lexicographical ordering on values such that we can build orderings for
arithmetic expressions and guards. Here, numbers are defined as less than strings, else the natural
ordering on the respective datatypes is used.\<close>

theory Value_Lexorder
imports Value
begin

instantiation "value" :: linorder begin
text_raw\<open>\snip{valueorder}{1}{2}{%\<close>
fun less_value :: "value \<Rightarrow> value \<Rightarrow> bool" where
  "(Num n) < (Str s) = True" |
  "(Str s) < (Num n) = False" |
  "(Str s1) < (Str s2) = (s1 < s2)" |
  "(Num n1) < (Num n2) = (n1 < n2)"
text_raw\<open>}%endsnip\<close>

definition less_eq_value :: "value \<Rightarrow> value \<Rightarrow> bool" where
  "less_eq_value v1 v2 = (v1 < v2 \<or> v1 = v2)"
declare less_eq_value_def [simp]

instance
  apply standard
      apply (simp, metis less_imp_not_less less_value.elims(2) less_value.simps(3) less_value.simps(4))
     apply simp
  subgoal for x y z
    apply (induct x y rule: less_value.induct)
       apply (metis less_eq_value_def less_value.elims(3) less_value.simps(2) value.simps(4))
      apply simp
     apply (metis dual_order.strict_trans less_eq_value_def less_value.elims(2) less_value.simps(3) value.distinct(1))
    by (cases z, auto)
   apply (metis less_eq_value_def less_imp_not_less less_value.elims(2) less_value.simps(3) less_value.simps(4))
  subgoal for x y
    by (induct x y rule: less_value.induct, auto)
  done

end

end
