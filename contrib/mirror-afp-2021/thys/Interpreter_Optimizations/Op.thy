theory Op
  imports Main
begin

section \<open>n-ary operations\<close>

locale nary_operations =
  fixes
    \<OO>\<pp> :: "'op \<Rightarrow> 'a list \<Rightarrow> 'a" and
    \<AA>\<rr>\<ii>\<tt>\<yy> :: "'op \<Rightarrow> nat"
  assumes
    \<OO>\<pp>_\<AA>\<rr>\<ii>\<tt>\<yy>_domain: "length xs = \<AA>\<rr>\<ii>\<tt>\<yy> op \<Longrightarrow> \<exists>y. \<OO>\<pp> op xs = y"

end