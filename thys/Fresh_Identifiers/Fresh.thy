section \<open>The type class \<open>fresh\<close>\<close>

theory Fresh
  imports Main
begin

text \<open>A type in this class comes with a mechanism to generate fresh
items. The fresh operator takes a list of items to be avoided, \<open>xs\<close>, and
a preferred element to be generated, \<open>x\<close>.

It is required that
implementations of fresh for specific types produce \<open>x\<close> if possible
(i.e., if not in \<open>xs\<close>).

While not required, it is also expected that, if \<open>x\<close> is not possible,
then implementation produces an element that is as close to \<open>x\<close> as
possible, given a notion of distance.
\<close>

class fresh =
  fixes fresh :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes fresh_notIn: "\<And> xs x. finite xs \<Longrightarrow> fresh xs x \<notin> xs"
  and fresh_eq: "\<And> xs x. x \<notin> xs \<Longrightarrow> fresh xs x = x"


text \<open>The type class \<^class>\<open>fresh\<close> is essentially the same as
the type class \<open>infinite\<close> but with an emphasis on fresh item generation.\<close>

class infinite =
  assumes infinite_UNIV: "\<not> finite (UNIV :: 'a set)"

text \<open>We can subclass \<^class>\<open>fresh\<close> to \<^class>\<open>infinite\<close> since the latter
has no associated operators (in particular, no additional operators w.r.t.
the former).\<close>

subclass (in fresh) infinite
  apply (standard)
  using finite_list local.fresh_notIn by auto

end
