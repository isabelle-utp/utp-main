section \<open>The Static Representation of a Language\<close>

theory Language
  imports Semantics
begin

locale language =
  semantics step final
  for
    step :: "'state \<Rightarrow> 'state \<Rightarrow> bool" and
    final :: "'state \<Rightarrow> bool" +
  fixes
    load :: "'prog \<Rightarrow> 'state \<Rightarrow> bool"

context language begin

text \<open>
The language locale represents the concrete program representation (type variable @{typ 'prog}), which can be transformed into a program state (type variable @{typ 'state}) by the @{term load } function.
The set of initial states of the transition system is implicitly defined by the codomain of @{term load}.
\<close>


subsection \<open>Behaviour of a dynamic execution\<close>

definition behaves :: "'prog \<Rightarrow> 'state behaviour \<Rightarrow> bool" (infix "\<Down>" 50) where
  "behaves = load OO sem_behaves"

text \<open>If both the @{term load} and @{term step} relations are deterministic, then so is the behaviour of a program.\<close>

lemma behaves_deterministic:
  assumes
    load_deterministic: "\<And>p s s'. load p s \<Longrightarrow> load p s' \<Longrightarrow> s = s'" and
    step_deterministic: "\<And>x y z. step x y \<Longrightarrow> step x z \<Longrightarrow> y = z" and
    behaves: "p \<Down> b" "p \<Down> b'"
  shows "b = b'"
proof -
  obtain s where "load p s" and "s \<down> b" and "s \<down> b'"
    using behaves load_deterministic
    by (auto simp: behaves_def)

  thus ?thesis
    using step_deterministic sem_behaves_deterministic[OF _ \<open>s \<down> b\<close> \<open>s \<down> b'\<close>]
    by simp
qed

end

end