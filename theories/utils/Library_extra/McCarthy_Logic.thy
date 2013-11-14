theory McCarthy_Logic
imports Main
begin

definition "mconj p q = (case (p, q) of 
                           (Some True, x)  \<Rightarrow> x
                         | (Some False, _) \<Rightarrow> Some False
                         | (_, _) \<Rightarrow> None)"

definition "mdisj p q = (case (p, q) of 
                           (Some True, _) \<Rightarrow> Some True
                         | (Some False, x) \<Rightarrow> x
                         | (_, _) \<Rightarrow> None)"

definition "mnot p = (case p of None \<Rightarrow> None | Some x \<Rightarrow> Some (\<not> x))"

definition "mimplies p q = (mdisj (mnot p) q)"

lemma mconj_simps [simp]:
  "mconj (Some True)  x = x"
  "mconj (Some False) x = Some False"
  "mconj None x         = None"
  by (auto simp add: mconj_def)

lemma mdisj_simps [simp]:
  "mdisj (Some True) x  = Some True"
  "mdisj (Some False) x = x"
  "mdisj None x         = None"
  by (auto simp add: mdisj_def)

lemma mnot_simps [simp]:
  "mnot None = None"
  "mnot (Some p) = Some (\<not> p)"
  by (simp_all add:mnot_def)

lemma mimplies_simps [simp]:
  "mimplies (Some False) x = Some True"
  "mimplies (Some True) x = x"
  "mimplies None x = None"
  by (simp_all add:mimplies_def)

end
