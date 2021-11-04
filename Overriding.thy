section \<open> Polymorphic Overriding Operator \<close>

theory Overriding
  imports Main
begin

text \<open> We here use type classes to create the overriding operator and instantiate it for relations,
  partial function, and finite functions. \<close>

class oplus = 
  fixes oplus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 65)

class compatible = 
  fixes compatible :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "##" 60)
  assumes compatible_sym: "x ## y \<Longrightarrow> y ## x"

class override = oplus + zero + compatible +
  assumes compatible_zero [simp]: "x ## 0"
  and override_idem [simp]: "P \<oplus> P = P"
  and override_assoc: "P \<oplus> (Q \<oplus> R) = (P \<oplus> Q) \<oplus> R"
  and override_lzero [simp]: "0 \<oplus> P = P"
  and override_comm: "P ## Q \<Longrightarrow> P \<oplus> Q = Q \<oplus> P" 
  and override_compat: "\<lbrakk> P ## Q; (P \<oplus> Q) ## R \<rbrakk> \<Longrightarrow> P ## R"
  and override_compatI: "\<lbrakk> P ## Q; P ## R; Q ## R \<rbrakk> \<Longrightarrow> (P \<oplus> Q) ## R"
begin

lemma override_rzero [simp]: "P \<oplus> 0 = P"
  by (metis compatible_zero override_comm override_lzero)

lemma override_compat': "\<lbrakk> P ## Q; (P \<oplus> Q) ## R \<rbrakk> \<Longrightarrow> Q ## R"
  by (metis compatible_sym override_comm override_compat)

lemma override_compat_iff: "P ## Q \<Longrightarrow> (P \<oplus> Q) ## R \<longleftrightarrow> (P ## R) \<and> (Q ## R)"
  by (meson override_compat override_compatI override_compat')

end

end