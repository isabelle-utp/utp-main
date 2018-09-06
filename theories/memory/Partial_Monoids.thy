section \<open> Partial Monoid and Semigroups \<close>

theory Partial_Monoids
  imports Main
begin

text \<open> The content of this theory is adapted from two AFP entries: 
  \begin{itemize}
      \item Separation Algebra, by Klein et al. \cite{Klein2012}
      \item Partial Semigroups and Convolution Algebras, by Dongol et al. \cite{Dongol2015}
  \end{itemize}
\<close>

class compat =
  fixes compat :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "##" 60)

class partial_semigroup = compat + plus +
  assumes compat_comm: "x ## y \<Longrightarrow> y ## x"
  and compat_assoc: "\<lbrakk> x ## y; (x + y) ## z \<rbrakk> \<Longrightarrow> x ## (y + z)"
  and compat_decompr: "\<lbrakk> x ## y; (x + y) ## z \<rbrakk> \<Longrightarrow> y ## z"
  and plus_passoc : "\<lbrakk> x ## y; (x + y) ## z \<rbrakk> \<Longrightarrow> (x + y) + z = x + (y + z)"
begin

lemma compat_property: "y ## z \<and> x ## (y + z) \<longleftrightarrow> x ## y \<and> (x + y) ## z"
  by (meson local.compat_assoc local.compat_comm local.compat_decompr)

lemma compat_decompl: "\<lbrakk> x ## y; (x + y) ## z \<rbrakk> \<Longrightarrow> x ## z"
  using compat_property local.compat_comm by blast

definition green_preorder :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<preceq>\<^sub>G" 50) where
  "x \<preceq>\<^sub>G y = (\<exists>z. x ## z \<and> x + z = y)"

definition green_strict :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<prec>\<^sub>G" 50) where
  "x \<prec>\<^sub>G y = (x \<preceq>\<^sub>G y \<and> \<not> y \<preceq>\<^sub>G x)"

lemma gp_trans: "\<lbrakk> x \<preceq>\<^sub>G y; y \<preceq>\<^sub>G z \<rbrakk> \<Longrightarrow> x \<preceq>\<^sub>G z"
  using green_preorder_def local.compat_assoc local.plus_passoc by fastforce

end

class pas = partial_semigroup +
  assumes plus_pcomm: "\<lbrakk> x ## y \<rbrakk> \<Longrightarrow> x + y = y + x"

class partial_semigroup_cancel = partial_semigroup + 
  assumes add_cancl: "\<lbrakk> z ## x; z ## y; z + x = z + y \<rbrakk> \<Longrightarrow> x = y" 
  and add_cancr: "\<lbrakk> x ## z; y ## z; x + z = y + z \<rbrakk> \<Longrightarrow> x = y" 

class pas_cancel = pas +
  assumes add_cancel: "\<lbrakk> z ## x; z ## y; z + x = z + y \<rbrakk> \<Longrightarrow> x = y"
begin
  subclass partial_semigroup_cancel
    by (unfold_locales, simp_all add: add_cancel)
       (metis add_cancel compat_comm plus_pcomm)
end

class partial_monoid = partial_semigroup + zero +
  assumes 
    compat_zero [simp]: "0 ## x" and
    zero_unitl [simp]: "0 + x = x" and
    zero_unitr [simp]: "x + 0 = x"
begin

  lemma compat_zeror [simp]: "x ## 0"
    by (simp add: compat_comm)

  definition green_subtract :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "-\<^sub>G" 65)
    where "a -\<^sub>G b = (if (b \<preceq>\<^sub>G a) then THE c. (b ## c \<and> a = b + c) else 0)"

  lemma gp_least [simp]: "0 \<preceq>\<^sub>G x"
    by (simp add: local.green_preorder_def)

end

class partial_monoid_pos = partial_monoid +
  assumes
    positive_left: "x + y = 0 \<Longrightarrow> x = 0"
begin
  lemma positive_right: "x + y = 0 \<Longrightarrow> y = 0"
    using local.positive_left local.zero_unitl by fastforce
end

class pam = pas + partial_monoid
begin

  lemma gp_refl [simp]: "x \<preceq>\<^sub>G x"
    using compat_comm compat_zero green_preorder_def zero_unitr by blast

end

class pam_pos = pas + partial_monoid_pos
    
class pam_cancel = pam + pas_cancel
begin

  lemma gp_iso: "\<lbrakk> x \<preceq>\<^sub>G y; y ## z \<rbrakk> \<Longrightarrow> x + z \<preceq>\<^sub>G y + z"
    by (auto simp add: green_preorder_def)
       (metis local.compat_assoc local.compat_comm local.plus_passoc local.plus_pcomm)

  lemma gr_minus_cancel: "x ## y \<Longrightarrow> ((x + y) -\<^sub>G x) = y"
    using local.add_cancl by (auto simp add: green_subtract_def green_preorder_def)

  lemma gr_minus_zero [simp]: "x -\<^sub>G 0 = x"
    using gr_minus_cancel local.compat_zero local.zero_unitl by fastforce

end

class pam_cancel_pos = pam_cancel + pam_pos
begin

  lemma gp_antisym: "\<lbrakk> x \<preceq>\<^sub>G y; y \<preceq>\<^sub>G x \<rbrakk> \<Longrightarrow> x = y"
    by (auto simp add: green_preorder_def)
       (metis local.compat_assoc local.compat_comm local.compat_zero local.gr_minus_cancel local.plus_passoc local.positive_left)

end

class sep_alg = pam + ord + minus +
  assumes minus_def: "y \<le> x \<Longrightarrow> x - y = x -\<^sub>G y"
  and less_eq_def: "x \<le> y \<longleftrightarrow> x \<preceq>\<^sub>G y"
  and less_def: "x < y \<longleftrightarrow> x \<prec>\<^sub>G y"
begin

subclass preorder
  by (unfold_locales, auto intro: gp_trans simp add: less_eq_def less_def green_strict_def)
end

class sep_alg_cancel_pos = sep_alg + pam_cancel_pos
begin

subclass order
  by (unfold_locales, auto intro: gp_trans gp_antisym simp add: less_eq_def less_def green_strict_def)

end

end