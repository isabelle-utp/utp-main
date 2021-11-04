subsection \<open>Precedence\<close>

text 
  \<open>A precedence consists of two compatible relations (strict and non-strict) on symbols such that 
the strict relation is strongly normalizing. In the formalization we model this via a
function "prc" (precedence-compare) which returns two Booleans, indicating whether the one symbol is
strictly or weakly bigger than the other symbol. Moreover, there also is a function "prl" 
(precedence-least) which gives quick access to whether a symbol is least in precedence, i.e., 
without comparing it to all other symbols explicitly.\<close>

theory Precedence
  imports 
    "Abstract-Rewriting.Abstract_Rewriting"
begin

locale precedence =
  fixes prc :: "'f \<Rightarrow> 'f \<Rightarrow> bool \<times> bool"
    and prl :: "'f \<Rightarrow> bool"
  assumes prc_refl: "prc f f = (False, True)"
    and prc_SN: "SN {(f, g). fst (prc f g)}"
    and prl: "prl g \<Longrightarrow> snd (prc f g) = True"
    and prl3: "prl f \<Longrightarrow> snd (prc f g) \<Longrightarrow> prl g"
    and prc_compat: "prc f g = (s1, ns1) \<Longrightarrow> prc g h = (s2, ns2) \<Longrightarrow> prc f h = (s, ns) \<Longrightarrow> 
   (ns1 \<and> ns2 \<longrightarrow> ns) \<and> (ns1 \<and> s2 \<longrightarrow> s) \<and> (s1 \<and> ns2 \<longrightarrow> s)"
    and prc_stri_imp_nstri: "fst (prc f g) \<Longrightarrow> snd (prc f g)"
begin

lemma prl2:
  assumes g: "prl g" shows "fst (prc g f) = False"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain b where gf: "prc g f = (True, b)" by (cases "prc g f", auto)
  obtain b1 b2 where gg: "prc g g = (b1, b2)" by force
  obtain b' where fg: "prc f g = (b', True)" using prl[OF g, of f] by (cases "prc f g", auto)
  from prc_compat[OF gf fg gg] gg have gg: "fst (prc g g)" by auto
  with SN_on_irrefl[OF prc_SN] show False by blast
qed

abbreviation "pr \<equiv> (prc, prl)"

end

end
