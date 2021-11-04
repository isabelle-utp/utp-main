(*<*)
theory HOLCF_ROOT
imports
  "HOLCF-Prelude.HOLCF_Prelude"
begin

(*>*)
section\<open>Extra HOLCF\<close>

lemma lfp_fusion:
  assumes "g\<cdot>\<bottom> = \<bottom>"
  assumes "g oo f = h oo g"
  shows "g\<cdot>(fix\<cdot>f) = fix\<cdot>h"
proof(induct rule: parallel_fix_ind)
  case 2 show "g\<cdot>\<bottom> = \<bottom>" by fact
  case (3 x y)
  from \<open>g\<cdot>x = y\<close> \<open>g oo f = h oo g\<close> show "g\<cdot>(f\<cdot>x) = h\<cdot>y"
    by (simp add: cfun_eq_iff)
qed simp

lemma predE:
  obtains (strict) "p\<cdot>\<bottom> = \<bottom>" | (FF) "p = (\<Lambda> x. FF)" | (TT) "p = (\<Lambda> x. TT)"
using flat_codom[where f=p and x=\<bottom>] by (cases "p\<cdot>\<bottom>"; force simp: cfun_eq_iff)

lemma retraction_cfcomp_strict:
  assumes "f oo g = ID"
  shows "f\<cdot>\<bottom> = \<bottom>"
using assms retraction_strict by (clarsimp simp: cfun_eq_iff)

lemma match_Pair_csplit[simp]: "match_Pair\<cdot>x\<cdot>k = k\<cdot>(cfst\<cdot>x)\<cdot>(csnd\<cdot>x)"
by (cases x) simp

lemmas oo_assoc = assoc_oo \<comment>\<open>Normalize name\<close>

lemma If_cancel[simp]: "(If b then x else x) = seq\<cdot>b\<cdot>x"
by (cases b) simp_all

lemma seq_below[iff]: "seq\<cdot>x\<cdot>y \<sqsubseteq> y"
by (simp add: seq_conv_if)

lemma seq_strict_distr: "f\<cdot>\<bottom> = \<bottom> \<Longrightarrow> seq\<cdot>x\<cdot>(f\<cdot>y) = f\<cdot>(seq\<cdot>x\<cdot>y)"
by (cases "x = \<bottom>"; clarsimp)

lemma strictify_below[iff]: "strictify\<cdot>f \<sqsubseteq> f"
unfolding strictify_def by (clarsimp simp: cfun_below_iff)

lemma If_distr:
  "\<lbrakk>f \<bottom> = \<bottom>; cont f\<rbrakk> \<Longrightarrow> f (If b then t else e) = (If b then f t else f e)"
  "\<lbrakk>cont t'; cont e'\<rbrakk> \<Longrightarrow> (If b then t' else e') x = (If b then t' x else e' x)"
  "(If b then t''' else e''')\<cdot>x = (If b then t'''\<cdot>x else e'''\<cdot>x)"
  "\<lbrakk>g \<bottom> = \<bottom>; cont g\<rbrakk> \<Longrightarrow> g (If b then t'' else e'') y = (If b then g t'' y else g e'' y)"
by (case_tac [!] b) simp_all

lemma If2_split_asm: "P (If2 Q x y) \<longleftrightarrow> \<not>(Q = \<bottom> \<and> \<not>P \<bottom> \<or> Q = TT \<and> \<not>P x \<or> Q = FF \<and> \<not>P y)"
  by (cases Q) (simp_all add: If2_def)

lemmas If2_splits = split_If2 If2_split_asm

lemma If2_cont[simp, cont2cont]:
  assumes "cont i"
  assumes "cont t"
  assumes "cont e"
  shows "cont (\<lambda>x. If2 (i x) (t x) (e x))"
using assms unfolding If2_def by simp

lemma If_else_FF[simp]: "(If b then t else FF) = (b andalso t)"
by (cases b) simp_all

lemma If_then_TT[simp]: "(If b then TT else e) = (b orelse e)"
by (cases b) simp_all

lemma If_cong:
  assumes "b = b'"
  assumes"b = TT \<Longrightarrow> t = t'"
  assumes "b = FF \<Longrightarrow> e = e'"
  shows "(If b then t else e) = (If b' then t' else e')"
using assms by (cases b) simp_all

lemma If_tr: "(If b then t else e) = ((b andalso t) orelse (neg\<cdot>b andalso e))"
by (cases b) simp_all

lemma If_andalso:
  shows "If p andalso q then t else e = If p then If q then t else e else e"
by (cases p) simp_all

lemma If_else_absorb:
  assumes "c = \<bottom> \<Longrightarrow> e = \<bottom>"
  assumes "c = TT \<Longrightarrow> e = t"
  shows "If c then t else e = e"
using assms by (cases c; clarsimp)

lemma andalso_cong: "\<lbrakk>P = P'; P' = TT \<Longrightarrow> Q = Q'\<rbrakk> \<Longrightarrow> (P andalso Q) = (P' andalso Q')"
by (cases P) simp_all

lemma andalso_weaken_left:
  assumes "P = TT \<Longrightarrow> Q = TT"
  assumes "P = FF \<Longrightarrow> Q \<noteq> \<bottom>"
  assumes "P = \<bottom> \<Longrightarrow> Q \<noteq> FF"
  shows "P = (Q andalso P)"
using assms by (cases P; cases Q; simp)

lemma orelse_cong: "\<lbrakk>P = P'; P' = FF \<Longrightarrow> Q = Q'\<rbrakk> \<Longrightarrow> (P orelse Q) = (P' orelse Q')"
by (cases P) simp_all

lemma orelse_conv[simp]:
  "((x orelse y) = TT) \<longleftrightarrow> (x = TT \<or> (x = FF \<and> y = TT))"
  "((x orelse y) = \<bottom>) \<longleftrightarrow> (x = \<bottom> \<or> (x = FF \<and> y = \<bottom>))"
by (cases x; cases y; simp)+

lemma csplit_cfun2: "cont F \<Longrightarrow> (\<Lambda> x. F x) = (\<Lambda> (x, y). F (x, y))"
by (clarsimp simp: cfun_eq_iff prod_cont_iff)

lemma csplit_cfun3: "cont F \<Longrightarrow> (\<Lambda> x. F x) = (\<Lambda> (x, y, z). F (x, y, z))"
by (clarsimp simp: cfun_eq_iff prod_cont_iff)

definition convol :: "('a::cpo \<rightarrow> 'b::cpo) \<rightarrow> ('a \<rightarrow> 'c::cpo) \<rightarrow> 'a \<rightarrow> 'b \<times> 'c" where
  "convol = (\<Lambda> f g x. (f\<cdot>x, g\<cdot>x))"

abbreviation convol_syn :: "('a::cpo \<rightarrow> 'b::cpo) \<Rightarrow> ('a \<rightarrow> 'c::cpo) \<Rightarrow> 'a \<rightarrow> 'b \<times> 'c" (infix "&&" 65) where
  "f && g \<equiv> convol\<cdot>f\<cdot>g"

lemma convol_strict[simp]:
  "convol\<cdot>\<bottom>\<cdot>\<bottom> = \<bottom>"
unfolding convol_def by simp

lemma convol_simp[simp]: "(f && g)\<cdot>x = (f\<cdot>x, g\<cdot>x)"
unfolding convol_def by simp

definition map_prod :: "('a::cpo \<rightarrow> 'c::cpo) \<rightarrow> ('b::cpo \<rightarrow> 'd) \<rightarrow> 'a \<times> 'b \<rightarrow> 'c \<times> 'd" where
  "map_prod = (\<Lambda> f g (x, y). (f\<cdot>x, g\<cdot>y))"

abbreviation map_prod_syn :: "('a \<rightarrow> 'c) \<Rightarrow> ('b \<rightarrow> 'd) \<Rightarrow> 'a \<times> 'b \<rightarrow> 'c \<times> 'd" (infix "**" 65) where
  "f ** g \<equiv> map_prod\<cdot>f\<cdot>g"

lemma map_prod_cfcomp[simp]: "(f ** m) oo (g ** n) = (f oo g) ** (m oo n)"
unfolding map_prod_def by (clarsimp simp: cfun_eq_iff)

lemma map_prod_ID[simp]: "ID ** ID = ID"
unfolding map_prod_def by (clarsimp simp: cfun_eq_iff)

lemma map_prod_app[simp]: "(f ** g)\<cdot>x = (f\<cdot>(cfst\<cdot>x), g\<cdot>(csnd\<cdot>x))"
unfolding map_prod_def by (cases x) (clarsimp simp: cfun_eq_iff)

lemma map_prod_cfst[simp]: "cfst oo (f ** g) = f oo cfst"
by (clarsimp simp: cfun_eq_iff)

lemma map_prod_csnd[simp]: "csnd oo (f ** g) = g oo csnd"
by (clarsimp simp: cfun_eq_iff)


subsection\<open> Extra HOLCF Prelude. \<close>

lemma eq_strict[simp]: "eq\<cdot>(\<bottom>::'a::Eq_strict) = \<bottom>"
by (simp add: cfun_eq_iff)

lemma Integer_le_both_plus_1[simp]:
  fixes m :: Integer
  shows "le\<cdot>(m + 1)\<cdot>(n + 1) = le\<cdot>m\<cdot>n"
by (cases m; cases n; simp add: one_Integer_def)

lemma plus_eq_MkI_conv:
  "l + n = MkI\<cdot>m \<longleftrightarrow> (\<exists>l' n'. l = MkI\<cdot>l' \<and> n = MkI\<cdot>n' \<and> m = l' + n')"
by (cases l, simp) (cases n, auto)

lemma lt_defined:
  fixes x :: Integer
  shows
    "lt\<cdot>x\<cdot>y = TT \<Longrightarrow> (x \<noteq> \<bottom> \<and> y \<noteq> \<bottom>)"
    "lt\<cdot>x\<cdot>y = FF \<Longrightarrow> (x \<noteq> \<bottom> \<and> y \<noteq> \<bottom>)"
by (cases x; cases y; clarsimp)+

lemma le_defined:
  fixes x :: Integer
  shows
    "le\<cdot>x\<cdot>y = TT \<Longrightarrow> (x \<noteq> \<bottom> \<and> y \<noteq> \<bottom>)"
    "le\<cdot>x\<cdot>y = FF \<Longrightarrow> (x \<noteq> \<bottom> \<and> y \<noteq> \<bottom>)"
by (cases x; cases y; clarsimp)+

text\<open>Induction on \<open>Integer\<close>, following the setup for the \<open>int\<close> type.\<close>

definition Integer_ge_less_than :: "int \<Rightarrow> (Integer \<times> Integer) set"
  where "Integer_ge_less_than d = {(MkI\<cdot>z', MkI\<cdot>z) |z z'. d \<le> z' \<and> z' < z}"

lemma wf_Integer_ge_less_than: "wf (Integer_ge_less_than d)"
proof(rule wf_subset)
  show "Integer_ge_less_than d \<subseteq> measure (\<lambda>z. nat (if z = \<bottom> then d else (THE z'. z = MkI\<cdot>z') - d))"
    unfolding Integer_ge_less_than_def by clarsimp
qed simp


subsection\<open> Element equality \label{sec:equality} \<close>

text\<open>

To avoid many extraneous headaches that take us far away from the
interesting parts of our derivation, we assume that the elements of
the pattern and text are drawn from a @{class \<open>pcpo\<close>}
where, if the @{const \<open>eq\<close>} function on this type is
given defined arguments, then its result is defined and coincides with
@{term \<open>(=)\<close>}.

Note this effectively restricts us to @{class \<open>flat\<close>}
element types; see @{cite [cite_macro=citet] \<open>\S4.12\<close>
"Paulson:1987"} for a discussion.

\<close>

class Eq_def = Eq_eq +
  assumes eq_defined: "\<lbrakk>x \<noteq> \<bottom>; y \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> eq\<cdot>x\<cdot>y \<noteq> \<bottom>"
begin

lemma eq_bottom_iff[simp]: "(eq\<cdot>x\<cdot>y = \<bottom>) \<longleftrightarrow> (x = \<bottom> \<or> y = \<bottom>)"
using eq_defined by auto

lemma eq_defined_reflD[simp]:
  "(eq\<cdot>a\<cdot>a = TT) \<longleftrightarrow> a \<noteq> \<bottom>"
  "(TT = eq\<cdot>a\<cdot>a) \<longleftrightarrow> a \<noteq> \<bottom>"
  "a \<noteq> \<bottom> \<Longrightarrow> eq\<cdot>a\<cdot>a = TT"
using eq_refl by auto

lemma eq_FF[simp]:
  "(FF = eq\<cdot>xs\<cdot>ys) \<longleftrightarrow> (xs \<noteq> \<bottom> \<and> ys \<noteq> \<bottom> \<and> xs \<noteq> ys)"
  "(eq\<cdot>xs\<cdot>ys = FF) \<longleftrightarrow> (xs \<noteq> \<bottom> \<and> ys \<noteq> \<bottom> \<and> xs \<noteq> ys)"
by (metis (mono_tags, hide_lams) Exh_tr dist_eq_tr(5) eq_TT_dest eq_bottom_iff eq_self_neq_FF')+

lemma eq_TT[simp]:
  "(TT = eq\<cdot>xs\<cdot>ys) \<longleftrightarrow> (xs \<noteq> \<bottom> \<and> ys \<noteq> \<bottom> \<and> xs = ys)"
  "(eq\<cdot>xs\<cdot>ys = TT) \<longleftrightarrow> (xs \<noteq> \<bottom> \<and> ys \<noteq> \<bottom> \<and> xs = ys)"
by (auto simp: local.eq_TT_dest)

end

instance Integer :: Eq_def by standard simp


subsection \<open>Recursive let bindings\<close>

text\<open>

@{verbatim \<open>
Title: HOL/HOLCF/ex/Letrec.thy
Author: Brian Huffman
\<close>}

See \S\ref{sec:KMP:final_version} for an example use.

\<close>

definition
  CLetrec :: "('a::pcpo \<rightarrow> 'a \<times> 'b::pcpo) \<rightarrow> 'b" where
  "CLetrec = (\<Lambda> F. prod.snd (F\<cdot>(\<mu> x. prod.fst (F\<cdot>x))))"

nonterminal recbinds and recbindt and recbind

syntax
  "_recbind"  :: "logic \<Rightarrow> logic \<Rightarrow> recbind"         ("(2_ =/ _)" 10)
  ""          :: "recbind \<Rightarrow> recbindt"               ("_")
  "_recbindt" :: "recbind \<Rightarrow> recbindt \<Rightarrow> recbindt"   ("_,/ _")
  ""          :: "recbindt \<Rightarrow> recbinds"              ("_")
  "_recbinds" :: "recbindt \<Rightarrow> recbinds \<Rightarrow> recbinds"  ("_;/ _")
  "_Letrec"   :: "recbinds \<Rightarrow> logic \<Rightarrow> logic"        ("(Letrec (_)/ in (_))" 10)

translations
  (recbindt) "x = a, (y,ys) = (b,bs)" == (recbindt) "(x,y,ys) = (a,b,bs)"
  (recbindt) "x = a, y = b"          == (recbindt) "(x,y) = (a,b)"

translations
  "_Letrec (_recbinds b bs) e" == "_Letrec b (_Letrec bs e)"
  "Letrec xs = a in (e,es)"    == "CONST CLetrec\<cdot>(\<Lambda> xs. (a,e,es))"
  "Letrec xs = a in e"         == "CONST CLetrec\<cdot>(\<Lambda> xs. (a,e))"

(*<*)

end
(*>*)
