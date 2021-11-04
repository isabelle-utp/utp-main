chapter \<open>Truth in a Standard Model\<close>

text \<open>Abstract notion of standard model and truth.\<close>

(*<*)
theory Standard_Model imports Deduction
begin
(*>*)

text \<open>First some minimal assumptions, involving
implication, negation and (universal and existential) quantification:\<close>

locale Minimal_Truth =
Syntax_with_Numerals_and_Connectives_False_Disj
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and eql cnj imp all exi
and fls
and dsj
and num
+
\<comment> \<open>The notion of truth for sentences:\<close>
fixes isTrue :: "'fmla \<Rightarrow> bool"
assumes
not_isTrue_fls: "\<not> isTrue fls"
and
isTrue_imp:
"\<And>\<phi> \<psi>. \<phi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> Fvars \<psi> = {} \<Longrightarrow>
  isTrue \<phi> \<Longrightarrow> isTrue (imp \<phi> \<psi>) \<Longrightarrow> isTrue \<psi>"
and
isTrue_all:
"\<And>x \<phi>. x \<in> var \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {x} \<Longrightarrow>
  (\<forall> n \<in> num. isTrue (subst \<phi> n x)) \<Longrightarrow> isTrue (all x \<phi>)"
and
isTrue_exi:
"\<And>x \<phi>. x \<in> var \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {x} \<Longrightarrow>
  isTrue (exi x \<phi>) \<Longrightarrow> (\<exists> n \<in> num. isTrue (subst \<phi> n x))"
and
isTrue_neg:
"\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow>
  isTrue \<phi> \<or> isTrue (neg \<phi>)"
begin

lemma isTrue_neg_excl:
"\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow>
 isTrue \<phi> \<Longrightarrow> isTrue (neg \<phi>) \<Longrightarrow> False"
  using isTrue_imp not_isTrue_fls unfolding neg_def by auto

lemma isTrue_neg_neg:
assumes "\<phi> \<in> fmla" "Fvars \<phi> = {}"
and "isTrue (neg (neg \<phi>))"
shows "isTrue \<phi>"
using assms isTrue_neg isTrue_neg_excl by fastforce

end \<comment> \<open>context @{locale  Minimal_Truth}\<close>


locale Minimal_Truth_Soundness =
Minimal_Truth
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
  isTrue
+
Deduct_with_False_Disj
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
  prv
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and eql cnj imp all exi
and fls
and dsj
and num
and prv
and isTrue
+
assumes
\<comment> \<open>We assume soundness of the provability for sentences (w.r.t. truth):\<close>
sound_isTrue: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> prv \<phi> \<Longrightarrow> isTrue \<phi>"
begin

text \<open>For sound theories, consistency is a fact rather than a hypothesis:\<close>
lemma consistent: consistent
  unfolding consistent_def using not_isTrue_fls sound_isTrue by blast

lemma prv_neg_excl:
"\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> prv \<phi> \<Longrightarrow> prv (neg \<phi>) \<Longrightarrow> False"
using isTrue_neg_excl[of \<phi>] sound_isTrue by auto

lemma prv_imp_implies_isTrue:
assumes [simp]: "\<phi> \<in> fmla" "\<chi> \<in> fmla" "Fvars \<phi> = {}" "Fvars \<chi> = {}"
and p: "prv (imp \<phi> \<chi>)" and i: "isTrue \<phi>"
shows "isTrue \<chi>"
proof-
  have "isTrue (imp \<phi> \<chi>)" using p by (intro sound_isTrue) auto
  thus ?thesis using assms isTrue_imp by blast
qed

text \<open>Sound theories are not only consistent, but also $\omega$-consistent
(in the strong, intuitionistic sense):\<close>

lemma \<omega>consistent: \<omega>consistent
unfolding \<omega>consistent_def proof (safe del: notI)
  fix \<phi> x assume 0[simp,intro]: "\<phi> \<in> fmla"  "x \<in> var" and 1: "Fvars \<phi> = {x}"
  and 00: "\<forall>n\<in>num. prv (neg (subst \<phi> n x))"
  hence "\<forall>n\<in>num. isTrue (neg (subst \<phi> n x))"
    using 00 1 by (auto intro!: sound_isTrue)
  hence "isTrue (all x (neg \<phi>))" by (simp add: "1" isTrue_all)
  moreover
  {have "prv (imp (all x (neg \<phi>)) (neg (exi x \<phi>)))"
    using prv_all_neg_imp_neg_exi by blast
   hence "isTrue (imp (all x (neg \<phi>)) (neg (exi x \<phi>)))"
    by (simp add: "1" sound_isTrue)
  }
  ultimately have "isTrue (neg (exi x \<phi>))"
    by (metis 0 1 Diff_insert_absorb Fvars_all Fvars_exi Fvars_neg all
      exi insert_absorb insert_not_empty isTrue_imp neg)
  hence "\<not> isTrue (neg (neg (exi x \<phi>)))"
    using 1 isTrue_neg_excl by force
  thus "\<not> prv (neg (neg (exi x \<phi>)))"
    using "1" sound_isTrue by auto
qed

lemma \<omega>consistentStd1: \<omega>consistentStd1
  using \<omega>consistent \<omega>consistent_impliesStd1 by blast

lemma \<omega>consistentStd2: \<omega>consistentStd2
  using \<omega>consistent \<omega>consistent_impliesStd2 by blast

end \<comment> \<open>context @{locale Minimal_Truth_Soundness}\<close>

(*<*)
end
(*>*)
