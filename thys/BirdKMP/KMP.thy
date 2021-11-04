(*<*)
theory KMP
imports
  Theory_Of_Lists
begin

hide_const abs

(*>*)
section\<open> Knuth-Morris-Pratt matching according to Bird \label{sec:KMP} \<close>


subsection\<open> Step 1: Specification \label{sec:KMP:specification} \<close>

text\<open>

We begin with the specification of string matching given by @{cite [cite_macro=citet] \<open>Chapter~16\<close>
"Bird:PearlsofFAD:2010"}. (References to ``Bird'' in the following are to this text.) Note that
we assume @{const \<open>eq\<close>} has some nice properties (see \S\ref{sec:equality}) and
use strict lists.

\<close>

fixrec endswith :: "[:'a::Eq_def:] \<rightarrow> [:'a:] \<rightarrow> tr" where
[simp del]: "endswith\<cdot>pat = selem\<cdot>pat oo stails"

fixrec matches :: "[:'a::Eq_def:] \<rightarrow> [:'a:] \<rightarrow> [:Integer:]" where
[simp del]: "matches\<cdot>pat = smap\<cdot>slength oo sfilter\<cdot>(endswith\<cdot>pat) oo sinits"

text\<open>

Bird describes @{term "matches\<cdot>pat\<cdot>xs"} as returning ``a list of integers \<open>p\<close> such that \<open>pat\<close> is a
suffix of @{term "stake\<cdot>p\<cdot>xs"}.''

The following examples illustrate this behaviour:

\<close>

lemma "matches\<cdot>[::]\<cdot>[::] = [:0:]"
unfolding matches.unfold endswith.unfold by simp

lemma "matches\<cdot>[::]\<cdot>[:10::Integer, 20, 30:] = [:0, 1, 2, 3:]"
unfolding matches.unfold endswith.unfold by simp

lemma "matches\<cdot>[:1::Integer,2,3,1,2:]\<cdot>[:1,2,1,2,3,1,2,3,1,2:] = [:7, 10:]"
unfolding matches.unfold endswith.unfold
by (simp add: sfilter_scons_let del: sfilter_strict_scons sfilter.simps)

lemma endswith_strict[simp]:
  "endswith\<cdot>\<bottom> = \<bottom>"
  "endswith\<cdot>pat\<cdot>\<bottom> = \<bottom>"
by (fixrec_simp; simp add: cfun_eq_iff)+

lemma matches_strict[simp]:
  "matches\<cdot>\<bottom> = \<bottom>"
  "matches\<cdot>pat\<cdot>\<bottom> = \<bottom>"
by (fixrec_simp; clarsimp simp: cfun_eq_iff)+

text\<open>

Bird's strategy for deriving KMP from this specification is encoded in the following lemmas:
if we can rewrite @{const \<open>endswith\<close>} as a composition of a predicate with a
@{const \<open>sfoldl\<close>}, then we can rewrite @{const \<open>matches\<close>} into a @{const \<open>sscanl\<close>}.

\<close>

lemma fork_sfoldl:
  shows "sfoldl\<cdot>f1\<cdot>z1 && sfoldl\<cdot>f2\<cdot>z2 = sfoldl\<cdot>(\<Lambda> (a, b) z. (f1\<cdot>a\<cdot>z, f2\<cdot>b\<cdot>z))\<cdot>(z1, z2)" (is "?lhs = ?rhs")
proof(rule cfun_eqI)
  fix xs show "?lhs\<cdot>xs = ?rhs\<cdot>xs"
    by (induct xs arbitrary: z1 z2) simp_all
qed

lemma smap_sfilter_split_cfcomp: \<comment>\<open> Bird (16.4) \<close>
  assumes "f\<cdot>\<bottom> = \<bottom>"
  assumes "p\<cdot>\<bottom> = \<bottom>"
  shows "smap\<cdot>f oo sfilter\<cdot>(p oo g) = smap\<cdot>cfst oo sfilter\<cdot>(p oo csnd) oo smap\<cdot>(f && g)" (is "?lhs = ?rhs")
proof(rule cfun_eqI)
  fix xs show "?lhs\<cdot>xs = ?rhs\<cdot>xs"
    using assms by (induct xs) (simp_all add: If2_def[symmetric] split: If2_splits)
qed

lemma Bird_strategy:
  assumes endswith: "endswith\<cdot>pat = p oo sfoldl\<cdot>op\<cdot>z"
  assumes step: "step = (\<Lambda> (n, x) y. (n + 1, op\<cdot>x\<cdot>y))"
  assumes "p\<cdot>\<bottom> = \<bottom>" \<comment>\<open> We can reasonably expect the predicate to be strict \<close>
  shows "matches\<cdot>pat = smap\<cdot>cfst oo sfilter\<cdot>(p oo csnd) oo sscanl\<cdot>step\<cdot>(0, z)"
apply (simp add: matches.simps assoc_oo endswith)
apply (subst smap_sfilter_split_cfcomp, fastforce, fact)
apply (subst slength_sfoldl)
apply (subst fork_sfoldl)
apply (simp add: oo_assoc[symmetric])
apply (subst sinits_sscanl)
apply (fold step)
apply (rule refl)
done

text\<open>

Bird proceeds by reworking @{const \<open>endswith\<close>} into the form required by @{thm [source] "Bird_strategy"}.
This is eased by an alternative definition of @{const \<open>endswith\<close>}.

\<close>

lemma sfilter_supto:
  assumes "0 \<le> d"
  shows "sfilter\<cdot>(\<Lambda> x. le\<cdot>(MkI\<cdot>n - x)\<cdot>(MkI\<cdot>d))\<cdot>(supto\<cdot>(MkI\<cdot>m)\<cdot>(MkI\<cdot>n))
       = supto\<cdot>(MkI\<cdot>(if m \<le> n - d then n - d else m))\<cdot>(MkI\<cdot>n)" (is "?sfilterp\<cdot>?suptomn = _")
proof(cases "m \<le> n - d")
  case True
  moreover
  from True assms have "?sfilterp\<cdot>?suptomn = ?sfilterp\<cdot>(supto\<cdot>(MkI\<cdot>m)\<cdot>(MkI\<cdot>(n - d - 1)) :@ supto\<cdot>(MkI\<cdot>(n - d))\<cdot>(MkI\<cdot>n))"
    using supto_split1 by auto
  moreover from True assms have "?sfilterp\<cdot>(supto\<cdot>(MkI\<cdot>m)\<cdot>(MkI\<cdot>(n - d - 1))) = [::]" by auto
  ultimately show ?thesis by (clarsimp intro!: trans[OF sfilter_cong[OF refl] sfilter_const_TT])
next
  case False then show ?thesis
    by (clarsimp intro!: trans[OF sfilter_cong[OF refl] sfilter_const_TT])
qed

lemma endswith_eq_sdrop: "endswith\<cdot>pat\<cdot>xs = eq\<cdot>pat\<cdot>(sdrop\<cdot>(slength\<cdot>xs - slength\<cdot>pat)\<cdot>xs)"
proof(cases "pat = \<bottom>" "xs = \<bottom>" rule: bool.exhaust[case_product bool.exhaust])
  case False_False then show ?thesis
    by (cases "endswith\<cdot>pat\<cdot>xs";
        simp only: endswith.simps cfcomp2 stails_sdrop';
        force simp: zero_Integer_def one_Integer_def elim: slengthE)
qed simp_all

lemma endswith_def2:  \<comment>\<open> Bird p127 \<close>
  shows "endswith\<cdot>pat\<cdot>xs = eq\<cdot>pat\<cdot>(shead\<cdot>(sfilter\<cdot>(\<Lambda> x. prefix\<cdot>x\<cdot>pat)\<cdot>(stails\<cdot>xs)))" (is "?lhs = ?rhs")
proof(cases "pat = \<bottom>" "xs = \<bottom>" rule: bool.exhaust[case_product bool.exhaust])
  case False_False
  from False_False obtain patl xsl where *: "slength\<cdot>xs = MkI\<cdot>xsl" "0 \<le> xsl" "slength\<cdot>pat = MkI\<cdot>patl" "0 \<le> patl"
    by (meson Integer.exhaust slength_bottom_iff slength_ge_0)
  let ?patl_xsl = "if patl \<le> xsl then xsl - patl else 0"
  have "?rhs = eq\<cdot>pat\<cdot>(shead\<cdot>(sfilter\<cdot>(\<Lambda> x. le\<cdot>(slength\<cdot>x)\<cdot>(slength\<cdot>pat) andalso prefix\<cdot>x\<cdot>pat)\<cdot>(stails\<cdot>xs)))"
    by (subst prefix_slength_strengthen) simp
  also have "\<dots> = eq\<cdot>pat\<cdot>(shead\<cdot>(sfilter\<cdot>(\<Lambda> x. prefix\<cdot>x\<cdot>pat)\<cdot>(sfilter\<cdot>(\<Lambda> x. le\<cdot>(slength\<cdot>x)\<cdot>(slength\<cdot>pat))\<cdot>(stails\<cdot>xs))))"
    by (simp add: sfilter_sfilter')
  also have "\<dots> = eq\<cdot>pat\<cdot>(shead\<cdot>(smap\<cdot>(\<Lambda> k. sdrop\<cdot>k\<cdot>xs)\<cdot>(sfilter\<cdot>(\<Lambda> k. prefix\<cdot>(sdrop\<cdot>k\<cdot>xs)\<cdot>pat)\<cdot>(sfilter\<cdot>(\<Lambda> k. le\<cdot>(slength\<cdot>(sdrop\<cdot>k\<cdot>xs))\<cdot>(MkI\<cdot>patl))\<cdot>(supto\<cdot>(MkI\<cdot>0)\<cdot>(MkI\<cdot>xsl))))))"
    using \<open>slength\<cdot>xs = MkI\<cdot>xsl\<close> \<open>slength\<cdot>pat = MkI\<cdot>patl\<close>
    by (simp add: stails_sdrop' sfilter_smap' cfcomp1 zero_Integer_def)
  also have "\<dots> = eq\<cdot>pat\<cdot>(shead\<cdot>(smap\<cdot>(\<Lambda> k. sdrop\<cdot>k\<cdot>xs)\<cdot>(sfilter\<cdot>(\<Lambda> k. prefix\<cdot>(sdrop\<cdot>k\<cdot>xs)\<cdot>pat)\<cdot>(sfilter\<cdot>(\<Lambda> k. le\<cdot>(MkI\<cdot>xsl - k)\<cdot>(MkI\<cdot>patl))\<cdot>(supto\<cdot>(MkI\<cdot>0)\<cdot>(MkI\<cdot>xsl))))))"
    using \<open>slength\<cdot>xs = MkI\<cdot>xsl\<close>
    by (subst (2) sfilter_cong[where p'="\<Lambda> x. le\<cdot>(MkI\<cdot>xsl - x)\<cdot>(MkI\<cdot>patl)"]; fastforce simp: zero_Integer_def)
  also have "\<dots> = If prefix\<cdot>(sdrop\<cdot>(MkI\<cdot>?patl_xsl)\<cdot>xs)\<cdot>pat
                  then eq\<cdot>pat\<cdot>(sdrop\<cdot>(MkI\<cdot>?patl_xsl)\<cdot>xs)
                  else eq\<cdot>pat\<cdot>(shead\<cdot>(smap\<cdot>(\<Lambda> k. sdrop\<cdot>k\<cdot>xs)\<cdot>(sfilter\<cdot>(\<Lambda> x. prefix\<cdot>(sdrop\<cdot>x\<cdot>xs)\<cdot>pat)\<cdot>(supto\<cdot>(MkI\<cdot>(?patl_xsl + 1))\<cdot>(MkI\<cdot>xsl)))))"
    using False_False \<open>0 \<le> xsl\<close> \<open>0 \<le> patl\<close>
    by (subst sfilter_supto) (auto simp: If_distr one_Integer_def)
  also have "\<dots> = ?lhs" (is "If ?c then _ else ?else = _")
  proof(cases ?c)
    case TT with \<open>slength\<cdot>xs = MkI\<cdot>xsl\<close> \<open>slength\<cdot>pat = MkI\<cdot>patl\<close>
    show ?thesis by (simp add: endswith_eq_sdrop sdrop_neg zero_Integer_def)
  next
    case FF \<comment>\<open> Recursive case: the lists generated by \<open>supto\<close> are too short \<close>
    have "?else = shead\<cdot>(smap\<cdot>(\<Lambda> x. eq\<cdot>pat\<cdot>(sdrop\<cdot>x\<cdot>xs))\<cdot>(sfilter\<cdot>(\<Lambda> x. prefix\<cdot>(sdrop\<cdot>x\<cdot>xs)\<cdot>pat)\<cdot>(supto\<cdot>(MkI\<cdot>(?patl_xsl + 1))\<cdot>(MkI\<cdot>xsl))))"
      using FF by (subst shead_smap_distr[where f="eq\<cdot>pat", symmetric]) (auto simp: cfcomp1)
    also have "\<dots> = shead\<cdot>(smap\<cdot>(\<Lambda> x. seq\<cdot>x\<cdot>FF)\<cdot>(sfilter\<cdot>(\<Lambda> x. prefix\<cdot>(sdrop\<cdot>x\<cdot>xs)\<cdot>pat)\<cdot>(supto\<cdot>(MkI\<cdot>(?patl_xsl + 1))\<cdot>(MkI\<cdot>xsl))))"
      using False_False * by (subst smap_cong[OF refl, where f'="\<Lambda> x. seq\<cdot>x\<cdot>FF"]) (auto simp: zero_Integer_def split: if_splits)
    also from * FF have "\<dots> = ?lhs"
      apply (auto 0 0 simp: shead_smap_distr seq_conv_if endswith_eq_sdrop zero_Integer_def dest!: prefix_FF_not_snilD)
        apply (metis (full_types) le_MkI_MkI linorder_not_less order_refl prefix_FF_not_snilD sdrop_all zless_imp_add1_zle)
       using FF apply fastforce
      apply (metis add.left_neutral le_MkI_MkI linorder_not_less order_refl prefix_FF_not_snilD sdrop_0(1) sdrop_all zero_Integer_def zless_imp_add1_zle)
      done
    finally show ?thesis using FF by simp
  qed (simp add: False_False)
  finally show ?thesis ..
qed simp_all

text\<open>

Bird then generalizes @{term \<open>sfilter\<cdot>(\<Lambda> x. prefix\<cdot>x\<cdot>pat) oo stails\<close>} to @{term \<open>split\<close>},
where ``\<open>split\<cdot>pat\<cdot>xs\<close> splits \<open>pat\<close> into two lists \<open>us\<close> and \<open>vs\<close> so that
@{prop \<open>us :@ vs = pat\<close>} and \<open>us\<close> is the longest suffix of \<open>xs\<close> that is a prefix of \<open>pat\<close>.''

\<close>

fixrec split :: "[:'a::Eq_def:] \<rightarrow> [:'a:] \<rightarrow> [:'a:] \<times> [:'a:]" where \<comment>\<open> Bird p128 \<close>
[simp del]: "split\<cdot>pat\<cdot>xs = If prefix\<cdot>xs\<cdot>pat then (xs, sdrop\<cdot>(slength\<cdot>xs)\<cdot>pat) else split\<cdot>pat\<cdot>(stail\<cdot>xs)"

lemma split_strict[simp]:
  shows "split\<cdot>\<bottom> = \<bottom>"
    and "split\<cdot>pat\<cdot>\<bottom> = \<bottom>"
by fixrec_simp+

lemma split_bottom_iff[simp]: "(split\<cdot>pat\<cdot>xs = \<bottom>) \<longleftrightarrow> (pat = \<bottom> \<or> xs = \<bottom>)"
by (cases "pat = \<bottom>"; clarsimp) (induct xs; subst split.unfold; simp)

lemma split_snil[simp]:
  assumes "pat \<noteq> \<bottom>"
  shows "split\<cdot>pat\<cdot>[::] = ([::], pat)"
using assms by fixrec_simp

lemma split_pattern: \<comment>\<open> Bird p128, observation \<close>
  assumes "xs \<noteq> \<bottom>"
  assumes "split\<cdot>pat\<cdot>xs = (us, vs)"
  shows "us :@ vs = pat"
using assms
proof(cases "pat = \<bottom>", simp, induct xs arbitrary: us vs)
  case snil then show ?case by (subst (asm) split.unfold) simp
next
  case (scons x xs) then show ?case
    by (subst (asm) (3) split.unfold)
       (fastforce dest: prefix_sdrop_slength simp: If2_def[symmetric] split: If2_splits)
qed simp

lemma endswith_split: \<comment>\<open> Bird p128, after defining \<open>split\<close> \<close>
  shows "endswith\<cdot>pat = snull oo csnd oo split\<cdot>pat"
proof(rule cfun_eqI)
  fix xs show "endswith\<cdot>pat\<cdot>xs = (snull oo csnd oo split\<cdot>pat)\<cdot>xs"
  proof(cases "pat = \<bottom>", simp, induct xs)
    case (scons x xs) then show ?case
      unfolding endswith_def2
      by (subst split.unfold)
         (fastforce dest: prefix_sdrop_prefix_eq simp: If2_def[symmetric] If_distr snull_eq_snil split: If2_splits)
  qed (simp_all add: snull_eq_snil endswith.simps)
qed

lemma split_length_lt:
  assumes "pat \<noteq> \<bottom>"
  assumes "xs \<noteq> \<bottom>"
  shows "lt\<cdot>(slength\<cdot>(prod.fst (split\<cdot>pat\<cdot>xs)))\<cdot>(slength\<cdot>xs + 1) = TT"
using assms
proof(induct xs)
  case (scons x xs) then show ?case
    by (subst split.unfold)
       (auto simp: If2_def[symmetric] one_Integer_def split: If2_splits elim!: slengthE elim: lt_trans)
qed simp_all

text\<open>

The predicate \<open>p\<close> required by @{thm [source] "Bird_strategy"} is therefore \<open>snull oo csnd\<close>. It
remains to find \<open>op\<close> and \<open>z\<close> such that:

\<^item> @{term \<open>split\<cdot>pat\<cdot>[::] = z\<close>}
\<^item> @{term \<open>split\<cdot>pat\<cdot>(xs :@ [:x:]) = op\<cdot>(split\<cdot>pat\<cdot>xs)\<cdot>x\<close>}

\<close>
text\<open>

so that @{term \<open>split = sfoldl\<cdot>op\<cdot>z\<close>}.

We obtain @{term \<open>z = ([::], pat)\<close>} directly from the definition of @{term \<open>split\<close>}.

Bird derives \<open>op\<close> on the basis of this crucial observation:

\<close>

lemma split_snoc: \<comment>\<open> Bird p128 \<close>
  shows "split\<cdot>pat\<cdot>(xs :@ [:x:]) = split\<cdot>pat\<cdot>(cfst\<cdot>(split\<cdot>pat\<cdot>xs) :@ [:x:])"
proof(cases "pat = \<bottom>", simp, cases "x = \<bottom>", simp, induct xs)
  case (scons x xs) then show ?case
    apply -
    apply (subst (1 3) split.unfold)
    apply (clarsimp simp: If2_def[symmetric] split: If2_splits; intro conjI impI)
      apply (subst split.unfold; fastforce)
     apply (subst split.unfold; fastforce)
    apply (simp add: append_prefixD)
    done
qed simp_all

fixrec \<comment>\<open> Bird p129 \<close>
  op :: "[:'a::Eq_def:] \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> 'a \<rightarrow> [:'a:] \<times> [:'a:]"
where
[simp del]:
  "op\<cdot>pat\<cdot>(us, vs)\<cdot>x =
     (     If prefix\<cdot>[:x:]\<cdot>vs then (us :@ [:x:], stail\<cdot>vs)
      else If snull\<cdot>us then ([::], pat)
      else op\<cdot>pat\<cdot>(split\<cdot>pat\<cdot>(stail\<cdot>us))\<cdot>x )"

lemma op_strict[simp]:
  "op\<cdot>pat\<cdot>\<bottom> = \<bottom>"
  "op\<cdot>pat\<cdot>(us, \<bottom>) = \<bottom>"
  "op\<cdot>pat\<cdot>usvs\<cdot>\<bottom> = \<bottom>"
by fixrec_simp+

text\<open>

Bird demonstrates that @{const \<open>op\<close>} is partially correct wrt @{const \<open>split\<close>}, i.e.,
@{prop "op\<cdot>pat\<cdot>(split\<cdot>pat\<cdot>xs)\<cdot>x \<sqsubseteq> split\<cdot>pat\<cdot>(xs :@ [:x:])"}. For total correctness we
essentially prove that @{const \<open>op\<close>} terminates on well-defined arguments with an inductive argument.

\<close>

lemma op_induct[case_names step]:
  fixes usvs:: "[:'a:] \<times> 'b"
  assumes step: "\<And>usvs. (\<And>usvs'. lt\<cdot>(slength\<cdot>(cfst\<cdot>usvs'))\<cdot>(slength\<cdot>(cfst\<cdot>usvs)) = TT \<Longrightarrow> P usvs') \<Longrightarrow> P usvs"
  shows "P usvs"
proof(induct usvs rule: wf_induct)
  let ?r = "{ (usvs', usvs) |(usvs :: [:'a:] \<times> 'b) (usvs' :: [:'a:] \<times> 'b). lt\<cdot>(slength\<cdot>(cfst\<cdot>usvs'))\<cdot>(slength\<cdot>(cfst\<cdot>usvs)) = TT }"
  show "wf ?r"
  proof(rule wf_subset[OF wf_inv_image[where f="\<lambda>(x, _). slength\<cdot>x", OF wf_subset[OF wf_Integer_ge_less_than[where d=0]]]])
    let ?rslen = "{ (slength\<cdot>us', slength\<cdot>us) |(us :: [:'a:]) (us' :: [:'a:]). lt\<cdot>(slength\<cdot>us')\<cdot>(slength\<cdot>us) = TT }"
    show "?rslen \<subseteq> Integer_ge_less_than 0"
      apply (clarsimp simp: Integer_ge_less_than_def zero_Integer_def)
      apply (metis Integer.exhaust dist_eq_tr(4) dist_eq_tr(6) lt_Integer_bottom_iff lt_MkI_MkI slength_ge_0)
      done
    show "?r \<subseteq> inv_image ?rslen (\<lambda>(x, _). slength\<cdot>x)" by (auto 0 3)
  qed
  fix usvs
  assume "\<forall>usvs'. (usvs', usvs) \<in> ?r \<longrightarrow> P usvs'"
  then show "P usvs"
    by - (rule step; clarsimp; metis eq_fst_iff)
qed

lemma op_induct'[case_names step]:
  assumes step: "\<And>us. (\<And>us'. lt\<cdot>(slength\<cdot>us')\<cdot>(slength\<cdot>us) = TT \<Longrightarrow> P us') \<Longrightarrow> P us"
  shows "P us"
by (rule op_induct[where P="P \<circ> prod.fst" and usvs="(us, vs)" for vs::unit, simplified])
   (fastforce intro: step)

lemma split_snoc_op:
  "split\<cdot>pat\<cdot>(xs :@ [:x:]) = op\<cdot>pat\<cdot>(split\<cdot>pat\<cdot>xs)\<cdot>x"
proof(induct "split\<cdot>pat\<cdot>xs" arbitrary: xs rule: op_induct)
  case (step xs) show ?case
  proof(cases "pat = \<bottom>" "xs = \<bottom>" "x = \<bottom>" rule: bool.exhaust[case_product bool.exhaust bool.exhaust])
    case False_False_False
    obtain us vs where *: "split\<cdot>pat\<cdot>xs = (us, vs)" by fastforce
    from False_False_False * have **: "prefix\<cdot>(us :@ [:x:])\<cdot>pat = prefix\<cdot>[:x:]\<cdot>vs"
      using split_pattern same_prefix_prefix sappend_bottom_iff by blast
    from False_False_False * **
    have ***: "sdrop\<cdot>(slength\<cdot>(us :@ [:x:]))\<cdot>pat = stail\<cdot>vs" if "prefix\<cdot>(us :@ [:x:])\<cdot>pat = TT"
      using sdrop_sappend_same[where xs="us :@ [:x:]"] that
      by (cases vs; clarsimp) (fastforce dest!: split_pattern)
    from False_False_False * ** *** show ?thesis
      apply -
      apply (subst split_snoc)
      apply (subst split.unfold)
      apply (subst op.unfold)
      apply (fastforce simp: If2_def[symmetric] snull_FF_conv split: If2_splits intro: step split_length_lt)
      done
  qed simp_all
qed

lemma split_sfoldl_op:
  assumes "pat \<noteq> \<bottom>"
  shows "sfoldl\<cdot>(op\<cdot>pat)\<cdot>([::], pat) = split\<cdot>pat" (is "?lhs = ?rhs")
proof -
  have "?lhs\<cdot>xs = ?rhs\<cdot>xs" for xs
    using assms by (induct xs rule: srev_induct) (simp_all add: split_snoc_op)
  then show ?thesis by (simp add: cfun_eq_iff)
qed

lemma matches_op:
  shows "matches\<cdot>pat = smap\<cdot>cfst oo sfilter\<cdot>(snull oo csnd oo csnd)
                                oo sscanl\<cdot>(\<Lambda> (n, usvs) x. (n + 1, op\<cdot>pat\<cdot>usvs\<cdot>x))\<cdot>(0, ([::], pat))" (is "?lhs = ?rhs")
proof(cases "pat = \<bottom>")
  case True
  then have "?lhs\<cdot>xs = ?rhs\<cdot>xs" for xs by (cases xs; clarsimp)
  then show ?thesis by (simp add: cfun_eq_iff)
next
  case False then show ?thesis
    apply (subst (2) oo_assoc)
    apply (rule Bird_strategy)
    apply (simp_all add: endswith_split split_sfoldl_op oo_assoc)
    done
qed

text\<open>

Using @{thm [source] "split_sfoldl_op"} we can rewrite @{const \<open>op\<close>} into a more perspicuous form
that exhibits how KMP handles the failure of the text to continue matching the pattern:

\<close>

fixrec
  op' :: "[:'a::Eq_def:] \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> 'a \<rightarrow> [:'a:] \<times> [:'a:]"
where
[simp del]:
  "op'\<cdot>pat\<cdot>(us, vs)\<cdot>x =
     (     If prefix\<cdot>[:x:]\<cdot>vs then (us :@ [:x:], stail\<cdot>vs) \<comment> \<open> continue matching \<close>
      else If snull\<cdot>us then ([::], pat) \<comment> \<open> fail at the start of the pattern: discard \<open>x\<close> \<close>
      else sfoldl\<cdot>(op'\<cdot>pat)\<cdot>([::], pat)\<cdot>(stail\<cdot>us :@ [:x:]) \<comment> \<open> fail later: discard \<open>shead\<cdot>us\<close> and determine where to restart \<close>
     )"

text\<open>

Intuitively if \<open>x\<close> continues the pattern match then we
extend the @{const \<open>split\<close>} of \<open>pat\<close>
recorded in \<open>us\<close> and \<open>vs\<close>.  Otherwise we
need to find a prefix of \<open>pat\<close> to continue matching
with. If we have yet to make any progress (i.e., \<open>us =
[::]\<close>) we restart with the entire \<open>pat\<close> (aka
\<open>z\<close>) and discard \<open>x\<close>.  Otherwise, because a
match cannot begin with @{term \<open>us :@ [:x:]\<close>}, we @{const
\<open>split\<close>} \<open>pat\<close> (aka \<open>z\<close>) by
iterating @{const \<open>op'\<close>} over @{term
\<open>stail\<cdot>us :@ [:x:]\<close>}.  The remainder of the
development is about memoising this last computation.

This is not yet the full KMP algorithm as it lacks what we call the
`K' optimisation, which we add in \S\ref{sec:KMP:data_refinement}.
Note that a termination proof for @{const "op'"} in HOL is tricky due
to its use of higher-order nested recursion via @{const
\<open>sfoldl\<close>}.

\<close>

lemma op'_strict[simp]:
  "op'\<cdot>pat\<cdot>\<bottom> = \<bottom>"
  "op'\<cdot>pat\<cdot>(us, \<bottom>) = \<bottom>"
  "op'\<cdot>pat\<cdot>usvs\<cdot>\<bottom> = \<bottom>"
by fixrec_simp+

lemma sfoldl_op'_strict[simp]:
  "op'\<cdot>pat\<cdot>(sfoldl\<cdot>(op'\<cdot>pat)\<cdot>(us, \<bottom>)\<cdot>xs)\<cdot>x = \<bottom>"
by (induct xs arbitrary: x rule: srev_induct) simp_all

lemma op'_op:
  shows "op'\<cdot>pat\<cdot>usvs\<cdot>x = op\<cdot>pat\<cdot>usvs\<cdot>x"
proof(cases "pat = \<bottom>" "x = \<bottom>" rule: bool.exhaust[case_product bool.exhaust])
  case True_False then show ?thesis
    apply (subst op'.unfold)
    apply (subst op.unfold)
    apply simp
    done
next
  case False_False then show ?thesis
  proof(induct usvs arbitrary: x rule: op_induct)
    case (step usvs x)
    have *: "sfoldl\<cdot>(op'\<cdot>pat)\<cdot>([::], pat)\<cdot>xs = sfoldl\<cdot>(op\<cdot>pat)\<cdot>([::], pat)\<cdot>xs"
         if "lt\<cdot>(slength\<cdot>xs)\<cdot>(slength\<cdot>(cfst\<cdot>usvs)) = TT" for xs
    using that
    proof(induct xs rule: srev_induct)
      case (ssnoc x' xs')
      from ssnoc(1,2,4) have "lt\<cdot>(slength\<cdot>xs')\<cdot>(slength\<cdot>(cfst\<cdot>usvs)) = TT"
        using lt_slength_0(2) lt_trans by auto
      moreover
      from step(2) ssnoc(1,2,4) have "lt\<cdot>(slength\<cdot>(cfst\<cdot>(split\<cdot>pat\<cdot>xs')))\<cdot>(slength\<cdot>(cfst\<cdot>usvs)) = TT"
        using lt_trans split_length_lt by (auto 10 0)
      ultimately show ?case by (simp add: ssnoc.hyps split_sfoldl_op split_snoc_op step)
    qed simp_all
    from step.prems show ?case
      apply (subst op'.unfold)
      apply (subst op.unfold)
      apply (clarsimp simp: If2_def[symmetric] snull_FF_conv split_sfoldl_op[symmetric] * split: If2_splits)
      apply (clarsimp simp: split_sfoldl_op step split_length_lt)
      done
  qed
qed simp_all


subsection\<open> Step 2: Data refinement and the `K' optimisation \label{sec:KMP:data_refinement} \<close>

text\<open>

Bird memoises the restart computation in @{const \<open>op'\<close>} in two steps.  The first reifies
the control structure of @{const \<open>op'\<close>} into a non-wellfounded tree, which we discuss here. The
second increases the sharing in this tree; see \S\ref{sec:KMP:increase_sharing}.

Briefly, we cache the @{term \<open>sfoldl\<cdot>(op'\<cdot>pat)\<cdot>([::], pat)\<cdot>(stail\<cdot>us :@ [:x:])\<close>}
computation in @{const \<open>op'\<close>} by finding a ``representation'' type @{typ "'t"}
for the ``abstract'' type @{typ \<open>[:'a::Eq_def:] \<times> [:'a:]\<close>}, a
pair of functions @{term \<open>rep :: [:'a::Eq_def:] \<times> [:'a:] \<rightarrow> 't\<close>},
@{term \<open>abs :: 't \<rightarrow> [:'a::Eq_def:] \<times> [:'a:]\<close>} where @{prop \<open>abs oo rep = ID\<close>}, and then
finding a derived form of @{const \<open>op'\<close>} that works on @{typ "'t"} rather
than @{typ "[:'a::Eq_def:] \<times> [:'a:]"}. We also take the opportunity to add the `K' optimisation in the form of the @{term \<open>next\<close>}
function.

As such steps are essentially @{emph \<open>deus ex machina\<close>}, we try to provide some intuition
after showing the new definitions.

\<close>

domain 'a tree \<comment>\<open> Bird p130 \<close>
  = Null
  | Node (label :: 'a) (lazy left :: "'a tree") (lazy right :: "'a tree") \<comment>\<open> Strict in the label @{typ "'a"} \<close>

(*<*)

lemma tree_injects'[simp]: \<comment>\<open> An unconditional form of @{thm [source] tree.injects}. \<close>
  "(Node\<cdot>a\<cdot>l\<cdot>r = Node\<cdot>a'\<cdot>l'\<cdot>r') \<longleftrightarrow> (a = a' \<and> (a \<noteq> \<bottom> \<longrightarrow> l = l' \<and> r = r'))"
by (cases "a = \<bottom>"; clarsimp)

lemma match_Null_match_Node_tree_case: "match_Null\<cdot>t\<cdot>k1 +++ match_Node\<cdot>t\<cdot>k2 = tree_case\<cdot>k1\<cdot>k2\<cdot>t"
by (cases t) simp_all

lemma match_Node_mplus_match_Node: "match_Node\<cdot>x\<cdot>k1 +++ match_Node\<cdot>x\<cdot>k2 = match_Node\<cdot>x\<cdot>(\<Lambda> v l r. k1\<cdot>v\<cdot>l\<cdot>r +++ k2\<cdot>v\<cdot>l\<cdot>r)"
by (cases x; clarsimp)

lemma tree_case_distr:
  "f\<cdot>\<bottom> = \<bottom> \<Longrightarrow> f\<cdot>(tree_case\<cdot>g\<cdot>h\<cdot>t) = tree_case\<cdot>(f\<cdot>g)\<cdot>(\<Lambda> x l r. f\<cdot>(h\<cdot>x\<cdot>l\<cdot>r))\<cdot>t"
  "(tree_case\<cdot>g'\<cdot>h'\<cdot>t)\<cdot>z = tree_case\<cdot>(g'\<cdot>z)\<cdot>(\<Lambda> x l r. h'\<cdot>x\<cdot>l\<cdot>r\<cdot>z)\<cdot>t"
by (case_tac [!] t) simp_all

lemma tree_case_cong:
  assumes "t = t'"
  assumes "t' = Null \<Longrightarrow> n = n'"
  assumes "\<And>v l r. \<lbrakk>t' = Node\<cdot>v\<cdot>l\<cdot>r; v \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> c v l r = c' v l r"
  assumes "cont (\<lambda>(x, y, z). c x y z)"
  assumes "cont (\<lambda>(x, y, z). c' x y z)"
  shows "tree_case\<cdot>n\<cdot>(\<Lambda> v l r. c v l r)\<cdot>t = tree_case\<cdot>n'\<cdot>(\<Lambda> v l r. c' v l r)\<cdot>t'"
using assms by (cases t; cases t'; clarsimp simp: prod_cont_iff)

lemma tree_take_smaller:
  assumes "tree_take i\<cdot>t = tree_take i\<cdot>u"
  assumes "j \<le> i"
  shows "tree_take j\<cdot>t = tree_take j\<cdot>u"
using assms by (metis min.orderE tree.take_take)

fixrec tree_map' :: "('a \<rightarrow> 'b) \<rightarrow> 'a tree \<rightarrow> 'b tree" where
  "tree_map'\<cdot>f\<cdot>Null = Null"
| "a \<noteq> \<bottom> \<Longrightarrow> tree_map'\<cdot>f\<cdot>(Node\<cdot>a\<cdot>l\<cdot>r) = Node\<cdot>(f\<cdot>a)\<cdot>(tree_map'\<cdot>f\<cdot>l)\<cdot>(tree_map'\<cdot>f\<cdot>r)"

lemma tree_map'_strict[simp]: "tree_map'\<cdot>f\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma tree_map'_ID': "tree_map'\<cdot>ID\<cdot>xs = xs"
by (induct xs) simp_all

lemma tree_map'_ID[simp]: "tree_map'\<cdot>ID = ID"
by (clarsimp simp: cfun_eq_iff tree_map'_ID')

lemma tree_map'_strict_scons[simp]:
  assumes "f\<cdot>\<bottom> = \<bottom>"
  shows "tree_map'\<cdot>f\<cdot>(Node\<cdot>a\<cdot>l\<cdot>r) = Node\<cdot>(f\<cdot>a)\<cdot>(tree_map'\<cdot>f\<cdot>l)\<cdot>(tree_map'\<cdot>f\<cdot>r)"
using assms by (cases "a = \<bottom>"; clarsimp)

lemma tree_map'_comp'[simp]:
  assumes "f\<cdot>\<bottom> = \<bottom>"
  shows "tree_map'\<cdot>f\<cdot>(tree_map'\<cdot>g\<cdot>t) = tree_map'\<cdot>(f oo g)\<cdot>t"
using assms by (induct t) simp_all

lemma tree_map'_comp[simp]:
  assumes "f\<cdot>\<bottom> = \<bottom>"
  shows "tree_map'\<cdot>f oo tree_map'\<cdot>g = tree_map'\<cdot>(f oo g)"
using assms by (clarsimp simp: cfun_eq_iff)

lemma tree_unique: \<comment>\<open> Adapted from @{cite [cite_macro=citet] "Matthews:1999"} for \emph{contractive functions}. \<close>
  fixes x :: "'a tree"
  assumes xfx: "x = f\<cdot>x"
  assumes f: "\<And>i t u. tree_take i\<cdot>t = tree_take i\<cdot>u
                      \<Longrightarrow> tree_take (Suc i)\<cdot>(f\<cdot>t) = tree_take (Suc i)\<cdot>(f\<cdot>u)"
  shows "x = fix\<cdot>f"
proof(rule tree.take_lemma)
  fix i show "tree_take i\<cdot>x = tree_take i\<cdot>(fix\<cdot>f)"
  proof(induct i)
    case (Suc i) from xfx f[OF Suc, folded fix_eq] show ?case by simp
  qed simp
qed

(*>*)

fixrec "next" :: "[:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> ([:'a:] \<times> [:'a:]) tree" where
  "next\<cdot>[::]\<cdot>t = t"
| "\<lbrakk>x \<noteq> \<bottom>; xs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow>
   next\<cdot>(x :# xs)\<cdot>Null = Null"
| "\<lbrakk>x \<noteq> \<bottom>; xs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow>
   next\<cdot>(x :# xs)\<cdot>(Node\<cdot>(us, [::])\<cdot>l\<cdot>r) = Node\<cdot>(us, [::])\<cdot>l\<cdot>r"
| "\<lbrakk>v \<noteq> \<bottom>; vs \<noteq> \<bottom>; x \<noteq> \<bottom>; xs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow>
   next\<cdot>(x :# xs)\<cdot>(Node\<cdot>(us, v :# vs)\<cdot>l\<cdot>r) = If eq\<cdot>x\<cdot>v then l else Node\<cdot>(us, v :# vs)\<cdot>l\<cdot>r"

fixrec \<comment>\<open> Bird p131 ``an even simpler form'', with the `K' optimisation \<close>
    root2  :: "[:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree"
and op2    :: "[:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> 'a \<rightarrow> ([:'a:] \<times> [:'a:]) tree"
and rep2   :: "[:'a:] \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree"
and left2  :: "[:'a:] \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree"
and right2 :: "[:'a:] \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree"
where
  [simp del]:
  "root2\<cdot>pat = rep2\<cdot>pat\<cdot>([::], pat)"
| "op2\<cdot>pat\<cdot>Null\<cdot>x = root2\<cdot>pat"
| "usvs \<noteq> \<bottom> \<Longrightarrow>
   op2\<cdot>pat\<cdot>(Node\<cdot>usvs\<cdot>l\<cdot>r)\<cdot>x = If prefix\<cdot>[:x:]\<cdot>(csnd\<cdot>usvs) then r else op2\<cdot>pat\<cdot>l\<cdot>x"
| [simp del]:
  "rep2\<cdot>pat\<cdot>usvs = Node\<cdot>usvs\<cdot>(left2\<cdot>pat\<cdot>usvs)\<cdot>(right2\<cdot>pat\<cdot>usvs)"
| "left2\<cdot>pat\<cdot>([::], vs) = next\<cdot>vs\<cdot>Null"
| "\<lbrakk>u \<noteq> \<bottom>; us \<noteq> \<bottom>\<rbrakk> \<Longrightarrow>
   left2\<cdot>pat\<cdot>(u :# us, vs) = next\<cdot>vs\<cdot>(sfoldl\<cdot>(op2\<cdot>pat)\<cdot>(root2\<cdot>pat)\<cdot>us)" \<comment>\<open> Note the use of @{term \<open>op2\<close>} and @{const \<open>next\<close>}. \<close>
| "right2\<cdot>pat\<cdot>(us, [::]) = Null" \<comment>\<open> Unreachable \<close>
| "\<lbrakk>v \<noteq> \<bottom>; vs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow>
   right2\<cdot>pat\<cdot>(us, v :# vs) = rep2\<cdot>pat\<cdot>(us :@ [:v:], vs)"

fixrec abs2 :: "([:'a:] \<times> [:'a:]) tree \<rightarrow> [:'a:] \<times> [:'a:]" where
 "usvs \<noteq> \<bottom> \<Longrightarrow> abs2\<cdot>(Node\<cdot>usvs\<cdot>l\<cdot>r) = usvs"

fixrec matches2 :: "[:'a::Eq_def:] \<rightarrow> [:'a:] \<rightarrow> [:Integer:]" where
[simp del]: "matches2\<cdot>pat = smap\<cdot>cfst oo sfilter\<cdot>(snull oo csnd oo abs2 oo csnd)
                                     oo sscanl\<cdot>(\<Lambda> (n, x) y. (n + 1, op2\<cdot>pat\<cdot>x\<cdot>y))\<cdot>(0, root2\<cdot>pat)"

text\<open>

\begin{figure}
  \centering
  \begin{tikzpicture}[
    shorten >=1pt,
    node distance=1.5cm,
    on grid,
    auto,
    initial text=,
    thick,
    accepting/.style = {rectangle,minimum size=0.3cm}
    ]
    \node[state,accepting] (q_0i)                     {};
    \node[state,initial]   (q_0)  [right=of q_0i]     {$q_0$};
    \node[state]           (q_1)  [right=of q_0]      {$q_1$};
    \node[state]           (q_2)  [right=of q_1]      {$q_2$};
    \node[state]           (q_3)  [right=of q_2]      {$q_3$};
    \node[state]           (q_4)  [right=of q_3]      {$q_4$};
    \node[state,double]    (q_5)  [right=of q_4]      {$q_5$};
    \node[state,accepting] (q_5r) [right=of q_5]      {};

    \path[->] (q_0) edge [bend left] node [above]       {0} (q_1)
              (q_1) edge [bend left] node [above]       {1} (q_2)
              (q_2) edge [bend left] node [above]       {0} (q_3)
              (q_3) edge [bend left] node [above]       {0} (q_4)
              (q_4) edge [bend left] node [above]       {1} (q_5)
              (q_5) edge [bend left] node [above]       {*} (q_5r);

    \path[->] (q_0) edge [bend right]               (q_0i)
              (q_1) edge [bend left]                (q_0)
              (q_2) edge [bend left]                (q_0)  % MP
              (q_2) edge [bend left,color=red]      (q_0i) % K opt
              (q_3) edge [bend left]                (q_1)
              (q_4) edge [bend left]                (q_1)  % MP
              (q_4) edge [bend left,color=red]      (q_0)  % K opt
              (q_5) edge [bend left]                (q_2);
  \end{tikzpicture}
  \caption{An example from @{cite [cite_macro=citet]
    \<open>\S2.1\<close> "CrochemoreRytter:2002"}. The MP tree for the
    pattern $01001$ is drawn in black: right transitions are labelled
    with a symbol, whereas left transitions are unlabelled. The two
    `K'-optimised left transitions are shown in red. The boxes denote
    @{const \<open>Null\<close>}. The root node is $q_0$.}
  \label{fig:example_tree}
\end{figure}

This tree can be interpreted as a sort of automaton\footnote{@{cite
[cite_macro=citet] \<open>\S3.1\<close> "Bird:2012"} suggests it can
be thought of as a doubly-linked list, following @{cite
[cite_macro=citet] "TakeichiAkama:1990"}.)}, where @{const
\<open>op2\<close>} goes @{const \<open>right\<close>} if the pattern
continues with the next element of the text, and @{const
\<open>left\<close>} otherwise, to determine how much of a prefix of
the pattern could still be in play.  Figure~\ref{fig:example_tree}
visualises such an automaton for the pattern $01001$, used by @{cite
[cite_macro=citet] \<open>\S2.1\<close> "CrochemoreRytter:2002"} to
illustrate the difference between Morris-Pratt (MP) and
Knuth-Morris-Pratt (KMP) preprocessing as we discuss below.  Note that
these are not the classical Mealy machines that correspond to regular
expressions, where all outgoing transitions are labelled with symbols.

The following lemma shows how our sample automaton is encoded as a non-wellfounded tree.

\<close>

lemma concrete_tree_KMP:
  shows "root2\<cdot>[:0::Integer, 1, 0, 0, 1:]
      = (\<mu> q0. Node\<cdot>([::], [:0, 1, 0, 0, 1:])
                     \<cdot>Null
                     \<cdot>(\<mu> q1. Node\<cdot>([:0:], [:1, 0, 0, 1:])
                          \<cdot>q0
                          \<cdot>(\<mu> q2. Node\<cdot>([:0,1:], [:0, 0, 1:])
                               \<cdot>Null \<comment>\<open> K optimisation: MP \<open>q0\<close> \<close>
                               \<cdot>(Node\<cdot>([:0,1,0:], [:0, 1:])
                                     \<cdot>q1
                                     \<cdot>(Node\<cdot>([:0,1,0,0:], [:1:])
                                          \<cdot>q0 \<comment>\<open> K optimisation: MP \<open>q1\<close> \<close>
                                          \<cdot>(Node\<cdot>([:0,1,0,0,1:], [::])\<cdot>q2\<cdot>Null))))))"
(is "?lhs = fix\<cdot>?F")
proof(rule tree_unique) \<^marker>\<open>tag invisible\<close>
  note rep2.simps[simp]
  show "?lhs = ?F\<cdot>?lhs"
    apply (subst root2.unfold; simp)
    apply (rule tree_unique; simp)
     apply (intro conjI)
      apply (subst (1) root2.unfold; simp)
      apply (subst (1) root2.unfold; fastforce)
     apply (rule tree_unique; simp)
      apply (intro conjI)
         apply (subst (1) root2.unfold; simp)
         apply (subst (1) root2.unfold; simp)
        apply (subst (1) root2.unfold; simp)
        apply (subst (1) root2.unfold; fastforce)
       apply (subst (1) root2.unfold; simp)
       apply (subst (1) root2.unfold; simp)
       apply (subst (1) root2.unfold; simp)
       apply (subst (1 2) root2.unfold; fastforce)
      apply (subst (1) root2.unfold; simp)
      apply (subst (1) root2.unfold; simp)
      apply (subst (1) root2.unfold; fastforce)
     apply (rename_tac i t u; case_tac i; clarsimp)
     apply (rename_tac t u i; case_tac i; clarsimp)
     apply (rename_tac t u i; case_tac i; clarsimp)
     apply (meson Suc_n_not_le_n linear tree_take_smaller)
    apply (rule parallel_fix_ind; simp)
    apply (rename_tac i t u x y; case_tac i; clarsimp)
    apply (rename_tac i; case_tac i; clarsimp; intro conjI)
     apply (meson Suc_n_not_le_n linear tree_take_smaller)
    apply (rename_tac i; case_tac i; clarsimp)
    apply (rename_tac i; case_tac i; clarsimp)
    apply (meson Suc_n_not_le_n linear tree_take_smaller)
    done
  fix i :: nat
  fix t u :: "([:Integer:] \<times> [:Integer:]) tree"
  assume "tree_take i\<cdot>t = tree_take i\<cdot>u"
  then show "tree_take (Suc i)\<cdot>(?F\<cdot>t) = tree_take (Suc i)\<cdot>(?F\<cdot>u)"
    apply simp
    apply (rule parallel_fix_ind; simp)
    apply (case_tac i; clarsimp; intro conjI)
     apply (meson Suc_n_not_le_n linear tree_take_smaller)
    apply (rule parallel_fix_ind; simp)
    apply (rename_tac j t0 t1; case_tac j; clarsimp)
    apply (rename_tac j; case_tac j; clarsimp; intro conjI)
     apply (meson Suc_n_not_le_n linear tree_take_smaller)
    apply (rename_tac j; case_tac j; clarsimp; intro conjI)
     apply (meson Suc_n_not_le_n linear tree_take_smaller)
    apply (rename_tac j; case_tac j; clarsimp)
    apply (meson Suc_n_not_le_n linear tree_take_smaller)
    done
qed

text\<open>

The sharing that we expect from a lazy (call-by-need) evaluator is here implied by the use of
nested fixed points.

The KMP preprocessor is expressed by the @{const \<open>left2\<close>} function, where @{const \<open>op2\<close>} is used
to match the pattern against itself; the use of @{const \<open>op2\<close>} in @{const \<open>matches2\<close>} (``the driver'')
is responsible for matching the (preprocessed) pattern against the text. This formally cashes in
an observation by @{cite [cite_macro=citet] \<open>\S5\<close> "vanderWoude:1989"}, that these two algorithms
are essentially the same, which has eluded other presentations\footnote{For instance, contrast
our shared use of @{const \<open>op2\<close>} with the separated \texttt{match}
and \texttt{rematch} functions of @{cite [cite_macro=citet] \<open>Figure~1\<close> "AgerDanvyRohde:2006"}.}.

Bird uses @{const \<open>Null\<close>} on a left path to signal to the driver that it should discard the
current element of the text and restart matching from the beginning of the pattern (i.e,
@{const \<open>root2\<close>}). This is a step towards the removal of @{term \<open>us\<close>} in \S\ref{sec:KMP:step8}.

Note that the @{const \<open>Null\<close>} at the end of the rightmost path is unreachable: the rightmost
@{const \<open>Node\<close>} has @{term "vs = [::]"} and therefore @{const \<open>op2\<close>} always takes the left branch.

The `K' optimisation is perhaps best understood by example. Consider
the automaton in Figure~\ref{fig:example_tree}, and a text beginning
with \texttt{011}. Using the MP (black) transitions we take the path
$\rightarrow q_0 \stackrel{{\mathtt{0}}}{\rightarrow} q_1
\stackrel{\mathtt{1}}{\rightarrow} \overbrace{q_2 \rightarrow q_0
\rightarrow \Box}$. Now, due to the failure of the comparison of the
current element of the text (\texttt{1}) at $q_2$, we can predict that
the (identical) comparison at node $q_0$ will fail as well, and
therefore have $q_2$ left-branch directly to $\Box$. This saves a
comparison in the driver at the cost of another in the preprocessor
(in @{const \<open>next\<close>}). These optimisations are the red
arrows in the diagram, and can in general save an arbitrary number of
driver comparisons; consider the pattern $\mathtt{1}^n$ for instance.

More formally, @{const \<open>next\<close>} ensures that the heads of
the suffixes of the pattern (@{term \<open>vs\<close>}) on consecutive
labels on left paths are distinct; see below for a proof of this fact
in our setting, and @{cite [cite_macro=citet] \<open>\S3.3.4\<close>
"Gusfield:1997"} for a classical account. Unlike Bird's suggestion
(p134), our @{const \<open>next\<close>} function is not recursive.

We note in passing that while MP only allows \<open>Null\<close> on
the left of the root node, \<open>Null\<close> can be on the left of
any KMP node except for the rightmost
(i.e., the one that signals a complete pattern match) where no optimisation is possible.

We proceed with the formalities of the data refinement.

\<close>

schematic_goal root2_op2_rep2_left2_right2_def: \<comment> \<open> Obtain the definition of these functions as a single fixed point \<close>
  "( root2  :: [:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , op2    :: [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> 'a \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , rep2   :: [:'a:] \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , left2  :: [:'a:] \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , right2 :: [:'a:] \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree )
   = fix\<cdot>?F"
unfolding op2_def root2_def rep2_def left2_def right2_def by simp

lemma abs2_strict[simp]:
  "abs2\<cdot>\<bottom> = \<bottom>"
  "abs2\<cdot>Null = \<bottom>"
by fixrec_simp+

lemma next_strict[simp]:
  "next\<cdot>\<bottom> = \<bottom>"
  "next\<cdot>xs\<cdot>\<bottom> = \<bottom>"
  "next\<cdot>(x :# xs)\<cdot>(Node\<cdot>(us, \<bottom>)\<cdot>l\<cdot>r) = \<bottom>"
  apply fixrec_simp
 apply (cases xs; fixrec_simp; simp)
apply (cases "x = \<bottom>"; cases "xs = \<bottom>"; cases "us = \<bottom>"; fixrec_simp)
done

lemma next_Null[simp]:
  assumes "xs \<noteq> \<bottom>"
shows "next\<cdot>xs\<cdot>Null = Null"
using assms by (cases xs) simp_all

lemma next_snil[simp]:
  assumes "xs \<noteq> \<bottom>"
  shows "next\<cdot>xs\<cdot>(Node\<cdot>(us, [::])\<cdot>l\<cdot>r) = Node\<cdot>(us, [::])\<cdot>l\<cdot>r"
using assms by (cases xs) simp_all

lemma op2_rep2_left2_right2_strict[simp]:
  "op2\<cdot>pat\<cdot>\<bottom> = \<bottom>"
  "op2\<cdot>pat\<cdot>(Node\<cdot>(us, \<bottom>)\<cdot>l\<cdot>r) = \<bottom>"
  "op2\<cdot>pat\<cdot>(Node\<cdot>usvs\<cdot>l\<cdot>r)\<cdot>\<bottom> = \<bottom>"
  "rep2\<cdot>pat\<cdot>\<bottom> = \<bottom>"
  "left2\<cdot>pat\<cdot>(\<bottom>, vs) = \<bottom>"
  "left2\<cdot>pat\<cdot>(us, \<bottom>) = \<bottom>"
  "right2\<cdot>pat\<cdot>(us, \<bottom>) = \<bottom>"
      apply fixrec_simp
     apply (cases "us = \<bottom>"; fixrec_simp; simp)
    apply (cases "usvs = \<bottom>"; fixrec_simp; simp)
   apply fixrec_simp
  apply fixrec_simp
 apply (cases us; fixrec_simp)
apply fixrec_simp
done

lemma snd_abs_root2_bottom[simp]: "prod.snd (abs2\<cdot>(root2\<cdot>\<bottom>)) = \<bottom>"
by (simp add: root2.unfold rep2.unfold)

lemma abs_rep2_ID'[simp]: "abs2\<cdot>(rep2\<cdot>pat\<cdot>usvs) = usvs"
by (cases "usvs = \<bottom>"; subst rep2.unfold; clarsimp)

lemma abs_rep2_ID: "abs2 oo rep2\<cdot>pat = ID"
by (clarsimp simp: cfun_eq_iff)

lemma rep2_snoc_right2: \<comment>\<open> Bird p131 \<close>
  assumes "prefix\<cdot>[:x:]\<cdot>vs = TT"
  shows "rep2\<cdot>pat\<cdot>(us :@ [:x:], stail\<cdot>vs) = right2\<cdot>pat\<cdot>(us, vs)"
using assms by (cases "x = \<bottom>"; cases vs; clarsimp)

lemma not_prefix_op2_next:
  assumes "prefix\<cdot>[:x:]\<cdot>xs = FF"
  shows "op2\<cdot>pat\<cdot>(next\<cdot>xs\<cdot>(rep2\<cdot>pat\<cdot>usvs))\<cdot>x = op2\<cdot>pat\<cdot>(rep2\<cdot>pat\<cdot>usvs)\<cdot>x"
proof -
  obtain us vs where "usvs = (us, vs)" by force
  with assms show ?thesis
    by (cases xs; cases us; clarsimp; cases vs;
        clarsimp simp: rep2.simps prefix_singleton_FF If2_def[symmetric] split: If2_splits)
qed

text\<open>

Bird's appeal to \<open>foldl_fusion\<close> (p130) is too weak to
justify this data refinement as his condition (iii) requires the
worker functions to coincide on all representation values. Concretely
he asks that:

\begin{center}
  @{prop "rep2\<cdot>pat\<cdot>(op\<cdot>pat\<cdot>(abs2\<cdot>t)\<cdot>x) = op2\<cdot>pat\<cdot>t\<cdot>x"} \<comment>\<open>Bird (17.2)\<close>
\end{center}

where \<open>t\<close> is an arbitrary tree. This does not hold for junk representations
such as:

\begin{center}
  @{term \<open>t = Node\<cdot>(pat, [::])\<cdot>Null\<cdot>Null\<close>}
\end{center}

Using worker/wrapper fusion @{cite [cite_macro=citep]
"GillHutton:2009" and "Gammie:2011"} specialised to @{const
\<open>sscanl\<close>} (@{thm [source] "sscanl_ww_fusion"}) we only
need to establish this identity for valid representations, i.e., when
\<open>t\<close> lies under the image of \<open>rep2\<close>. In
pictures, we show that this diagram commutes:

\begin{center}
  \begin{tikzcd}[column sep=8em]
    usvs \arrow[r, "\<open>\<Lambda> usvs. op\<cdot>pat\<cdot>usvs\<cdot>x\<close>"] \arrow[d, "\<open>rep2\<cdot>pat\<close>"] & usvs' \arrow[d, "\<open>rep2\<cdot>pat\<close>"] \\
    t \arrow[r, "\<open>\<Lambda> usvs. op2\<cdot>pat\<cdot>usvs\<cdot>x \<close>"]                         & t'
  \end{tikzcd}
\end{center}

Clearly this result self-composes: after an initial @{term
\<open>rep2\<cdot>pat\<close>} step, we can repeatedly simulate
@{const \<open>op\<close>} steps with @{const \<open>op2\<close>} steps.

\<close>

lemma op_op2_refinement:
  assumes "pat \<noteq> \<bottom>"
  shows "rep2\<cdot>pat\<cdot>(op\<cdot>pat\<cdot>usvs\<cdot>x) = op2\<cdot>pat\<cdot>(rep2\<cdot>pat\<cdot>usvs)\<cdot>x"
proof(cases "x = \<bottom>" "usvs = \<bottom>" rule: bool.exhaust[case_product bool.exhaust])
  case False_False
  then have "x \<noteq> \<bottom>" "usvs \<noteq> \<bottom>" by simp_all
  then show ?thesis
  proof(induct usvs arbitrary: x rule: op_induct)
    case (step usvs)
    obtain us vs where usvs: "usvs = (us, vs)" by fastforce
    have *: "sfoldl\<cdot>(op2\<cdot>pat)\<cdot>(root2\<cdot>pat)\<cdot>xs = rep2\<cdot>pat\<cdot>(split\<cdot>pat\<cdot>xs)" if "lt\<cdot>(slength\<cdot>xs)\<cdot>(slength\<cdot>us) = TT" for xs
    using that
    proof(induct xs rule: srev_induct)
      case (ssnoc x xs)
      from ssnoc(1,2,4) have IH: "sfoldl\<cdot>(op2\<cdot>pat)\<cdot>(root2\<cdot>pat)\<cdot>xs = rep2\<cdot>pat\<cdot>(split\<cdot>pat\<cdot>xs)"
        by - (rule ssnoc; auto intro: lt_trans dest: lt_slength_0)
      obtain us' vs' where us'vs': "split\<cdot>pat\<cdot>xs = (us', vs')" by fastforce
      from \<open>pat \<noteq> \<bottom>\<close> ssnoc(1,2,4) usvs show ?case
        apply (clarsimp simp: split_sfoldl_op[symmetric] IH)
        apply (rule step(1)[simplified abs_rep2_ID', simplified, symmetric])
        using lt_trans split_length_lt split_sfoldl_op apply fastforce+
        done
    qed (fastforce simp: \<open>pat \<noteq> \<bottom>\<close> root2.unfold)+
    have **: "If snull\<cdot>us then rep2\<cdot>pat\<cdot>([::], pat) else rep2\<cdot>pat\<cdot>(op\<cdot>pat\<cdot>(split\<cdot>pat\<cdot>(stail\<cdot>us))\<cdot>x)
            = op2\<cdot>pat\<cdot>(left2\<cdot>pat\<cdot>(us, vs))\<cdot>x" if "prefix\<cdot>[:x:]\<cdot>vs = FF"
    proof(cases us)
      case snil with that show ?thesis
        by simp (metis next_Null op2.simps(1) prefix.simps(1) prefix_FF_not_snilD root2.simps)
    next
      case (scons u' us')
      from \<open>pat \<noteq> \<bottom>\<close> scons have "lt\<cdot>(slength\<cdot>(cfst\<cdot>(split\<cdot>pat\<cdot>us')))\<cdot>(slength\<cdot>us) = TT"
        using split_length_lt by fastforce
      from \<open>pat \<noteq> \<bottom>\<close> \<open>x \<noteq> \<bottom>\<close> usvs that scons this show ?thesis
        by (clarsimp simp: * step(1)[simplified abs_rep2_ID'] not_prefix_op2_next)
    qed simp
    from \<open>usvs \<noteq> \<bottom>\<close> usvs show ?case
      apply (subst (2) rep2.unfold)
      apply (subst op2.unfold)
      apply (subst op.unfold)
      apply (clarsimp simp: If_distr rep2_snoc_right2 ** cong: If_cong)
      done
  qed
qed (simp_all add: rep2.unfold)

text\<open>

Therefore the result of this data refinement is extensionally equal to
the specification:

\<close>

lemma data_refinement:
  shows "matches = matches2"
proof(intro cfun_eqI)
  fix pat xs :: "[:'a:]" show "matches\<cdot>pat\<cdot>xs = matches2\<cdot>pat\<cdot>xs"
  proof(cases "pat = \<bottom>")
    case True then show ?thesis by (cases xs; clarsimp simp: matches2.simps)
  next
    case False then show ?thesis
      unfolding matches2.simps
      apply (subst matches_op) \<comment>\<open> Continue with previous derivation. \<close>
      apply (subst sscanl_ww_fusion[where wrap="ID ** abs2" and unwrap="ID ** rep2\<cdot>pat" and f'="\<Lambda> (n, x) y. (n + 1, op2\<cdot>pat\<cdot>x\<cdot>y)"])
        apply (simp add: abs_rep2_ID)
       apply (simp add: op_op2_refinement)
      apply (simp add: oo_assoc sfilter_smap root2.unfold)
      apply (simp add: oo_assoc[symmetric])
      done
  qed
qed

text\<open>

This computation can be thought of as a pair coroutines with a
producer (@{const \<open>root2\<close>}/@{const \<open>rep2\<close>})
/ consumer (@{const \<open>op2\<close>}) structure. It turns out that
laziness is not essential (see \S\ref{sec:implementations}), though it
does depend on being able to traverse incompletely defined trees.

The key difficulty in defining this computation in HOL using present
technology is that @{const \<open>op2\<close>} is neither terminating
nor @{emph \<open>friendly\<close>} in the terminology of @{cite [cite_macro=citet]
"BlanchetteEtAl:2017"}.

While this representation works for automata with this sort of
structure, it is unclear how general it is; in particular it may not
work so well if @{const \<open>left\<close>} branches can go forward
as well as back. See also the commentary in @{cite [cite_macro=citet]
"HinzeJeuring:2001"}, who observe that sharing is easily lost, and so
it is probably only useful in ``closed'' settings like the present
one, unless the language is extended in unusual ways @{cite
[cite_macro=citep] "JeanninEtAl:2017"}.

\label{thm:k_property}

We conclude by proving that @{const \<open>rep2\<close>} produces
trees that have the `K' property, viz that labels on consecutive nodes
on a left path do not start with the same symbol. This also
establishes the productivity of @{const \<open>root2\<close>}. The
pattern of proof used here -- induction nested in coinduction --
recurs in \S\ref{sec:KMP:increase_sharing}.

\<close>

coinductive K :: "([:'a::Eq:] \<times> [:'a:]) tree \<Rightarrow> bool" where
  "K Null"
| "\<lbrakk> usvs \<noteq> \<bottom>; K l; K r;
     \<And>v vs. csnd\<cdot>usvs = v :# vs \<Longrightarrow> l = Null \<or> (\<exists>v' vs'. csnd\<cdot>(label\<cdot>l) = v' :# vs' \<and> eq\<cdot>v\<cdot>v' = FF)
   \<rbrakk> \<Longrightarrow> K (Node\<cdot>usvs\<cdot>l\<cdot>r)"

declare K.intros[intro!, simp]

lemma sfoldl_op2_root2_rep2_split:
  assumes "pat \<noteq> \<bottom>"
  shows "sfoldl\<cdot>(op2\<cdot>pat)\<cdot>(root2\<cdot>pat)\<cdot>xs = rep2\<cdot>pat\<cdot>(split\<cdot>pat\<cdot>xs)"
proof(induct xs rule: srev_induct)
  case (ssnoc x xs) with \<open>pat \<noteq> \<bottom>\<close> ssnoc show ?case by (clarsimp simp: split_sfoldl_op[symmetric] op_op2_refinement)
qed (simp_all add: \<open>pat \<noteq> \<bottom>\<close> root2.unfold)

lemma K_rep2:
  assumes "pat \<noteq> \<bottom>"
  assumes "us :@ vs = pat"
  shows "K (rep2\<cdot>pat\<cdot>(us, vs))"
using assms
proof(coinduction arbitrary: us vs)
  case (K us vs) then show ?case
  proof(induct us arbitrary: vs rule: op_induct')
    case (step us)
    from step.prems have "us \<noteq> \<bottom>" "vs \<noteq> \<bottom>" by auto
    show ?case
    proof(cases us)
      case bottom with \<open>us \<noteq> \<bottom>\<close> show ?thesis by simp
    next
      case snil with step.prems show ?thesis by (cases vs; force simp: rep2.simps)
    next
      case (scons u' us')
      from \<open>pat \<noteq> \<bottom>\<close> scons \<open>us \<noteq> \<bottom>\<close> \<open>vs \<noteq> \<bottom>\<close>
      obtain usl vsl where splitl: "split\<cdot>pat\<cdot>us' = (usl, vsl)" "usl \<noteq> \<bottom>" "vsl \<noteq> \<bottom>" "usl :@ vsl = pat"
        by (metis (no_types, hide_lams) Rep_cfun_strict1 prod.collapse sappend_strict sappend_strict2 split_pattern)
      from scons obtain l r where r: "rep2\<cdot>pat\<cdot>(us, vs) = Node\<cdot>(us, vs)\<cdot>l\<cdot>r" by (simp add: rep2.simps)
      moreover
      have "(\<exists>us vs. l = rep2\<cdot>pat\<cdot>(us, vs) \<and> us :@ vs = pat) \<or> K l"
      proof(cases vs)
        case snil with scons splitl r show ?thesis
          by (clarsimp simp: rep2.simps sfoldl_op2_root2_rep2_split)
      next
        case scons
        with \<open>pat \<noteq> \<bottom>\<close> \<open>us = u' :# us'\<close> \<open>u' \<noteq> \<bottom>\<close> \<open>us' \<noteq> \<bottom>\<close> \<open>vs \<noteq> \<bottom>\<close> r splitl show ?thesis
          apply (clarsimp simp: rep2.simps sfoldl_op2_root2_rep2_split)
          apply (cases vsl; cases usl; clarsimp simp: If2_def[symmetric] sfoldl_op2_root2_rep2_split split: If2_splits)
          apply (rename_tac ul' usl')
          apply (cut_tac us'="prod.fst (split\<cdot>pat\<cdot>usl')" and vs="prod.snd (split\<cdot>pat\<cdot>usl')" in step(1); clarsimp simp: split_pattern)
           apply (metis fst_conv lt_trans slength.simps(2) split_length_lt step.prems(1))
          apply (erule disjE; clarsimp simp: sfoldl_op2_root2_rep2_split)
          apply (rename_tac b l r)
          apply (case_tac b; clarsimp simp: rep2.simps)
           apply (auto simp: If2_def[symmetric] rep2.simps dest: split_pattern[rotated] split: If2_splits)
          done
      qed (simp add: \<open>vs \<noteq> \<bottom>\<close>)
      moreover
      from \<open>us :@ vs = pat\<close> \<open>us \<noteq> \<bottom>\<close> \<open>vs \<noteq> \<bottom>\<close> r
      have "(\<exists>usr vsr. r = rep2\<cdot>pat\<cdot>(usr, vsr) \<and> usr :@ vsr = pat) \<or> K r"
        by (cases vs; clarsimp simp: rep2.simps)
      moreover
      have "l = Null \<or> (\<exists>v' vs'. csnd\<cdot>(label\<cdot>l) = v' :# vs' \<and> eq\<cdot>v\<cdot>v' = FF)" if "vs = v :# vs'" for v vs'
      proof(cases vsl)
        case snil with \<open>us :@ vs = pat\<close> \<open>us = u' :# us'\<close> splitl show ?thesis
          using split_length_lt[where pat=pat and xs=us']
          by (force elim: slengthE simp: one_Integer_def split: if_splits)
      next
        case scons
        from splitl have "lt\<cdot>(slength\<cdot>usl)\<cdot>(slength\<cdot>us' + 1) = TT"
          by (metis fst_conv fst_strict split_bottom_iff split_length_lt)
        with scons \<open>pat \<noteq> \<bottom>\<close> \<open>us = u' :# us'\<close> \<open>u' \<noteq> \<bottom>\<close> \<open>us' \<noteq> \<bottom>\<close> \<open>vs \<noteq> \<bottom>\<close> r splitl \<open>vs = v :# vs'\<close> show ?thesis
          using step(1)[OF _ \<open>pat \<noteq> \<bottom>\<close>, where us'="prod.fst (split\<cdot>pat\<cdot>us')" and vs="prod.snd (split\<cdot>pat\<cdot>us')"]
          by (clarsimp simp: rep2.simps sfoldl_op2_root2_rep2_split If2_def[symmetric] split: If2_splits)
      qed (simp add: \<open>vsl \<noteq> \<bottom>\<close>)
      moreover note \<open>pat \<noteq> \<bottom>\<close> \<open>us \<noteq> \<bottom>\<close> \<open>vs \<noteq> \<bottom>\<close>
      ultimately show ?thesis by auto
    qed
  qed
qed

theorem K_root2:
  assumes "pat \<noteq> \<bottom>"
  shows "K (root2\<cdot>pat)"
using assms unfolding root2.unfold by (simp add: K_rep2)

text\<open>

The remaining steps are as follows:

\<^item> 3. introduce an accumulating parameter (\<open>grep\<close>).
\<^item> 4. inline \<open>rep\<close> and simplify.
\<^item> 5. simplify to Bird's ``simpler forms.''
\<^item> 6. memoise \<open>left\<close>.
\<^item> 7. simplify, unfold \<open>prefix\<close>.
\<^item> 8. discard \<open>us\<close>.
\<^item> 9. factor out \<open>pat\<close>.

\<close>


subsection\<open> Step 3: Introduce an accumulating parameter (grep) \<close>

text\<open>

Next we prepare for the second memoization step (\S\ref{sec:KMP:increase_sharing})
by introducing an accumulating parameter to @{const \<open>rep2\<close>} that supplies the value of the left
subtree.

We retain @{const \<open>rep2\<close>} as a wrapper for now, and inline @{const \<open>right2\<close>} to speed up
simplification.

\<close>

fixrec \<comment>\<open> Bird p131 / p132 \<close>
    root3  :: "[:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree"
and op3    :: "[:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> 'a \<rightarrow> ([:'a:] \<times> [:'a:]) tree"
and rep3   :: "[:'a:] \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree"
and grep3  :: "[:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree"
where
  [simp del]:
  "root3\<cdot>pat = rep3\<cdot>pat\<cdot>([::], pat)"
| "op3\<cdot>pat\<cdot>Null\<cdot>x = root3\<cdot>pat"
| "usvs \<noteq> \<bottom> \<Longrightarrow>
   op3\<cdot>pat\<cdot>(Node\<cdot>usvs\<cdot>l\<cdot>r)\<cdot>x = If prefix\<cdot>[:x:]\<cdot>(csnd\<cdot>usvs) then r else op3\<cdot>pat\<cdot>l\<cdot>x"
| [simp del]: \<comment>\<open> Inline @{const \<open>left2\<close>}, factor out @{const \<open>next\<close>}. \<close>
  "rep3\<cdot>pat\<cdot>usvs = grep3\<cdot>pat\<cdot>(case cfst\<cdot>usvs of [::] \<Rightarrow> Null | u :# us \<Rightarrow> sfoldl\<cdot>(op3\<cdot>pat)\<cdot>(root3\<cdot>pat)\<cdot>us)\<cdot>usvs"
| [simp del]:  \<comment>\<open> @{const \<open>rep2\<close>} with @{const \<open>left2\<close>} abstracted, @{const \<open>right2\<close>} inlined. \<close>
  "grep3\<cdot>pat\<cdot>l\<cdot>usvs = Node\<cdot>usvs\<cdot>(next\<cdot>(csnd\<cdot>usvs)\<cdot>l)\<cdot>(case csnd\<cdot>usvs of
          [::] \<Rightarrow> Null
        | v :# vs \<Rightarrow> rep3\<cdot>pat\<cdot>(cfst\<cdot>usvs :@ [:v:], vs))"

schematic_goal root3_op3_rep3_grep3_def:
  "( root3  :: [:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , op3    :: [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> 'a \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , rep3   :: [:'a:] \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , grep3  :: [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree )
   = fix\<cdot>?F"
unfolding root3_def op3_def rep3_def grep3_def by simp

lemma r3_2:
  "(\<Lambda> (root, op, rep, grep). (root, op, rep))\<cdot>
   ( root3  :: [:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , op3    :: [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> 'a \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , rep3   :: [:'a:] \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , grep3  :: [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree )
 = (\<Lambda> (root, op, rep, left, right). (root, op, rep))\<cdot>
   ( root2  :: [:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , op2    :: [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> 'a \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , rep2   :: [:'a::Eq_def:] \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , left2  :: [:'a::Eq_def:] \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , right2 :: [:'a::Eq_def:] \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree )"
unfolding root2_op2_rep2_left2_right2_def root3_op3_rep3_grep3_def
apply (simp add: match_snil_match_scons_slist_case match_Null_match_Node_tree_case slist_case_distr tree_case_distr)
apply (simp add: fix_cprod fix_const) \<comment>\<open> Very slow. Sensitive to tuple order due to the asymmetry of \<open>fix_cprod\<close>. \<close>
apply (simp add: slist_case_distr)
done


subsection\<open> Step 4: Inline rep \<close>

text\<open>

We further simplify by inlining @{const \<open>rep3\<close>} into @{const \<open>root3\<close>} and @{const \<open>grep3\<close>}.

\<close>

fixrec
    root4  :: "[:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree"
and op4    :: "[:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> 'a \<rightarrow> ([:'a:] \<times> [:'a:]) tree"
and grep4  :: "[:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree"
where
  [simp del]:
  "root4\<cdot>pat = grep4\<cdot>pat\<cdot>Null\<cdot>([::], pat)"
| "op4\<cdot>pat\<cdot>Null\<cdot>x = root4\<cdot>pat"
| "usvs \<noteq> \<bottom> \<Longrightarrow>
   op4\<cdot>pat\<cdot>(Node\<cdot>usvs\<cdot>l\<cdot>r)\<cdot>x = If prefix\<cdot>[:x:]\<cdot>(csnd\<cdot>usvs) then r else op4\<cdot>pat\<cdot>l\<cdot>x"
| [simp del]:
  "grep4\<cdot>pat\<cdot>l\<cdot>usvs = Node\<cdot>usvs\<cdot>(next\<cdot>(csnd\<cdot>usvs)\<cdot>l)\<cdot>(case csnd\<cdot>usvs of
          [::] \<Rightarrow> Null
        | v :# vs \<Rightarrow> grep4\<cdot>pat\<cdot>(case cfst\<cdot>usvs :@ [:v:] of
              [::] \<Rightarrow> Null \<comment>\<open> unreachable \<close>
            | u :# us \<Rightarrow> sfoldl\<cdot>(op4\<cdot>pat)\<cdot>(root4\<cdot>pat)\<cdot>us)\<cdot>(cfst\<cdot>usvs :@ [:v:], vs))"

schematic_goal root4_op4_grep4_def:
  "( root4  :: [:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , op4    :: [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> 'a \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , grep4  :: [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree )
   = fix\<cdot>?F"
unfolding root4_def op4_def grep4_def by simp

lemma fix_syn4_permute:
  assumes "cont (\<lambda>(X1, X2, X3, X4). F1 X1 X2 X3 X4)"
  assumes "cont (\<lambda>(X1, X2, X3, X4). F2 X1 X2 X3 X4)"
  assumes "cont (\<lambda>(X1, X2, X3, X4). F3 X1 X2 X3 X4)"
  assumes "cont (\<lambda>(X1, X2, X3, X4). F4 X1 X2 X3 X4)"
  shows "fix_syn (\<lambda>(X1, X2, X3, X4). (F1 X1 X2 X3 X4, F2 X1 X2 X3 X4, F3 X1 X2 X3 X4, F4 X1 X2 X3 X4))
      = (\<lambda>(x1, x2, x4, x3). (x1, x2, x3, x4))
            (fix_syn (\<lambda>(X1, X2, X4, X3). (F1 X1 X2 X3 X4, F2 X1 X2 X3 X4, F4 X1 X2 X3 X4, F3 X1 X2 X3 X4)))"
by (induct rule: parallel_fix_ind) (use assms in \<open>auto simp: prod_cont_iff\<close>)

lemma r4_3:
  "( root4  :: [:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , op4    :: [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> 'a \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , grep4  :: [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree )
 = (\<Lambda> (root, op, rep, grep). (root, op, grep))\<cdot>
   ( root3  :: [:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , op3    :: [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> 'a \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , rep3   :: [:'a:] \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , grep3  :: [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree )"
unfolding root3_op3_rep3_grep3_def root4_op4_grep4_def
apply (clarsimp simp: slist_case_distr match_Null_match_Node_tree_case tree_case_distr eta_cfun)
apply (subst fix_syn4_permute; clarsimp simp: fix_cprod fix_const) \<comment>\<open> Slow \<close>
done


subsection\<open> Step 5: Simplify to Bird's ``simpler forms'' \<close>

text\<open>

The remainder of @{const \<open>left2\<close>} in @{const \<open>grep4\<close>} can be simplified by transforming the
@{text "case"} scrutinee from @{term "cfst\<cdot>usvs :@ [:v:]"} into @{term "cfst\<cdot>usvs"}.

\<close>

fixrec
    root5  :: "[:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree"
and op5    :: "[:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> 'a \<rightarrow> ([:'a:] \<times> [:'a:]) tree"
and grep5  :: "[:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree"
where
  [simp del]:
  "root5\<cdot>pat = grep5\<cdot>pat\<cdot>Null\<cdot>([::], pat)"
| "op5\<cdot>pat\<cdot>Null\<cdot>x = root5\<cdot>pat"
| "usvs \<noteq> \<bottom> \<Longrightarrow>
   op5\<cdot>pat\<cdot>(Node\<cdot>usvs\<cdot>l\<cdot>r)\<cdot>x = If prefix\<cdot>[:x:]\<cdot>(csnd\<cdot>usvs) then r else op5\<cdot>pat\<cdot>l\<cdot>x"
| [simp del]:
  "grep5\<cdot>pat\<cdot>l\<cdot>usvs = Node\<cdot>usvs\<cdot>(next\<cdot>(csnd\<cdot>usvs)\<cdot>l)\<cdot>(case csnd\<cdot>usvs of
          [::] \<Rightarrow> Null
        | v :# vs \<Rightarrow> grep5\<cdot>pat\<cdot>(case cfst\<cdot>usvs of \<comment> \<open> was @{term \<open>cfst\<cdot>usvs :@ [:v:]\<close>} \<close>
              [::] \<Rightarrow> root5\<cdot>pat
            | u :# us \<Rightarrow> sfoldl\<cdot>(op5\<cdot>pat)\<cdot>(root5\<cdot>pat)\<cdot>(us :@ [:v:]))\<cdot>(cfst\<cdot>usvs :@ [:v:], vs))"

schematic_goal root5_op5_grep5_def:
  "( root5  :: [:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , op5    :: [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> 'a \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , grep5  :: [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree )
   = fix\<cdot>?F"
unfolding root5_def op5_def grep5_def by simp

lemma op5_grep5_strict[simp]:
  "op5\<cdot>pat\<cdot>\<bottom> = \<bottom>"
  "op5\<cdot>pat\<cdot>(Node\<cdot>(us, \<bottom>)\<cdot>l\<cdot>r) = \<bottom>"
  "op5\<cdot>pat\<cdot>(Node\<cdot>usvs\<cdot>l\<cdot>r)\<cdot>\<bottom> = \<bottom>"
  "grep5\<cdot>pat\<cdot>l\<cdot>\<bottom> = \<bottom>"
   apply fixrec_simp
  apply (cases "us = \<bottom>"; fixrec_simp; simp)
 apply (cases "usvs = \<bottom>"; fixrec_simp; simp)
apply fixrec_simp
done

lemma r5_4:
  "( root5  :: [:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , op5    :: [:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> 'a \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , grep5  :: [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree )
 = ( root4  :: [:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , op4    :: [:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> 'a \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , grep4  :: [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree )"
unfolding root4_op4_grep4_def root5_op5_grep5_def
by (clarsimp simp: slist_case_distr slist_case_snoc stail_sappend cong: slist_case_cong)


subsection\<open> Step 6: Memoize left \label{sec:KMP:increase_sharing} \<close>

text\<open>

The last substantial step is to memoise the computation of the left subtrees by tying the knot.

Note this makes the computation of \<open>us\<close> in the tree redundant; we remove it in \S\ref{sec:KMP:step8}.

\<close>

fixrec \<comment>\<open> Bird p132 \<close>
    root6  :: "[:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree"
and op6    :: "[:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> 'a \<rightarrow> ([:'a:] \<times> [:'a:]) tree"
and grep6  :: "[:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree"
where
  [simp del]:
  "root6\<cdot>pat = grep6\<cdot>pat\<cdot>Null\<cdot>([::], pat)"
| "op6\<cdot>pat\<cdot>Null\<cdot>x = root6\<cdot>pat"
| "usvs \<noteq> \<bottom> \<Longrightarrow>
   op6\<cdot>pat\<cdot>(Node\<cdot>usvs\<cdot>l\<cdot>r)\<cdot>x = If prefix\<cdot>[:x:]\<cdot>(csnd\<cdot>usvs) then r else op6\<cdot>pat\<cdot>l\<cdot>x"
| [simp del]:
  "grep6\<cdot>pat\<cdot>l\<cdot>usvs = Node\<cdot>usvs\<cdot>(next\<cdot>(csnd\<cdot>usvs)\<cdot>l)\<cdot>(case csnd\<cdot>usvs of
          [::] \<Rightarrow> Null
        | v :# vs \<Rightarrow> grep6\<cdot>pat\<cdot>(op6\<cdot>pat\<cdot>l\<cdot>v)\<cdot>(cfst\<cdot>usvs :@ [:v:], vs))"

schematic_goal root6_op6_grep6_def:
  "( root6  :: [:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , op6    :: [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> 'a \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , grep6  :: [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree )
   = fix\<cdot>?F"
unfolding root6_def op6_def grep6_def by simp

lemma op6_grep6_strict[simp]:
  "op6\<cdot>pat\<cdot>\<bottom> = \<bottom>"
  "op6\<cdot>pat\<cdot>(Node\<cdot>(us, \<bottom>)\<cdot>l\<cdot>r) = \<bottom>"
  "op6\<cdot>pat\<cdot>(Node\<cdot>usvs\<cdot>l\<cdot>r)\<cdot>\<bottom> = \<bottom>"
  "grep6\<cdot>pat\<cdot>l\<cdot>\<bottom> = \<bottom>"
   apply fixrec_simp
  apply (cases "us = \<bottom>"; fixrec_simp; simp)
 apply (cases "usvs = \<bottom>"; fixrec_simp; simp)
apply fixrec_simp
done

text\<open>

Intuitively this step cashes in the fact that, in the context of
@{term \<open>grep6\<cdot>pat\<cdot>l\<cdot>usvs\<close>}, @{term
"sfoldl\<cdot>(op6\<cdot>pat)\<cdot>(root6\<cdot>pat)\<cdot>us"} is
equal to @{term \<open>l\<close>}.

Connecting this step with the previous one is not simply a matter of
equational reasoning; we can see this by observing that the right
subtree of @{term \<open>grep5\<cdot>pat\<cdot>l\<cdot>usvs\<close>}
does not depend on @{term \<open>l\<close>} whereas that of @{term
\<open>grep6\<cdot>pat\<cdot>l\<cdot>usvs\<close>} does, and therefore
these cannot be extensionally equal. Furthermore the computations of
the corresponding @{term \<open>root\<close>}s do not proceed in
lockstep: consider the computation of the left subtree.

For our purposes it is enough to show that the trees @{const
\<open>root5\<close>} and @{const \<open>root6\<close>} are equal,
from which it follows that @{prop "op6 = op5"} by induction on its
tree argument. The equality is established by exhibiting a @{emph
\<open>tree bisimulation\<close>} (@{const tree_bisim}) that relates
the corresponding ``producer'' \<open>grep\<close> functions. Such a
relation \<open>R\<close> must satisfy:

\<^item> \<open>R \<bottom> \<bottom>\<close>;
\<^item> \<open>R Null Null\<close>; and
\<^item> if \<open>R (Node\<cdot>x\<cdot>l\<cdot>r) (Node\<cdot>x'\<cdot>l'\<cdot>r')\<close> then \<open>x = x'\<close>, \<open>R l l'\<close>, and \<open>R r r'\<close>.

\<close>
text\<open>

The following pair of \<open>left\<close> functions define suitable left
paths from the corresponding @{term \<open>root\<close>}s.

\<close>

fixrec left5 :: "[:'a::Eq_def:] \<rightarrow> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree" where
  "left5\<cdot>pat\<cdot>[::] = Null"
| "\<lbrakk>u \<noteq> \<bottom>; us \<noteq> \<bottom>\<rbrakk> \<Longrightarrow>
   left5\<cdot>pat\<cdot>(u :# us) = sfoldl\<cdot>(op5\<cdot>pat)\<cdot>(root5\<cdot>pat)\<cdot>us"

fixrec left6 :: "[:'a::Eq_def:] \<rightarrow> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree" where
  "left6\<cdot>pat\<cdot>[::] = Null"
| "\<lbrakk>u \<noteq> \<bottom>; us \<noteq> \<bottom>\<rbrakk> \<Longrightarrow>
   left6\<cdot>pat\<cdot>(u :# us) = sfoldl\<cdot>(op6\<cdot>pat)\<cdot>(root6\<cdot>pat)\<cdot>us"

inductive \<comment>\<open> This relation is not inductive. \<close>
  root_bisim :: "[:'a::Eq_def:] \<Rightarrow> ([:'a:] \<times> [:'a:]) tree \<Rightarrow> ([:'a:] \<times> [:'a:]) tree \<Rightarrow> bool"
  for pat :: "[:'a:]"
where
  bottom: "root_bisim pat \<bottom> \<bottom>"
| Null: "root_bisim pat Null Null"
| gl: "\<lbrakk>pat \<noteq> \<bottom>; us \<noteq> \<bottom>; vs \<noteq> \<bottom>\<rbrakk>
   \<Longrightarrow> root_bisim pat (grep6\<cdot>pat\<cdot>(left6\<cdot>pat\<cdot>us)\<cdot>(us, vs)) (grep5\<cdot>pat\<cdot>(left5\<cdot>pat\<cdot>us)\<cdot>(us, vs))"

declare root_bisim.intros[intro!, simp]

lemma left6_left5_strict[simp]:
  "left6\<cdot>pat\<cdot>\<bottom> = \<bottom>"
  "left5\<cdot>pat\<cdot>\<bottom> = \<bottom>"
by fixrec_simp+

lemma op6_left6: "\<lbrakk>us \<noteq> \<bottom>; v \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> op6\<cdot>pat\<cdot>(left6\<cdot>pat\<cdot>us)\<cdot>v = left6\<cdot>pat\<cdot>(us :@ [:v:])"
by (cases us) simp_all

lemma op5_left5: "\<lbrakk>us \<noteq> \<bottom>; v \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> op5\<cdot>pat\<cdot>(left5\<cdot>pat\<cdot>us)\<cdot>v = left5\<cdot>pat\<cdot>(us :@ [:v:])"
by (cases us) simp_all

lemma root5_left5: "v \<noteq> \<bottom> \<Longrightarrow> root5\<cdot>pat = left5\<cdot>pat\<cdot>[:v:]"
by simp

lemma op5_sfoldl_left5: "\<lbrakk>us \<noteq> \<bottom>; u \<noteq> \<bottom>; v \<noteq> \<bottom>\<rbrakk> \<Longrightarrow>
                 op5\<cdot>pat\<cdot>(sfoldl\<cdot>(op5\<cdot>pat)\<cdot>(root5\<cdot>pat)\<cdot>us)\<cdot>v = left5\<cdot>pat\<cdot>(u :# us :@ [:v:])"
by simp

lemma root_bisim_root:
  assumes "pat \<noteq> \<bottom>"
  shows "root_bisim pat (root6\<cdot>pat) (root5\<cdot>pat)"
unfolding root6.unfold root5.unfold using assms
by simp (metis (no_types, lifting) left5.simps(1) left6.simps(1) root_bisim.simps slist.con_rews(3))

lemma next_grep6_cases[consumes 3, case_names gl nl]:
  assumes "vs \<noteq> \<bottom>"
  assumes "xs \<noteq> \<bottom>"
  assumes "P (next\<cdot>xs\<cdot>(grep6\<cdot>pat\<cdot>(left6\<cdot>pat\<cdot>us)\<cdot>(us, vs)))"
  obtains (gl) "P (grep6\<cdot>pat\<cdot>(left6\<cdot>pat\<cdot>us)\<cdot>(us, vs))" | (nl) "P (next\<cdot>vs\<cdot>(left6\<cdot>pat\<cdot>us))"
using assms
apply atomize_elim
apply (subst grep6.unfold)
apply (subst (asm) grep6.unfold)
apply (cases xs; clarsimp)
apply (cases vs; clarsimp simp: If2_def[symmetric] split: If2_splits)
done

lemma root_bisim_op_next56:
  assumes "root_bisim pat t6 t5"
  assumes "prefix\<cdot>[:x:]\<cdot>xs = FF"
  shows "op6\<cdot>pat\<cdot>(next\<cdot>xs\<cdot>t6)\<cdot>x = op6\<cdot>pat\<cdot>t6\<cdot>x \<and> op5\<cdot>pat\<cdot>(next\<cdot>xs\<cdot>t5)\<cdot>x = op5\<cdot>pat\<cdot>t5\<cdot>x"
using \<open>root_bisim pat t6 t5\<close>
proof cases
  case Null with assms(2) show ?thesis by (cases xs) simp_all
next
  case (gl us vs) with assms(2) show ?thesis
    apply (cases "x = \<bottom>", simp)
    apply (cases xs; clarsimp)
    apply (subst (1 2) grep6.simps)
    apply (subst (1 2) grep5.simps)
    apply (cases vs; clarsimp simp: If2_def[symmetric] split: If2_splits)
    done
qed simp

text\<open>

The main part of establishing that @{const \<open>root_bisim\<close>}
is a @{const \<open>tree_bisim\<close>} is in showing that the left
paths constructed by the \<open>grep\<close>s are @{const
\<open>root_bisim\<close>}-related. We do this by inducting over the
length of the pattern so far matched (\<open>us\<close>), as we did
when proving that this tree has the `K' property in
\S\ref{thm:k_property}.

\<close>

lemma
  assumes "pat \<noteq> \<bottom>"
  shows root_bisim_op: "root_bisim pat t6 t5 \<Longrightarrow> root_bisim pat (op6\<cdot>pat\<cdot>t6\<cdot>x) (op5\<cdot>pat\<cdot>t5\<cdot>x)" \<comment> \<open> unused \<close>
    and root_bisim_next_left: "root_bisim pat (next\<cdot>vs\<cdot>(left6\<cdot>pat\<cdot>us)) (next\<cdot>vs\<cdot>(left5\<cdot>pat\<cdot>us))" (is "?rbnl us vs")
proof -
  let ?ogl5 = "\<lambda>us vs. op5\<cdot>pat\<cdot>(grep5\<cdot>pat\<cdot>(left5\<cdot>pat\<cdot>us)\<cdot>(us, vs))\<cdot>x"
  let ?ogl6 = "\<lambda>us vs. op6\<cdot>pat\<cdot>(grep6\<cdot>pat\<cdot>(left6\<cdot>pat\<cdot>us)\<cdot>(us, vs))\<cdot>x"
  let ?for5 = "\<lambda>us. sfoldl\<cdot>(op5\<cdot>pat)\<cdot>(root5\<cdot>pat)\<cdot>us"
  let ?for6 = "\<lambda>us. sfoldl\<cdot>(op6\<cdot>pat)\<cdot>(root6\<cdot>pat)\<cdot>us"
  have "\<lbrakk>?ogl6 us vs = Node\<cdot>usvs\<cdot>l\<cdot>r; cfst\<cdot>usvs \<noteq> \<bottom>; x \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> le\<cdot>(slength\<cdot>(cfst\<cdot>usvs))\<cdot>(slength\<cdot>us + 1) = TT"
   and "\<lbrakk>op6\<cdot>pat\<cdot>(next\<cdot>xs\<cdot>(grep6\<cdot>pat\<cdot>(left6\<cdot>pat\<cdot>us)\<cdot>(us, vs)))\<cdot>x = Node\<cdot>usvs\<cdot>l\<cdot>r; cfst\<cdot>usvs \<noteq> \<bottom>; x \<noteq> \<bottom>; us \<noteq> \<bottom>; vs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> le\<cdot>(slength\<cdot>(cfst\<cdot>usvs))\<cdot>(slength\<cdot>us + 1) = TT"
   and "\<lbrakk>?for6 us = Node\<cdot>usvs\<cdot>l\<cdot>r; cfst\<cdot>usvs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> lt\<cdot>(slength\<cdot>(cfst\<cdot>usvs))\<cdot>(slength\<cdot>us + 1) = TT"
   and "\<lbrakk>us \<noteq> \<bottom>; vs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> root_bisim pat (?ogl6 us vs) (?ogl5 us vs)"
   and "root_bisim pat (?for6 us) (?for5 us)"
   and "?rbnl us vs"
   for usvs l r xs us vs
  proof(induct us arbitrary: usvs l r vs x xs rule: op_induct')
    case (step us)
    have rbl: "root_bisim pat (left6\<cdot>pat\<cdot>us) (left5\<cdot>pat\<cdot>us)"
      by (cases us; fastforce intro: step(5) simp: left6.unfold left5.unfold)
    { case (1 usvs l r vs x)
      from rbl
      have L: "le\<cdot>(slength\<cdot>(prod.fst usvs'))\<cdot>(slength\<cdot>us + 1) = TT"
          if "op6\<cdot>pat\<cdot>(next\<cdot>vs\<cdot>(left6\<cdot>pat\<cdot>us))\<cdot>x = Node\<cdot>usvs'\<cdot>l\<cdot>r"
         and "cfst\<cdot>usvs' \<noteq> \<bottom>"
         and "vs \<noteq> \<bottom>"
         for usvs' l r
      proof cases
        case bottom with that show ?thesis by simp
      next
        case Null with that show ?thesis
          apply simp
          apply (subst (asm) root6.unfold)
          apply (subst (asm) grep6.unfold)
          apply (fastforce intro: le_plus_1)
          done
      next
        case (gl us'' vs'') show ?thesis
        proof(cases us)
          case bottom with that show ?thesis by simp
        next
          case snil with that show ?thesis
            apply simp
            apply (subst (asm) root6.unfold)
            apply (subst (asm) grep6.unfold)
            apply clarsimp
            done
        next
          case (scons ush ust)
          moreover from that gl scons \<open>x \<noteq> \<bottom>\<close> have "le\<cdot>(slength\<cdot>(cfst\<cdot>usvs'))\<cdot>(slength\<cdot>us'' + 1) = TT"
            apply simp
            apply (subst (asm) (2) grep6.unfold)
            apply (fastforce dest: step(2, 3)[rotated])
            done
          moreover from gl scons have "lt\<cdot>(slength\<cdot>us'')\<cdot>(slength\<cdot>(stail\<cdot>us) + 1) = TT"
            apply simp
            apply (subst (asm) grep6.unfold)
            apply (fastforce dest: step(3)[rotated])
            done
          ultimately show ?thesis
            apply clarsimp
            apply (metis Integer_le_both_plus_1 Ord_linear_class.le_trans le_iff_lt_or_eq)
            done
        qed
      qed
      from 1 show ?case
        apply (subst (asm) grep6.unfold)
        apply (cases vs; clarsimp simp: If2_def[symmetric] split: If2_splits)
          apply (rule L; fastforce)
         apply (metis (no_types, lifting) ab_semigroup_add_class.add_ac(1) fst_conv grep6.simps le_refl_Integer sappend_snil_id_right slength.simps(2) slength_bottom_iff slength_sappend slist.con_rews(3) tree_injects')
        apply (rule L; fastforce)
        done }
    note slength_ogl = this
    { case (2 usvs l r vs x xs)
      from 2 have "xs \<noteq> \<bottom>" by clarsimp
      from \<open>vs \<noteq> \<bottom>\<close> \<open>xs \<noteq> \<bottom>\<close> 2(1) show ?case
      proof(cases rule: next_grep6_cases)
        case gl with \<open>cfst\<cdot>usvs \<noteq> \<bottom>\<close> \<open>x \<noteq> \<bottom>\<close> show ?thesis using slength_ogl by blast
      next
        case nl
        from rbl show ?thesis
        proof cases
          case bottom with nl \<open>cfst\<cdot>usvs \<noteq> \<bottom>\<close> show ?thesis by simp
        next
          case Null with nl \<open>us \<noteq> \<bottom>\<close> \<open>vs \<noteq> \<bottom>\<close> show ?thesis
            apply simp
            apply (subst (asm) root6.unfold)
            apply (subst (asm) grep6.unfold)
            apply (clarsimp simp: zero_Integer_def one_Integer_def elim!: slengthE)
            done
        next
          case (gl us'' vs'') show ?thesis
          proof(cases us)
            case bottom with \<open>us \<noteq> \<bottom>\<close> show ?thesis by simp
          next
            case snil with gl show ?thesis by (subst (asm) grep6.unfold) simp
          next
            case (scons u' us') with 2 nl gl show ?thesis
              apply clarsimp
              apply (subst (asm) (4) grep6.unfold)
              apply clarsimp
              apply (drule step(3)[rotated]; clarsimp)
              apply (drule step(2)[rotated]; clarsimp)
              apply (clarsimp simp: lt_le)
              apply (metis Integer_le_both_plus_1 Ord_linear_class.le_trans)
              done
          qed
        qed
      qed }
    { case (3 usvs l r) show ?case
      proof(cases us rule: srev_cases)
        case snil with 3 show ?thesis
          apply (subst (asm) root6.unfold)
          apply (subst (asm) grep6.unfold)
          apply fastforce
          done
      next
        case (ssnoc u' us')
        then have "root_bisim pat (?for6 us') (?for5 us')" by (fastforce intro: step(5))
        then show ?thesis
        proof cases
          case bottom with 3 ssnoc show ?thesis by simp
        next
          case Null with 3 ssnoc show ?thesis
            apply simp
            apply (subst (asm) root6.unfold)
            apply (subst (asm) grep6.unfold)
            apply (clarsimp simp: zero_Integer_def one_Integer_def elim!: slengthE)
            done
        next
          case (gl us'' vs'') with 3 ssnoc show ?thesis
            apply clarsimp
            apply (subst (asm) (2) grep6.unfold)
            apply (fastforce simp: zero_Integer_def one_Integer_def split: if_splits dest!: step(1)[rotated] step(3)[rotated] elim!: slengthE)
            done
        qed
      qed (use 3 in simp) }
    { case (4 vs x) show ?case
      proof(cases "prefix\<cdot>[:x:]\<cdot>vs")
        case bottom then show ?thesis
          apply (subst grep6.unfold)
          apply (subst grep5.unfold)
          apply auto
          done
      next
        case TT with \<open>pat \<noteq> \<bottom>\<close> \<open>us \<noteq> \<bottom>\<close> show ?thesis
          apply (subst grep6.unfold)
          apply (subst grep5.unfold)
          apply (cases vs; clarsimp simp: op6_left6)
          apply (cases us; clarsimp simp del: left6.simps left5.simps simp add: root5_left5)
          apply (metis (no_types, lifting) op5_sfoldl_left5 root5_left5 root_bisim.simps sappend_bottom_iff slist.con_rews(3) slist.con_rews(4))
          done
      next
        case FF with \<open>pat \<noteq> \<bottom>\<close> \<open>us \<noteq> \<bottom>\<close> show ?thesis
          apply (subst grep6.unfold)
          apply (subst grep5.unfold)
          using rbl
          apply (auto simp: root_bisim_op_next56 elim!: root_bisim.cases intro: root_bisim_root)
          apply (subst (asm) grep6.unfold)
          apply (cases us; fastforce dest: step(3)[rotated] intro: step(4))
          done
      qed }
    { case 5 show ?case
      proof(cases us rule: srev_cases)
        case (ssnoc u' us')
        then have "root_bisim pat (?for6 us') (?for5 us')" by (fastforce intro: step(5))
        then show ?thesis
        proof cases
          case (gl us'' vs'') with ssnoc show ?thesis
            apply clarsimp
            apply (subst (asm) grep6.unfold)
            apply (fastforce dest: step(3)[rotated] intro: step(4))
            done
        qed (use \<open>pat \<noteq> \<bottom>\<close> ssnoc root_bisim_root in auto)
      qed (use \<open>pat \<noteq> \<bottom>\<close> root_bisim_root in auto) }
    { case (6 vs)
      from rbl \<open>pat \<noteq> \<bottom>\<close> show rbnl: "?rbnl us vs"
      proof cases
        case bottom then show ?thesis by fastforce
      next
        case Null then show ?thesis by (cases vs) auto
      next
        case (gl us'' vs'') then show ?thesis
          apply clarsimp
          apply (subst grep5.unfold)
          apply (subst grep6.unfold)
          apply (subst (asm) grep5.unfold)
          apply (subst (asm) grep6.unfold)
          apply (cases us; clarsimp; cases vs''; clarsimp)
           apply (metis Rep_cfun_strict1 bottom left5.simps(2) left6.simps(2) next_snil next_strict(1) rbl)
          apply (cases vs; clarsimp)
          using rbl apply (fastforce dest: step(3)[rotated] intro: step(6) simp: If2_def[symmetric] simp del: eq_FF split: If2_splits)+
          done
    qed }
  qed
  from \<open>pat \<noteq> \<bottom>\<close> this(4) show "root_bisim pat t6 t5 \<Longrightarrow> root_bisim pat (op6\<cdot>pat\<cdot>t6\<cdot>x) (op5\<cdot>pat\<cdot>t5\<cdot>x)"
    by (auto elim!: root_bisim.cases intro: root_bisim_root)
  show \<open>root_bisim pat (next\<cdot>vs\<cdot>(left6\<cdot>pat\<cdot>us)) (next\<cdot>vs\<cdot>(left5\<cdot>pat\<cdot>us))\<close> by fact
qed

text\<open>

With this result in hand the remainder is technically fiddly but straightforward.

\<close>

lemmas tree_bisimI = iffD2[OF fun_cong[OF tree.bisim_def[unfolded atomize_eq]], rule_format]

lemma tree_bisim_root_bisim:
  shows "tree_bisim (root_bisim pat)"
proof(rule tree_bisimI, erule root_bisim.cases, goal_cases bottom Null Node)
  case (Node x y us vs) then show ?case
    apply (subst (asm) grep5.unfold)
    apply (subst (asm) grep6.unfold)
    apply hypsubst_thin
    apply (clarsimp simp: root_bisim_next_left)
    apply (cases vs; clarsimp)
    apply (cases us; clarsimp simp del: left6.simps left5.simps simp add: op5_sfoldl_left5 op6_left6)
     apply (metis (no_types, lifting) root5_left5 root_bisim.simps slist.con_rews(3,4))
    apply (metis (no_types, lifting) op5_sfoldl_left5 root_bisim.simps sappend_bottom_iff slist.con_rews(3, 4))
    done
qed simp_all

lemma r6_5:
  shows "(root6\<cdot>pat, op6\<cdot>pat) = (root5\<cdot>pat, op5\<cdot>pat)"
proof(cases "pat = \<bottom>")
  case True
  from True have "root6\<cdot>pat = root5\<cdot>pat"
    apply (subst root6.unfold)
    apply (subst grep6.unfold)
    apply (subst root5.unfold)
    apply (subst grep5.unfold)
    apply simp
    done
  moreover
  from True \<open>root6\<cdot>pat = root5\<cdot>pat\<close> have "op6\<cdot>pat\<cdot>t\<cdot>x = op5\<cdot>pat\<cdot>t\<cdot>x" for t x
    by (induct t) simp_all
  ultimately show ?thesis by (simp add: cfun_eq_iff)
next
  case False
  then have root: "root6\<cdot>pat = root5\<cdot>pat"
    by (rule tree.coinduct[OF tree_bisim_root_bisim root_bisim_root])
  moreover
  from root have "op6\<cdot>pat\<cdot>t\<cdot>x = op5\<cdot>pat\<cdot>t\<cdot>x" for t x by (induct t) simp_all
  ultimately show ?thesis by (simp add: cfun_eq_iff)
qed

text\<open>

We conclude this section by observing that accumulator-introduction is a well known technique
(see, for instance, @{cite [cite_macro=citet] \<open>\S13.6\<close> "Hutton:2016"}), but the examples in the
literature assume that the type involved is defined inductively. Bird adopts this strategy without
considering what the mixed inductive/coinductive rule is that justifies the preservation of total
correctness.

The difficulty of this step is why we wired in the `K' opt earlier: it allows us to preserve the
shape of the tree all the way from the data refinement to the final version.

\<close>


subsection\<open> Step 7: Simplify, unfold prefix \<close>

text\<open>

The next step (Bird, bottom of p132) is to move the case split in @{const \<open>grep6\<close>} on \<open>vs\<close> above the
\<open>Node\<close> constructor, which makes @{term \<open>grep7\<close>} strict in that parameter and therefore not
extensionally equal to @{const \<open>grep6\<close>}. We establish a weaker correspondence using fixed-point induction.

We also unfold @{const \<open>prefix\<close>} in @{const \<open>op6\<close>}.

\<close>

fixrec
    root7  :: "[:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree"
and op7    :: "[:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> 'a \<rightarrow> ([:'a:] \<times> [:'a:]) tree"
and grep7  :: "[:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree"
where
  [simp del]:
  "root7\<cdot>pat = grep7\<cdot>pat\<cdot>Null\<cdot>([::], pat)"
| "op7\<cdot>pat\<cdot>Null\<cdot>x = root7\<cdot>pat"
| "op7\<cdot>pat\<cdot>(Node\<cdot>(us, [::])\<cdot>l\<cdot>r)\<cdot>x = op7\<cdot>pat\<cdot>l\<cdot>x" \<comment>\<open> Unfold \<open>prefix\<close> \<close>
| "\<lbrakk>v \<noteq> \<bottom>; vs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow>
   op7\<cdot>pat\<cdot>(Node\<cdot>(us, v :# vs)\<cdot>l\<cdot>r)\<cdot>x = If eq\<cdot>x\<cdot>v then r else op7\<cdot>pat\<cdot>l\<cdot>x"
| [simp del]:
  "grep7\<cdot>pat\<cdot>l\<cdot>(us, [::]) = Node\<cdot>(us, [::])\<cdot>l\<cdot>Null" \<comment>\<open> Case split on \<open>vs\<close> hoisted above \<open>Node\<close>. \<close>
| "\<lbrakk>v \<noteq> \<bottom>; vs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow>
   grep7\<cdot>pat\<cdot>l\<cdot>(us, v :# vs) = Node\<cdot>(us, v :# vs)\<cdot>(next\<cdot>(v :# vs)\<cdot>l)\<cdot>(grep7\<cdot>pat\<cdot>(op7\<cdot>pat\<cdot>l\<cdot>v)\<cdot>(us :@ [:v:], vs))"

schematic_goal root7_op7_grep7_def:
  "( root7  :: [:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , op7    :: [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> 'a \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , grep7  :: [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree )
   = fix\<cdot>?F"
unfolding root7_def op7_def grep7_def by simp

lemma r7_6_aux:
  assumes "pat \<noteq> \<bottom>"
  shows
  "(\<Lambda> (root, op, grep). (root\<cdot>pat, seq\<cdot>x\<cdot>(op\<cdot>pat\<cdot>t\<cdot>x), grep\<cdot>pat\<cdot>l\<cdot>(us, vs)))\<cdot>
   ( root7  :: [:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , op7    :: [:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> 'a \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , grep7  :: [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree )
 = (\<Lambda> (root, op, grep). (root\<cdot>pat, seq\<cdot>x\<cdot>(op\<cdot>pat\<cdot>t\<cdot>x), seq\<cdot>vs\<cdot>(grep\<cdot>pat\<cdot>l\<cdot>(us, vs))))\<cdot>
   ( root6  :: [:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , op6    :: [:'a::Eq_def:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> 'a \<rightarrow> ([:'a:] \<times> [:'a:]) tree
   , grep6  :: [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree \<rightarrow> [:'a:] \<times> [:'a:] \<rightarrow> ([:'a:] \<times> [:'a:]) tree )"
unfolding root6_op6_grep6_def root7_op7_grep7_def
proof(induct arbitrary: t x l us vs rule: parallel_fix_ind[case_names adm bottom step])
  case (step X Y t x l us vs) then show ?case
    apply -
    apply (cases X, cases Y)
    apply (rename_tac r10 o10 g10 r9 o9 g9)
    apply (clarsimp simp: cfun_eq_iff assms match_Node_mplus_match_Node match_Null_match_Node_tree_case tree_case_distr match_snil_match_scons_slist_case slist_case_distr If_distr)
    apply (intro allI conjI)
     apply (case_tac t; clarsimp)
     apply (rename_tac us vs l r)
     apply (case_tac "x = \<bottom>"; clarsimp)
     apply (case_tac vs; clarsimp; fail)
    apply (case_tac vs; clarsimp)
    apply (metis ID1 seq_simps(3))
    done
qed simp_all

lemma r7_6:
  assumes "pat \<noteq> \<bottom>"
  shows "root7\<cdot>pat = root6\<cdot>pat"
    and "x \<noteq> \<bottom> \<Longrightarrow> op7\<cdot>pat\<cdot>t\<cdot>x = op6\<cdot>pat\<cdot>t\<cdot>x"
using r7_6_aux[OF assms] by (force simp: cfun_eq_iff dest: spec[where x=x])+


subsection\<open> Step 8: Discard us \label{sec:KMP:step8} \<close>

text\<open>

We now discard \<open>us\<close> from the tree as it is no longer used. This requires a new
definition of @{const \<open>next\<close>}.

This is essentially another data refinement.

\<close>

fixrec next' :: "'a::Eq_def \<rightarrow> [:'a:] tree \<rightarrow> [:'a:] tree" where
  "next'\<cdot>x\<cdot>Null = Null"
| "next'\<cdot>x\<cdot>(Node\<cdot>[::]\<cdot>l\<cdot>r) = Node\<cdot>[::]\<cdot>l\<cdot>r"
| "\<lbrakk>v \<noteq> \<bottom>; vs \<noteq> \<bottom>; x \<noteq> \<bottom>\<rbrakk> \<Longrightarrow>
   next'\<cdot>x\<cdot>(Node\<cdot>(v :# vs)\<cdot>l\<cdot>r) = If eq\<cdot>x\<cdot>v then l else Node\<cdot>(v :# vs)\<cdot>l\<cdot>r"

fixrec \<comment>\<open> Bird p133 \<close>
    root8 :: "[:'a::Eq_def:] \<rightarrow> [:'a:] tree"
and op8   :: "[:'a:] \<rightarrow> [:'a:] tree \<rightarrow> 'a \<rightarrow> [:'a:] tree"
and grep8 :: "[:'a:] \<rightarrow> [:'a:] tree \<rightarrow> [:'a:] \<rightarrow> [:'a:] tree"
where
[simp del]:
  "root8\<cdot>pat = grep8\<cdot>pat\<cdot>Null\<cdot>pat"
| "op8\<cdot>pat\<cdot>Null\<cdot>x = root8\<cdot>pat"
| "op8\<cdot>pat\<cdot>(Node\<cdot>[::]\<cdot>l\<cdot>r)\<cdot>x = op8\<cdot>pat\<cdot>l\<cdot>x"
| "\<lbrakk>v \<noteq> \<bottom>; vs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow>
   op8\<cdot>pat\<cdot>(Node\<cdot>(v :# vs)\<cdot>l\<cdot>r)\<cdot>x = If eq\<cdot>x\<cdot>v then r else op8\<cdot>pat\<cdot>l\<cdot>x"
| "grep8\<cdot>pat\<cdot>l\<cdot>[::] = Node\<cdot>[::]\<cdot>l\<cdot>Null"
| "\<lbrakk>v \<noteq> \<bottom>; vs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow>
   grep8\<cdot>pat\<cdot>l\<cdot>(v :# vs) = Node\<cdot>(v :# vs)\<cdot>(next'\<cdot>v\<cdot>l)\<cdot>(grep8\<cdot>pat\<cdot>(op8\<cdot>pat\<cdot>l\<cdot>v)\<cdot>vs)"

fixrec ok8 :: "[:'a:] tree \<rightarrow> tr" where
  "vs \<noteq> \<bottom> \<Longrightarrow> ok8\<cdot>(Node\<cdot>vs\<cdot>l\<cdot>r) = snull\<cdot>vs"

schematic_goal root8_op8_grep8_def:
  "( root8 :: [:'a::Eq_def:] \<rightarrow> [:'a:] tree
   , op8   :: [:'a:] \<rightarrow> [:'a:] tree \<rightarrow> 'a \<rightarrow> [:'a:] tree
   , grep8 :: [:'a:] \<rightarrow> [:'a:] tree \<rightarrow> [:'a:] \<rightarrow> [:'a:] tree )
   = fix\<cdot>?F"
unfolding op8_def root8_def grep8_def by simp

lemma next'_strict[simp]:
  "next'\<cdot>x\<cdot>\<bottom> = \<bottom>"
  "next'\<cdot>\<bottom>\<cdot>(Node\<cdot>(v :# vs)\<cdot>l\<cdot>r) = \<bottom>"
by (cases "v :# vs = \<bottom>"; fixrec_simp; clarsimp)+

lemma root8_op8_grep8_strict[simp]:
  "grep8\<cdot>pat\<cdot>l\<cdot>\<bottom> = \<bottom>"
  "op8\<cdot>pat\<cdot>\<bottom> = \<bottom>"
  "root8\<cdot>\<bottom> = \<bottom>"
by fixrec_simp+

lemma ok8_strict[simp]:
  "ok8\<cdot>\<bottom> = \<bottom>"
  "ok8\<cdot>Null = \<bottom>"
by fixrec_simp+

text\<open>

We cannot readily relate @{const \<open>next\<close>} and @{const
\<open>next'\<close>} using worker/wrapper as the obvious abstraction
is not invertible.  Conversely the desired result is easily shown by
fixed-point induction.

\<close>

lemma next'_next:
  assumes "v \<noteq> \<bottom>"
  assumes "vs \<noteq> \<bottom>"
  shows "next'\<cdot>v\<cdot>(tree_map'\<cdot>csnd\<cdot>t) = tree_map'\<cdot>csnd\<cdot>(next\<cdot>(v :# vs)\<cdot>t)"
proof(induct t)
  case (Node usvs' l r) with assms show ?case
    apply (cases usvs'; clarsimp)
    apply (rename_tac us'' vs'')
    apply (case_tac vs''; clarsimp simp: If_distr)
    done
qed (use assms in simp_all)

lemma r8_7[simplified]:
  shows "(\<Lambda> (root, op, grep). ( root\<cdot>pat
                              ,  op\<cdot>pat\<cdot>(tree_map'\<cdot>csnd\<cdot>t)\<cdot>x
                              , grep\<cdot>pat\<cdot>(tree_map'\<cdot>csnd\<cdot>l)\<cdot>(csnd\<cdot>usvs)))\<cdot>(root8, op8, grep8)
       = (\<Lambda> (root, op, grep). ( tree_map'\<cdot>csnd\<cdot>(root\<cdot>pat)
                              , tree_map'\<cdot>csnd\<cdot>(op\<cdot>pat\<cdot>t\<cdot>x)
                              , tree_map'\<cdot>csnd\<cdot>(grep\<cdot>pat\<cdot>l\<cdot>usvs)))\<cdot>(root7, op7, grep7)"
unfolding root7_op7_grep7_def root8_op8_grep8_def
proof(induct arbitrary: l t usvs x rule: parallel_fix_ind[case_names adm bottom step])
  case (step X Y l t usvs x) then show ?case
    apply -
    apply (cases X; cases Y)
    apply (clarsimp simp: cfun_eq_iff next'_next
                          match_snil_match_scons_slist_case slist_case_distr
                          match_Node_mplus_match_Node match_Null_match_Node_tree_case tree_case_distr
                    cong: slist_case_cong)
    apply (cases t; clarsimp simp: If_distr)
    apply (rename_tac us vs l r)
    apply (case_tac vs; fastforce)
    done
qed simp_all

text\<open>

Top-level equivalence follows from \<open>lfp_fusion\<close> specialized to \<open>sscanl\<close> (@{thm [source]
"sscanl_lfp_fusion"}), which states that
\begin{center}
  @{prop \<open>smap\<cdot>g oo sscanl\<cdot>f\<cdot>z = sscanl\<cdot>f'\<cdot>(g\<cdot>z)\<close>}
\end{center}
provided that \<open>g\<close> is strict and the following diagram commutes for @{prop \<open>x \<noteq> \<bottom>\<close>}:

\begin{center}
  \begin{tikzcd}[column sep=6em]
    a \arrow[r, "\<open>\<Lambda> a. f\<cdot>a\<cdot>x\<close>"] \arrow[d, "\<open>g\<close>"] & a' \arrow[d, "\<open>g\<close>"] \\
    b \arrow[r, "\<open>\<Lambda> a. f'\<cdot>a\<cdot>x\<close>"]                 & b'
  \end{tikzcd}
\end{center}

\<close>

lemma ok8_ok8: "ok8 oo tree_map'\<cdot>csnd = snull oo csnd oo abs2" (is "?lhs = ?rhs")
proof(rule cfun_eqI)
  fix t show "?lhs\<cdot>t = ?rhs\<cdot>t"
    by (cases t; clarsimp) (metis ok8.simps ok8_strict(1) snull_strict tree.con_rews(3))
qed

lemma matches8: \<comment>\<open> Bird p133 \<close>
  shows "matches\<cdot>pat = smap\<cdot>cfst oo sfilter\<cdot>(ok8 oo csnd) oo sscanl\<cdot>(\<Lambda> (n, x) y. (n + 1, op8\<cdot>pat\<cdot>x\<cdot>y))\<cdot>(0, root8\<cdot>pat)" (is "?lhs = ?rhs")
proof(cases "pat = \<bottom>")
  case True
  then have "?lhs\<cdot>xs = ?rhs\<cdot>xs" for xs by (cases xs; clarsimp)
  then show ?thesis by (simp add: cfun_eq_iff)
next
  case False
  then have *: "matches\<cdot>pat = smap\<cdot>cfst oo sfilter\<cdot>(snull oo csnd oo abs2 oo csnd) oo sscanl\<cdot>(\<Lambda> (n, x) y. (n + 1, op7\<cdot>pat\<cdot>x\<cdot>y))\<cdot>(0, root7\<cdot>pat)"
    using data_refinement[where 'a='a] r3_2[where 'a='a] r4_3[where 'a='a] r5_4[where 'a='a] r6_5(1)[where pat=pat] r7_6[where pat=pat]
    unfolding matches2.unfold by (fastforce simp: oo_assoc cfun_eq_iff csplit_def intro!: cfun_arg_cong sscanl_cong)
  from \<open>pat \<noteq> \<bottom>\<close> show ?thesis
    apply -
    apply (subst conjunct1[OF r8_7])
    apply (subst sscanl_lfp_fusion[where g="ID ** tree_map'\<cdot>csnd" and z="(0, root7\<cdot>pat)", simplified, symmetric])
     prefer 2
     apply (subst oo_assoc, subst sfilter_smap, simp)
     apply (simp add: oo_assoc)
     apply (simp add: oo_assoc[symmetric])
     apply (subst oo_assoc, subst ok8_ok8)
     apply (clarsimp simp: oo_assoc *)
     apply (rule refl) (* instantiate schematic *)
    apply (clarsimp simp: r8_7)
    done
qed


subsection\<open> Step 9: Factor out pat (final version) \label{sec:KMP:final_version} \<close>

text\<open>

Finally we factor @{term \<open>pat\<close>} from these definitions and arrive
at Bird's cyclic data structure, which when executed using lazy
evaluation actually memoises the computation of @{const \<open>grep8\<close>}.

The \<open>Letrec\<close> syntax groups recursive bindings with
\<open>,\<close> and separates these with \<open>;\<close>. Its lack
of support for clausal definitions, and that \texttt{HOLCF}
\<open>case\<close> does not support nested patterns, leads to some
awkwardness.

\<close>

fixrec matchesf :: "[:'a::Eq_def:] \<rightarrow> [:'a:] \<rightarrow> [:Integer:]" where
[simp del]: "matchesf\<cdot>pat =
    (Letrec okf = (\<Lambda> (Node\<cdot>vs\<cdot>l\<cdot>r). snull\<cdot>vs);
            nextf = (\<Lambda> x t. case t of
                   Null \<Rightarrow> Null
                 | Node\<cdot>vs\<cdot>l\<cdot>r \<Rightarrow> (case vs of
                     [::] \<Rightarrow> t
                   | v :# vs \<Rightarrow> If eq\<cdot>x\<cdot>v then l else t));
            rootf = grepf\<cdot>Null\<cdot>pat,
            opf = (\<Lambda> t x. case t of
                   Null \<Rightarrow> rootf
                 | Node\<cdot>vs\<cdot>l\<cdot>r \<Rightarrow> (case vs of
                     [::] \<Rightarrow> opf\<cdot>l\<cdot>x
                   | v :# vs \<Rightarrow> If eq\<cdot>x\<cdot>v then r else opf\<cdot>l\<cdot>x)),
            grepf = (\<Lambda> l vs. case vs of
                   [::] \<Rightarrow> Node\<cdot>[::]\<cdot>l\<cdot>Null
                 | v :# vs \<Rightarrow> Node\<cdot>(v :# vs)\<cdot>(nextf\<cdot>v\<cdot>l)\<cdot>(grepf\<cdot>(opf\<cdot>l\<cdot>v)\<cdot>vs));
            stepf = (\<Lambda> (n, t) x. (n + 1, opf\<cdot>t\<cdot>x))
         in smap\<cdot>cfst oo sfilter\<cdot>(okf oo csnd) oo sscanl\<cdot>stepf\<cdot>(0, rootf))"

lemma matchesf_ok8: "(\<Lambda> (Node\<cdot>vs\<cdot>l\<cdot>r). snull\<cdot>vs) = ok8"
by (clarsimp simp: cfun_eq_iff; rename_tac x; case_tac x; clarsimp)

lemma matchesf_next':
  "(\<Lambda> x t. case t of Null \<Rightarrow> Null | Node\<cdot>vs\<cdot>l\<cdot>r \<Rightarrow> (case vs of [::] \<Rightarrow> t | v :# vs \<Rightarrow> If eq\<cdot>x\<cdot>v then l else t)) = next'"
apply (clarsimp simp: cfun_eq_iff next'.unfold
                      match_snil_match_scons_slist_case slist_case_distr
                      match_Node_mplus_match_Node match_Null_match_Node_tree_case tree_case_distr)
apply (simp cong: tree_case_cong)
apply (simp cong: slist_case_cong)
done

lemma matchesf_8:
  "fix\<cdot>(\<Lambda> (Rootf, Opf, Grepf).
          ( Grepf\<cdot>Null\<cdot>pat
          , \<Lambda> t x. case t of Null \<Rightarrow> Rootf | Node\<cdot>vs\<cdot>l\<cdot>r \<Rightarrow>
                (case vs of [::] \<Rightarrow> Opf\<cdot>l\<cdot>x | v :# vs \<Rightarrow> If eq\<cdot>x\<cdot>v then r else Opf\<cdot>l\<cdot>x)
          , \<Lambda> l vs. case vs of [::] \<Rightarrow> Node\<cdot>[::]\<cdot>l\<cdot>Null | v :# vs \<Rightarrow> Node\<cdot>(v :# vs)\<cdot>(next'\<cdot>v\<cdot>l)\<cdot>(Grepf\<cdot>(Opf\<cdot>l\<cdot>v)\<cdot>vs)) )
= (\<Lambda> (root, op, grep). (root\<cdot>pat, op\<cdot>pat, grep\<cdot>pat))\<cdot>(root8, op8, grep8)"
unfolding root8_op8_grep8_def
by (rule lfp_fusion[symmetric])
   (fastforce simp: cfun_eq_iff
                    match_snil_match_scons_slist_case slist_case_distr
                    match_Node_mplus_match_Node match_Null_match_Node_tree_case tree_case_distr)+

theorem matches_final:
  shows "matches = matchesf"
by (clarsimp simp: cfun_eq_iff fix_const eta_cfun csplit_cfun3 CLetrec_def
                   matches8 matchesf.unfold matchesf_next' matchesf_ok8 matchesf_8[simplified eta_cfun])

text\<open>

The final program above is easily syntactically translated into the
Haskell shown in Figure~\ref{fig:haskell-kmp}, and one can expect
GHC's list fusion machinery to compile the top-level driver into an
efficient loop.  @{cite [cite_macro=citet] "LochbihlerMaximova:2015"}
have mechanised this optimisation for Isabelle/HOL's code generator
(and see also @{cite [cite_macro=citet] "Huffman:2009"}).

As we lack both pieces of infrastructure we show such a fusion is sound
by hand.

\<close>

lemma fused_driver':
  assumes "g\<cdot>\<bottom> = \<bottom>"
  assumes "p\<cdot>\<bottom> = \<bottom>"
  shows "smap\<cdot>g oo sfilter\<cdot>p oo sscanl\<cdot>f\<cdot>z
       = (\<mu> R. \<Lambda> z xxs. case xxs of
                          [::] \<Rightarrow> If p\<cdot>z then [:g\<cdot>z:] else [::]
                        | x :# xs \<Rightarrow> let z' = f\<cdot>z\<cdot>x in If p\<cdot>z then g\<cdot>z :# R\<cdot>z'\<cdot>xs else R\<cdot>z'\<cdot>xs)\<cdot>z"
(is "?lhs = ?rhs")
proof(rule cfun_eqI)
  fix xs from assms show "?lhs\<cdot>xs = ?rhs\<cdot>xs"
    by (induct xs arbitrary: z) (subst fix_eq; fastforce simp: If_distr Let_def)+
qed

(*<*)

end
(*>*)
