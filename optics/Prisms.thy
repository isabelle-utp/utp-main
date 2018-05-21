section \<open>Prisms\<close>

theory Prisms
  imports Lens_Laws
begin
  
text \<open>Prisms are like lenses, but they act on sum types rather than product types. For now
  we do not support many properties about them. See \url{https://hackage.haskell.org/package/lens-4.15.2/docs/Control-Lens-Prism.html}
  for more information.\<close>

subsection \<open> Main Definitions \<close>

record ('v, 's) prism =
  prism_match :: "'s \<Rightarrow> 'v option" ("match\<index>")
  prism_build :: "'v \<Rightarrow> 's" ("build\<index>")

locale wb_prism =
  fixes x :: "('v, 's) prism" (structure)
  assumes match_build: "match (build v) = Some v"
  and build_match: "match s = Some v \<Longrightarrow> s = build v"
begin

  lemma build_match_iff: "match s = Some v \<longleftrightarrow> s = build v"
    using build_match match_build by blast

  lemma range_build: "range build = dom match"
    using build_match match_build by fastforce
end

declare wb_prism.match_build [simp]
declare wb_prism.build_match_iff [simp]

definition prism_suml :: "('a, 'a + 'b) prism" where
"prism_suml = \<lparr> prism_match = (\<lambda> v. case v of Inl x \<Rightarrow> Some x | _ \<Rightarrow> None), prism_build = Inl \<rparr>"

lemma wb_prim_suml: "wb_prism prism_suml"
  apply (unfold_locales)
   apply (simp_all add: prism_suml_def sum.case_eq_if)
  apply (metis option.inject option.simps(3) sum.collapse(1))
done

definition prism_diff :: "('a, 's) prism \<Rightarrow> ('b, 's) prism \<Rightarrow> bool" (infix "\<nabla>" 50) where
"prism_diff X Y = (range build\<^bsub>X\<^esub> \<inter> range build\<^bsub>Y\<^esub> = {})"

lemma prism_diff_build: "X \<nabla> Y \<Longrightarrow> build\<^bsub>X\<^esub> u \<noteq> build\<^bsub>Y\<^esub> v"
  by (simp add: disjoint_iff_not_equal prism_diff_def)

definition prism_plus :: "('a, 's) prism \<Rightarrow> ('b, 's) prism \<Rightarrow> ('a + 'b, 's) prism" (infixl "+\<^sub>P" 85) where
"X +\<^sub>P Y = \<lparr> prism_match = (\<lambda> s. case (match\<^bsub>X\<^esub> s, match\<^bsub>Y\<^esub> s) of
                                 (Some u, _) \<Rightarrow> Some (Inl u) |
                                 (None, Some v) \<Rightarrow> Some (Inr v) |
                                 (None, None) \<Rightarrow> None),
           prism_build = (\<lambda> v. case v of Inl x \<Rightarrow> build\<^bsub>X\<^esub> x | Inr y \<Rightarrow> build\<^bsub>Y\<^esub> y) \<rparr>"

subsection \<open> Relating prisms and lenses \<close>

text \<open> A prism lens is a weak lens where put is the same as create. This essentially means that
  put does not leave any residual information when applied. \<close>

locale prism_lens = weak_lens +
  assumes put_is_create [simp]: "put s = create"
begin

  lemma lens_source_create: "range create = \<S>"
    by (auto simp add: lens_source_def)

end

declare prism_lens.put_is_create [simp]

sublocale prism_lens \<subseteq> mwb_lens
  by (unfold_locales, simp add: put_is_create)

definition lens_of_prism :: "('a, 's) prism \<Rightarrow> ('a \<Longrightarrow> 's)" where
"lens_of_prism X = \<lparr> lens_get = (\<lambda> s. if s \<in> range build\<^bsub>X\<^esub> then the (match\<^bsub>X\<^esub> s) else undefined)
                   , lens_put = (\<lambda> s v. build\<^bsub>X\<^esub> v) \<rparr>"

lemma wb_prism_is_mwb_lens:
  "wb_prism X \<Longrightarrow> mwb_lens (lens_of_prism X)"
  by (unfold_locales, simp_all add: lens_of_prism_def)

lemma wb_prism_is_prism_lens:
  "wb_prism X \<Longrightarrow> prism_lens (lens_of_prism X)"
  by (unfold_locales, auto simp add: lens_of_prism_def lens_source_def lens_create_def)

definition prism_of_lens :: "('a \<Longrightarrow> 's) \<Rightarrow> ('a, 's) prism" where
"prism_of_lens X = \<lparr> prism_match = (\<lambda> s. if (s \<in> range(create\<^bsub>X\<^esub>)) then (Some (get\<^bsub>X\<^esub> s)) else None)
                   , prism_build = create\<^bsub>X\<^esub> \<rparr>"

lemma mwb_lens_is_wb_prism:
  assumes "mwb_lens X"
  shows "wb_prism (prism_of_lens X)"
proof
  fix s v
  show "match\<^bsub>prism_of_lens X\<^esub> (build\<^bsub>prism_of_lens X\<^esub> v) = Some v"
    by (simp add: prism_of_lens_def weak_lens.create_closure assms)
  show "match\<^bsub>prism_of_lens X\<^esub> s = Some v \<Longrightarrow> s = build\<^bsub>prism_of_lens X\<^esub> v" (is "?A \<Longrightarrow> ?B")
  proof -
    assume a: ?A
    have 1: "s \<in> range create\<^bsub>X\<^esub>"
      by (metis (mono_tags, lifting) a option.simps(3) prism.select_convs(1) prism_of_lens_def)
    have 2: "get\<^bsub>X\<^esub> s = v"
      by (metis (mono_tags, lifting) "1" a option.sel prism.select_convs(1) prism_of_lens_def)
    with 1 2 show ?B
      by (metis (no_types, lifting) assms f_inv_into_f mwb_lens_weak prism.select_convs(2) prism_of_lens_def weak_lens.create_get)
  qed
qed

lemma lens_of_prism_inverse:
  assumes "wb_prism X"
  shows "prism_of_lens (lens_of_prism X) = X" (is "?lhs = ?rhs")
proof -
  from assms have 1: "match\<^bsub>?lhs\<^esub> = match\<^bsub>?rhs\<^esub>"
    apply (rule_tac ext)
    apply (auto simp add: prism_of_lens_def lens_of_prism_def lens_create_def assms)
    apply (metis assms domIff wb_prism.range_build)
    done
  from assms have 2: "build\<^bsub>?lhs\<^esub> = build\<^bsub>?rhs\<^esub>"
    by (auto simp add: prism_of_lens_def lens_of_prism_def lens_create_def)
  from 1 2 show ?thesis
    by simp
qed

text \<open> @{term lens_of_prism} inverts @{term prism_of_lens} provided that the get function always
  returns the same arbitrary element for unhealthy sources. \<close>

lemma prism_of_lens_almost_inverse:
  assumes "prism_lens X" "\<And>x. x \<notin> \<S>\<^bsub>X\<^esub> \<Longrightarrow> get\<^bsub>X\<^esub> x = undefined"
  shows "lens_of_prism (prism_of_lens X) = X" (is "?lhs = ?rhs")
proof -
  have 1:"put\<^bsub>?lhs\<^esub> = put\<^bsub>?rhs\<^esub>"
    by (auto simp add: prism_of_lens_def lens_of_prism_def assms)
  have 2:"get\<^bsub>?lhs\<^esub> = get\<^bsub>?rhs\<^esub>"
    apply (rule ext)
    apply (auto simp add: prism_of_lens_def lens_of_prism_def)
    apply (simp add: assms(1) assms(2) prism_lens.lens_source_create)
    done
  show ?thesis
    by (simp add: "1" "2")
qed

text \<open> We have now shown that a prism can be losslessly represented as a kind of lens. \<close>

end