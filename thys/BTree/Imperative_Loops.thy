theory Imperative_Loops
  imports 
    "Refine_Imperative_HOL.Sepref_HOL_Bindings"
    "Refine_Imperative_HOL.Pf_Mono_Prover"
    "Refine_Imperative_HOL.Pf_Add"


begin

section \<open>Imperative Loops\<close>

text "An auxiliary while rule provided by Peter Lammich."

lemma heap_WHILET_rule:
  assumes
    "wf R"
    "P \<Longrightarrow>\<^sub>A I s"
    "\<And>s. <I s * true> bi s <\<lambda>r. I s * \<up>(r \<longleftrightarrow> b s)>\<^sub>t"
    "\<And>s. b s \<Longrightarrow> <I s * true> f s <\<lambda>s'. I s' * \<up>((s', s) \<in> R)>\<^sub>t"
    "\<And>s. \<not> b s \<Longrightarrow> I s \<Longrightarrow>\<^sub>A Q s"
  shows "<P * true> heap_WHILET bi f s <Q>\<^sub>t"
proof -
  have "<I s * true> heap_WHILET bi f s <\<lambda>s'. I s' * \<up>(\<not> b s')>\<^sub>t"
    using assms(1)
  proof (induction arbitrary:)
    case (less s)
    show ?case
    proof (cases "b s")
      case True
      then show ?thesis
        by (subst heap_WHILET_unfold) (sep_auto heap: assms(3,4) less)
    next
      case False
      then show ?thesis
        by (subst heap_WHILET_unfold) (sep_auto heap: assms(3))
    qed
  qed
  then show ?thesis
    apply (rule cons_rule[rotated 2])
     apply (intro ent_star_mono assms(2) ent_refl)
    apply clarsimp
    apply (intro ent_star_mono assms(5) ent_refl)
    .
qed


lemma heap_WHILET_rule':
  assumes
    "wf R"
    "P \<Longrightarrow>\<^sub>A I s si * F"
    "\<And>si s. <I s si * F> bi si <\<lambda>r. I s si * F * \<up>(r \<longleftrightarrow> b s)>\<^sub>t"
    "\<And>si s. b s \<Longrightarrow> <I s si * F> f si <\<lambda>si'. \<exists>\<^sub>As'. I s' si' * F * \<up>((s', s) \<in> R)>\<^sub>t"
    "\<And>si s. \<not> b s \<Longrightarrow> I s si * F \<Longrightarrow>\<^sub>A Q s si"
  shows "<P> heap_WHILET bi f si <\<lambda>si. \<exists>\<^sub>As. Q s si>\<^sub>t"
proof -
  have "<I s si * F> heap_WHILET bi f si <\<lambda>si'. \<exists>\<^sub>As'. I s' si' * F * \<up>(\<not> b s')>\<^sub>t"
    using assms(1)
  proof (induction arbitrary: si)
    case (less s)
    show ?case
    proof (cases "b s")
      case True
      then show ?thesis
        apply (subst heap_WHILET_unfold)
        apply (sep_auto heap: assms(3,4) less)
        done
    next
      case False
      then show ?thesis
        by (subst heap_WHILET_unfold) (sep_auto heap: assms(3))
    qed
  qed
  then show ?thesis
    apply (rule cons_rule[rotated 2])
     apply (intro ent_star_mono assms(2) ent_refl)
    apply clarsimp
    apply (sep_auto )
    apply (erule ent_frame_fwd[OF assms(5)])
     apply frame_inference
    by sep_auto

qed

(* Added by NM, just a technicality since this rule fits our use case better *)

text "I derived my own version,
simply because it was a better fit to my use case."

corollary heap_WHILET_rule'':
  assumes
    "wf R"
    "P \<Longrightarrow>\<^sub>A I s"
    "\<And>s. <I s * true> bi s <\<lambda>r. I s * \<up>(r \<longleftrightarrow> b s)>\<^sub>t"
    "\<And>s. b s \<Longrightarrow> <I s * true> f s <\<lambda>s'. I s' * \<up>((s', s) \<in> R)>\<^sub>t"
    "\<And>s. \<not> b s \<Longrightarrow> I s \<Longrightarrow>\<^sub>A Q s"
  shows "<P> heap_WHILET bi f s <Q>\<^sub>t"
  supply R = heap_WHILET_rule'[of R P "\<lambda>s si. \<up>(s = si) * I s" s _ true bi b f "\<lambda>s si.\<up>(s = si) * Q s * true"]
  thm R
  using assms ent_true_drop apply(sep_auto heap: R assms)
  done
    (*
explicit proof:

proof -
  have "<I s * true> heap_WHILET bi f s <\<lambda>s'. I s' * \<up>(\<not> b s')>\<^sub>t"
    using assms(1)
  proof (induction arbitrary:)
    case (less s)
    show ?case
    proof (cases "b s")
      case True
      then show ?thesis
        by (subst heap_WHILET_unfold) (sep_auto heap: assms(3,4) less)
    next
      case False
      then show ?thesis
        by (subst heap_WHILET_unfold) (sep_auto heap: assms(3))
    qed
  qed
  then show ?thesis
    apply (rule cons_rule[rotated 2])
     apply (intro ent_true_drop assms(2) ent_refl)
    apply clarsimp
    apply(intro ent_star_mono assms(5) ent_refl)
    .
qed
*)

end
