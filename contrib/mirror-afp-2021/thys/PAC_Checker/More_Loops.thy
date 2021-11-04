(*
  File:         More_Loops.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Maintainer:   Mathias Fleury, JKU
*)
theory More_Loops
imports
  "Refine_Monadic.Refine_While"
  "Refine_Monadic.Refine_Foreach"
  "HOL-Library.Rewrite"
begin

subsection \<open>More Theorem about Loops\<close>

text \<open>Most theorem below have a counterpart in the Refinement Framework that is weaker (by missing
  assertions for example that are critical for code generation).
\<close>
lemma Down_id_eq:
  \<open>\<Down>Id x = x\<close>
  by auto

lemma while_upt_while_direct1:
  "b \<ge> a \<Longrightarrow>
  do {
    (_,\<sigma>) \<leftarrow> WHILE\<^sub>T (FOREACH_cond c) (\<lambda>x. do {ASSERT (FOREACH_cond c x); FOREACH_body f x})
      ([a..<b],\<sigma>);
    RETURN \<sigma>
  } \<le> do {
    (_,\<sigma>) \<leftarrow> WHILE\<^sub>T (\<lambda>(i, x). i < b \<and> c x) (\<lambda>(i, x). do {ASSERT (i < b);  \<sigma>'\<leftarrow>f i x; RETURN (i+1,\<sigma>')
}) (a,\<sigma>);
    RETURN \<sigma>
  }"
  apply (rewrite at \<open>_ \<le> \<hole>\<close> Down_id_eq[symmetric])
  apply (refine_vcg WHILET_refine[where R = \<open>{((l, x'), (i::nat, x::'a)). x= x' \<and> i \<le> b \<and> i \<ge> a \<and>
     l = drop (i-a) [a..<b]}\<close>])
  subgoal by auto
  subgoal by (auto simp: FOREACH_cond_def)
  subgoal by (auto simp: FOREACH_body_def intro!: bind_refine[OF Id_refine])
  subgoal by auto
  done

lemma while_upt_while_direct2:
  "b \<ge> a \<Longrightarrow>
  do {
    (_,\<sigma>) \<leftarrow> WHILE\<^sub>T (FOREACH_cond c) (\<lambda>x. do {ASSERT (FOREACH_cond c x); FOREACH_body f x})
      ([a..<b],\<sigma>);
    RETURN \<sigma>
  } \<ge> do {
    (_,\<sigma>) \<leftarrow> WHILE\<^sub>T (\<lambda>(i, x). i < b \<and> c x) (\<lambda>(i, x). do {ASSERT (i < b);  \<sigma>'\<leftarrow>f i x; RETURN (i+1,\<sigma>')
}) (a,\<sigma>);
    RETURN \<sigma>
  }"
  apply (rewrite at \<open>_ \<le> \<hole>\<close> Down_id_eq[symmetric])
  apply (refine_vcg WHILET_refine[where R = \<open>{((i::nat, x::'a), (l, x')). x= x' \<and> i \<le> b \<and> i \<ge> a \<and>
    l = drop (i-a) [a..<b]}\<close>])
  subgoal by auto
  subgoal by (auto simp: FOREACH_cond_def)
  subgoal by (auto simp: FOREACH_body_def intro!: bind_refine[OF Id_refine])
  subgoal by (auto simp: FOREACH_body_def intro!: bind_refine[OF Id_refine])
  subgoal by auto
  done

lemma while_upt_while_direct:
  "b \<ge> a \<Longrightarrow>
  do {
    (_,\<sigma>) \<leftarrow> WHILE\<^sub>T (FOREACH_cond c) (\<lambda>x. do {ASSERT (FOREACH_cond c x); FOREACH_body f x})
      ([a..<b],\<sigma>);
    RETURN \<sigma>
  } = do {
    (_,\<sigma>) \<leftarrow> WHILE\<^sub>T (\<lambda>(i, x). i < b \<and> c x) (\<lambda>(i, x). do {ASSERT (i < b);  \<sigma>'\<leftarrow>f i x; RETURN (i+1,\<sigma>')
}) (a,\<sigma>);
    RETURN \<sigma>
  }"
  using while_upt_while_direct1[of a b] while_upt_while_direct2[of a b]
  unfolding order_class.eq_iff by fast

lemma while_nfoldli:
  "do {
    (_,\<sigma>) \<leftarrow> WHILE\<^sub>T (FOREACH_cond c) (\<lambda>x. do {ASSERT (FOREACH_cond c x); FOREACH_body f x}) (l,\<sigma>);
    RETURN \<sigma>
  } \<le> nfoldli l c f \<sigma>"
  apply (induct l arbitrary: \<sigma>)
  apply (subst WHILET_unfold)
  apply (simp add: FOREACH_cond_def)

  apply (subst WHILET_unfold)
  apply (auto
    simp: FOREACH_cond_def FOREACH_body_def
    intro: bind_mono Refine_Basic.bind_mono(1))
 done
lemma nfoldli_while: "nfoldli l c f \<sigma>
          \<le>
         (WHILE\<^sub>T\<^bsup>I\<^esup>
           (FOREACH_cond c) (\<lambda>x. do {ASSERT (FOREACH_cond c x); FOREACH_body f x}) (l, \<sigma>) \<bind>
          (\<lambda>(_, \<sigma>). RETURN \<sigma>))"
proof (induct l arbitrary: \<sigma>)
  case Nil thus ?case by (subst WHILEIT_unfold) (auto simp: FOREACH_cond_def)
next
  case (Cons x ls)
  show ?case
  proof (cases "c \<sigma>")
    case False thus ?thesis
      apply (subst WHILEIT_unfold)
      unfolding FOREACH_cond_def
      by simp
  next
    case [simp]: True
    from Cons show ?thesis
      apply (subst WHILEIT_unfold)
      unfolding FOREACH_cond_def FOREACH_body_def
      apply clarsimp
      apply (rule Refine_Basic.bind_mono)
      apply simp_all
      done
  qed
qed

lemma while_eq_nfoldli: "do {
    (_,\<sigma>) \<leftarrow> WHILE\<^sub>T (FOREACH_cond c) (\<lambda>x. do {ASSERT (FOREACH_cond c x); FOREACH_body f x}) (l,\<sigma>);
    RETURN \<sigma>
  } = nfoldli l c f \<sigma>"
  apply (rule antisym)
  apply (rule while_nfoldli)
  apply (rule order_trans[OF nfoldli_while[where I="\<lambda>_. True"]])
  apply (simp add: WHILET_def)
  done

end