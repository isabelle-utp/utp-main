(*
  File:      PAL.thy
  Author:    Asta Halkjær From

  This work is a formalization of public announcement logic with countably many agents.
  It includes proofs of soundness and completeness for a variant of the axiom system
    PA + DIST! + NEC!.
  The completeness proof builds on the Epistemic Logic theory.
*)

theory PAL imports "Epistemic_Logic.Epistemic_Logic" begin

section \<open>Syntax\<close>

datatype 'i pfm
  = FF ("\<^bold>\<bottom>\<^sub>!")
  | Pro' id ("Pro\<^sub>!")
  | Dis \<open>'i pfm\<close> \<open>'i pfm\<close> (infixr "\<^bold>\<or>\<^sub>!" 30)
  | Con \<open>'i pfm\<close> \<open>'i pfm\<close> (infixr "\<^bold>\<and>\<^sub>!" 35)
  | Imp \<open>'i pfm\<close> \<open>'i pfm\<close> (infixr "\<^bold>\<longrightarrow>\<^sub>!" 25)
  | K' 'i \<open>'i pfm\<close> ("K\<^sub>!")
  | Ann \<open>'i pfm\<close> \<open>'i pfm\<close> ("[_]\<^sub>! _" [50, 50] 50)

abbreviation PIff :: \<open>'i pfm \<Rightarrow> 'i pfm \<Rightarrow> 'i pfm\<close> (infixr "\<^bold>\<longleftrightarrow>\<^sub>!" 25) where
  \<open>p \<^bold>\<longleftrightarrow>\<^sub>! q \<equiv> (p \<^bold>\<longrightarrow>\<^sub>! q) \<^bold>\<and>\<^sub>! (q \<^bold>\<longrightarrow>\<^sub>! p)\<close>

section \<open>Semantics\<close>

fun
  psemantics :: \<open>('i, 'w) kripke \<Rightarrow> 'w \<Rightarrow> 'i pfm \<Rightarrow> bool\<close> ("_, _ \<Turnstile>\<^sub>! _" [50, 50] 50) and
  restrict :: \<open>('i, 'w) kripke \<Rightarrow> 'i pfm \<Rightarrow> ('i, 'w) kripke\<close> where
  \<open>(M, w \<Turnstile>\<^sub>! \<^bold>\<bottom>\<^sub>!) = False\<close>
| \<open>(M, w \<Turnstile>\<^sub>! Pro\<^sub>! x) = \<pi> M w x\<close>
| \<open>(M, w \<Turnstile>\<^sub>! (p \<^bold>\<or>\<^sub>! q)) = ((M, w \<Turnstile>\<^sub>! p) \<or> (M, w \<Turnstile>\<^sub>! q))\<close>
| \<open>(M, w \<Turnstile>\<^sub>! (p \<^bold>\<and>\<^sub>! q)) = ((M, w \<Turnstile>\<^sub>! p) \<and> (M, w \<Turnstile>\<^sub>! q))\<close>
| \<open>(M, w \<Turnstile>\<^sub>! (p \<^bold>\<longrightarrow>\<^sub>! q)) = ((M, w \<Turnstile>\<^sub>! p) \<longrightarrow> (M, w \<Turnstile>\<^sub>! q))\<close>
| \<open>(M, w \<Turnstile>\<^sub>! K\<^sub>! i p) = (\<forall>v \<in> \<K> M i w. M, v \<Turnstile>\<^sub>! p)\<close>
| \<open>(M, w \<Turnstile>\<^sub>! [r]\<^sub>! p) = ((M, w \<Turnstile>\<^sub>! r) \<longrightarrow> (restrict M r, w \<Turnstile>\<^sub>! p))\<close>
| \<open>restrict M p = Kripke (\<pi> M) (\<lambda>i w. {v. v \<in> \<K> M i w \<and> (M, v \<Turnstile>\<^sub>! p)})\<close>

primrec static :: \<open>'i pfm \<Rightarrow> bool\<close> where
  \<open>static \<^bold>\<bottom>\<^sub>! = True\<close>
| \<open>static (Pro\<^sub>! _) = True\<close>
| \<open>static (p \<^bold>\<or>\<^sub>! q) = (static p \<and> static q)\<close>
| \<open>static (p \<^bold>\<and>\<^sub>! q) = (static p \<and> static q)\<close>
| \<open>static (p \<^bold>\<longrightarrow>\<^sub>! q) = (static p \<and> static q)\<close>
| \<open>static (K\<^sub>! i p) = static p\<close>
| \<open>static ([r]\<^sub>! p) = False\<close>

primrec lower :: \<open>'i pfm \<Rightarrow> 'i fm\<close> where
  \<open>lower \<^bold>\<bottom>\<^sub>! = \<^bold>\<bottom>\<close>
| \<open>lower (Pro\<^sub>! x) = Pro x\<close>
| \<open>lower (p \<^bold>\<or>\<^sub>! q) = (lower p \<^bold>\<or> lower q)\<close>
| \<open>lower (p \<^bold>\<and>\<^sub>! q) = (lower p \<^bold>\<and> lower q)\<close>
| \<open>lower (p \<^bold>\<longrightarrow>\<^sub>! q) = (lower p \<^bold>\<longrightarrow> lower q)\<close>
| \<open>lower (K\<^sub>! i p) = K i (lower p)\<close>
| \<open>lower ([r]\<^sub>! p) = undefined\<close>

primrec lift :: \<open>'i fm \<Rightarrow> 'i pfm\<close> where
  \<open>lift \<^bold>\<bottom> = \<^bold>\<bottom>\<^sub>!\<close>
| \<open>lift (Pro x) = Pro\<^sub>! x\<close>
| \<open>lift (p \<^bold>\<or> q) = (lift p \<^bold>\<or>\<^sub>! lift q)\<close>
| \<open>lift (p \<^bold>\<and> q) = (lift p \<^bold>\<and>\<^sub>! lift q)\<close>
| \<open>lift (p \<^bold>\<longrightarrow> q) = (lift p \<^bold>\<longrightarrow>\<^sub>! lift q)\<close>
| \<open>lift (K i p) = K\<^sub>! i (lift p)\<close>

lemma lower_semantics:
  assumes \<open>static p\<close>
  shows \<open>(M, w \<Turnstile> lower p) \<longleftrightarrow> (M, w \<Turnstile>\<^sub>! p)\<close>
  using assms by (induct p arbitrary: w) simp_all

lemma lift_semantics: \<open>(M, w \<Turnstile> p) \<longleftrightarrow> (M, w \<Turnstile>\<^sub>! lift p)\<close>
  by (induct p arbitrary: w) simp_all

lemma lower_lift: \<open>lower (lift p) = p\<close>
  by (induct p) simp_all

lemma lift_lower: \<open>static p \<Longrightarrow> lift (lower p) = p\<close>
  by (induct p) simp_all

section \<open>Soundness of Reduction\<close>

primrec reduce' :: \<open>'i pfm \<Rightarrow> 'i pfm \<Rightarrow> 'i pfm\<close> where
  \<open>reduce' r \<^bold>\<bottom>\<^sub>! = (r \<^bold>\<longrightarrow>\<^sub>! \<^bold>\<bottom>\<^sub>!)\<close>
| \<open>reduce' r (Pro\<^sub>! x) = (r \<^bold>\<longrightarrow>\<^sub>! Pro\<^sub>! x)\<close>
| \<open>reduce' r (p \<^bold>\<or>\<^sub>! q) = (reduce' r p \<^bold>\<or>\<^sub>! reduce' r q)\<close>
| \<open>reduce' r (p \<^bold>\<and>\<^sub>! q) = (reduce' r p \<^bold>\<and>\<^sub>! reduce' r q)\<close>
| \<open>reduce' r (p \<^bold>\<longrightarrow>\<^sub>! q) = (reduce' r p \<^bold>\<longrightarrow>\<^sub>! reduce' r q)\<close>
| \<open>reduce' r (K\<^sub>! i p) = (r \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i (reduce' r p))\<close>
| \<open>reduce' r ([p]\<^sub>! q) = undefined\<close>

primrec reduce :: \<open>'i pfm \<Rightarrow> 'i pfm\<close> where
  \<open>reduce \<^bold>\<bottom>\<^sub>! = \<^bold>\<bottom>\<^sub>!\<close>
| \<open>reduce (Pro\<^sub>! x) = Pro\<^sub>! x\<close>
| \<open>reduce (p \<^bold>\<or>\<^sub>! q) = (reduce p \<^bold>\<or>\<^sub>! reduce q)\<close>
| \<open>reduce (p \<^bold>\<and>\<^sub>! q) = (reduce p \<^bold>\<and>\<^sub>! reduce q)\<close>
| \<open>reduce (p \<^bold>\<longrightarrow>\<^sub>! q) = (reduce p \<^bold>\<longrightarrow>\<^sub>! reduce q)\<close>
| \<open>reduce (K\<^sub>! i p) = K\<^sub>! i (reduce p)\<close>
| \<open>reduce ([r]\<^sub>! p) = reduce' (reduce r) (reduce p)\<close>

lemma static_reduce': \<open>static p \<Longrightarrow> static r \<Longrightarrow> static (reduce' r p)\<close>
  by (induct p) simp_all

lemma static_reduce: \<open>static (reduce p)\<close>
  by (induct p) (simp_all add: static_reduce')

lemma reduce'_semantics:
  assumes \<open>static q\<close>
  shows \<open>((M, w \<Turnstile>\<^sub>! [p]\<^sub>! (q))) = (M, w \<Turnstile>\<^sub>! reduce' p q)\<close>
  using assms by (induct q arbitrary: w) auto

lemma reduce_semantics: \<open>(M, w \<Turnstile>\<^sub>! p) = (M, w \<Turnstile>\<^sub>! reduce p)\<close>
proof (induct p arbitrary: M w)
  case (Ann p q)
  then show ?case
    using reduce'_semantics static_reduce by fastforce
qed auto

section \<open>Proof System\<close>

primrec peval :: \<open>(id \<Rightarrow> bool) \<Rightarrow> ('i pfm \<Rightarrow> bool) \<Rightarrow> 'i pfm \<Rightarrow> bool\<close> where
  \<open>peval _ _ \<^bold>\<bottom>\<^sub>! = False\<close>
| \<open>peval g _ (Pro\<^sub>! x) = g x\<close>
| \<open>peval g h (p \<^bold>\<or>\<^sub>! q) = (peval g h p \<or> peval g h q)\<close>
| \<open>peval g h (p \<^bold>\<and>\<^sub>! q) = (peval g h p \<and> peval g h q)\<close>
| \<open>peval g h (p \<^bold>\<longrightarrow>\<^sub>! q) = (peval g h p \<longrightarrow> peval g h q)\<close>
| \<open>peval _ h (K\<^sub>! i p) = h (K\<^sub>! i p)\<close>
| \<open>peval _ h ([r]\<^sub>! p) = h ([r]\<^sub>! p)\<close>

abbreviation \<open>ptautology p \<equiv> \<forall>g h. peval g h p\<close>

inductive PA :: \<open>'i pfm \<Rightarrow> bool\<close> ("\<turnstile>\<^sub>! _" [50] 50) where
  PA1: \<open>ptautology p \<Longrightarrow> \<turnstile>\<^sub>! p\<close>
| PA2: \<open>\<turnstile>\<^sub>! (K\<^sub>! i p \<^bold>\<and>\<^sub>! K\<^sub>! i (p \<^bold>\<longrightarrow>\<^sub>! q) \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i q)\<close>
| PR1: \<open>\<turnstile>\<^sub>! p \<Longrightarrow> \<turnstile>\<^sub>! (p \<^bold>\<longrightarrow>\<^sub>! q) \<Longrightarrow> \<turnstile>\<^sub>! q\<close>
| PR2: \<open>\<turnstile>\<^sub>! p \<Longrightarrow> \<turnstile>\<^sub>! K\<^sub>! i p\<close>
| PR3: \<open>\<turnstile>\<^sub>! p \<Longrightarrow> \<turnstile>\<^sub>! [r]\<^sub>! p\<close>
| PFF: \<open>\<turnstile>\<^sub>! ([r]\<^sub>! \<^bold>\<bottom>\<^sub>! \<^bold>\<longleftrightarrow>\<^sub>! (r \<^bold>\<longrightarrow>\<^sub>! \<^bold>\<bottom>\<^sub>!))\<close>
| PPro: \<open>\<turnstile>\<^sub>! ([r]\<^sub>! Pro\<^sub>! x \<^bold>\<longleftrightarrow>\<^sub>! (r \<^bold>\<longrightarrow>\<^sub>! Pro\<^sub>! x))\<close>
| PDis: \<open>\<turnstile>\<^sub>! ([r]\<^sub>! (p \<^bold>\<or>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! [r]\<^sub>! p \<^bold>\<or>\<^sub>! [r]\<^sub>! q)\<close>
| PCon: \<open>\<turnstile>\<^sub>! ([r]\<^sub>! (p \<^bold>\<and>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! [r]\<^sub>! p \<^bold>\<and>\<^sub>! [r]\<^sub>! q)\<close>
| PImp: \<open>\<turnstile>\<^sub>! (([r]\<^sub>! (p \<^bold>\<longrightarrow>\<^sub>! q)) \<^bold>\<longleftrightarrow>\<^sub>! ([r]\<^sub>! p \<^bold>\<longrightarrow>\<^sub>! [r]\<^sub>! q))\<close>
| PK: \<open>\<turnstile>\<^sub>! (([r]\<^sub>! K\<^sub>! i p) \<^bold>\<longleftrightarrow>\<^sub>! (r \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i ([r]\<^sub>! p)))\<close>

lemma eval_peval: \<open>eval h (g o lift) p = peval h g (lift p)\<close>
  by (induct p) simp_all

lemma tautology_ptautology: \<open>tautology p \<Longrightarrow> ptautology (lift p)\<close>
  using eval_peval by blast

lemma peval_eval:
  assumes \<open>static p\<close>
  shows \<open>eval h g (lower p) = peval h (g o lower) p\<close>
  using assms by (induct p) simp_all

lemma ptautology_tautology:
  assumes \<open>static p\<close>
  shows \<open>ptautology p \<Longrightarrow> tautology (lower p)\<close>
  using assms peval_eval by blast

theorem SystemK_PAK: \<open>\<turnstile> p \<Longrightarrow> \<turnstile>\<^sub>! lift p\<close>
  by (induct p rule: SystemK.induct) (auto intro: PA.intros(1-5) simp: tautology_ptautology)

theorem static_completeness:
  assumes \<open>static p\<close> \<open>\<forall>(M :: ('i :: countable, 'i fm set) kripke) w. M, w \<Turnstile>\<^sub>! p\<close>
  shows \<open>\<turnstile>\<^sub>! p\<close>
proof -
  have \<open>\<forall>(M :: ('i :: countable, 'i fm set) kripke) w. M, w \<Turnstile> lower p\<close>
    using assms by (simp add: lower_semantics)
  then have \<open>\<turnstile> lower p\<close>
    by (simp add: completeness)
  then have \<open>\<turnstile>\<^sub>! lift (lower p)\<close>
    using SystemK_PAK by fast
  then show ?thesis
    using assms(1) lift_lower by metis
qed

section \<open>Soundness\<close>

lemma peval_semantics: \<open>peval (val w) (\<lambda>q. Kripke val r, w \<Turnstile>\<^sub>! q) p = (Kripke val r, w \<Turnstile>\<^sub>! p)\<close>
  by (induct p) simp_all

lemma ptautology:
  assumes \<open>ptautology p\<close>
  shows \<open>M, w \<Turnstile>\<^sub>! p\<close>
proof -
  from assms have \<open>peval (g w) (\<lambda>q. Kripke g r, w \<Turnstile>\<^sub>! q) p\<close> for g r
    by simp
  then have \<open>Kripke g r, w \<Turnstile>\<^sub>! p\<close> for g r
    using peval_semantics by fast
  then show \<open>M, w \<Turnstile>\<^sub>! p\<close>
    by (metis kripke.collapse)
qed

theorem soundness:
  assumes \<open>\<turnstile>\<^sub>! p\<close>
  shows \<open>M, w \<Turnstile>\<^sub>! p\<close>
  using assms by (induct p arbitrary: M w rule: PA.induct) (simp_all add: ptautology)

section \<open>Completeness\<close>

lemma ConE:
  assumes \<open>\<turnstile>\<^sub>! (p \<^bold>\<and>\<^sub>! q)\<close>
  shows \<open>\<turnstile>\<^sub>! p\<close> \<open>\<turnstile>\<^sub>! q\<close>
  using assms by (metis PA1 PR1 peval.simps(4-5))+

lemma Iff_Dis:
  assumes \<open>\<turnstile>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! p')\<close> \<open>\<turnstile>\<^sub>! (q \<^bold>\<longleftrightarrow>\<^sub>! q')\<close>
  shows \<open>\<turnstile>\<^sub>! ((p \<^bold>\<or>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! (p' \<^bold>\<or>\<^sub>! q'))\<close>
proof -
  have \<open>\<turnstile>\<^sub>! ((p \<^bold>\<longleftrightarrow>\<^sub>! p') \<^bold>\<longrightarrow>\<^sub>! (q \<^bold>\<longleftrightarrow>\<^sub>! q') \<^bold>\<longrightarrow>\<^sub>! ((p \<^bold>\<or>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! (p' \<^bold>\<or>\<^sub>! q')))\<close>
    by (simp add: PA1)
  then show ?thesis
    using assms PR1 by blast
qed

lemma Iff_Con:
  assumes \<open>\<turnstile>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! p')\<close> \<open>\<turnstile>\<^sub>! (q \<^bold>\<longleftrightarrow>\<^sub>! q')\<close>
  shows \<open>\<turnstile>\<^sub>! ((p \<^bold>\<and>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! (p' \<^bold>\<and>\<^sub>! q'))\<close>
proof -
  have \<open>\<turnstile>\<^sub>! ((p \<^bold>\<longleftrightarrow>\<^sub>! p') \<^bold>\<longrightarrow>\<^sub>! (q \<^bold>\<longleftrightarrow>\<^sub>! q') \<^bold>\<longrightarrow>\<^sub>! ((p \<^bold>\<and>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! (p' \<^bold>\<and>\<^sub>! q')))\<close>
    by (simp add: PA1)
  then show ?thesis
    using assms PR1 by blast
qed

lemma Iff_Imp:
  assumes \<open>\<turnstile>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! p')\<close> \<open>\<turnstile>\<^sub>! (q \<^bold>\<longleftrightarrow>\<^sub>! q')\<close>
  shows \<open>\<turnstile>\<^sub>! ((p \<^bold>\<longrightarrow>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! (p' \<^bold>\<longrightarrow>\<^sub>! q'))\<close>
proof -
  have \<open>\<turnstile>\<^sub>! ((p \<^bold>\<longleftrightarrow>\<^sub>! p') \<^bold>\<longrightarrow>\<^sub>! (q \<^bold>\<longleftrightarrow>\<^sub>! q') \<^bold>\<longrightarrow>\<^sub>! ((p \<^bold>\<longrightarrow>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! (p' \<^bold>\<longrightarrow>\<^sub>! q')))\<close>
    by (simp add: PA1)
  then show ?thesis
    using assms PR1 by blast
qed

lemma Iff_sym: \<open>(\<turnstile>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! q)) = (\<turnstile>\<^sub>! (q \<^bold>\<longleftrightarrow>\<^sub>! p))\<close>
proof -
  have \<open>\<turnstile>\<^sub>! ((p \<^bold>\<longleftrightarrow>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! (q \<^bold>\<longleftrightarrow>\<^sub>! p))\<close>
    by (simp add: PA1)
  then show ?thesis
    using PR1 ConE by blast
qed

lemma Iff_Iff:
  assumes \<open>\<turnstile>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! p')\<close> \<open>\<turnstile>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! q)\<close>
  shows \<open>\<turnstile>\<^sub>! (p' \<^bold>\<longleftrightarrow>\<^sub>! q)\<close>
proof -
  have \<open>ptautology ((p \<^bold>\<longleftrightarrow>\<^sub>! p') \<^bold>\<longrightarrow>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! q) \<^bold>\<longrightarrow>\<^sub>! (p' \<^bold>\<longleftrightarrow>\<^sub>! q))\<close>
    by (metis peval.simps(4-5))
  with PA1 have \<open>\<turnstile>\<^sub>! ((p \<^bold>\<longleftrightarrow>\<^sub>! p') \<^bold>\<longrightarrow>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! q) \<^bold>\<longrightarrow>\<^sub>! (p' \<^bold>\<longleftrightarrow>\<^sub>! q))\<close> .
  then show ?thesis
    using assms PR1 by blast
qed

lemma K'_A2': \<open>\<turnstile>\<^sub>! (K\<^sub>! i (p \<^bold>\<longrightarrow>\<^sub>! q) \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i p \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i q)\<close>
proof -
  have \<open>\<turnstile>\<^sub>! (K\<^sub>! i p \<^bold>\<and>\<^sub>! K\<^sub>! i (p \<^bold>\<longrightarrow>\<^sub>! q) \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i q)\<close>
    using PA2 by fast
  moreover have \<open>\<turnstile>\<^sub>! ((P \<^bold>\<and>\<^sub>! Q \<^bold>\<longrightarrow>\<^sub>! R) \<^bold>\<longrightarrow>\<^sub>! (Q \<^bold>\<longrightarrow>\<^sub>! P \<^bold>\<longrightarrow>\<^sub>! R))\<close> for P Q R :: \<open>'i pfm\<close>
    by (simp add: PA1)
  ultimately show ?thesis
    using PR1 by fast
qed

lemma K'_map:
  assumes \<open>\<turnstile>\<^sub>! (p \<^bold>\<longrightarrow>\<^sub>! q)\<close>
  shows \<open>\<turnstile>\<^sub>! (K\<^sub>! i p \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i q)\<close>
proof -
  note \<open>\<turnstile>\<^sub>! (p \<^bold>\<longrightarrow>\<^sub>! q)\<close>
  then have \<open>\<turnstile>\<^sub>! K\<^sub>! i (p \<^bold>\<longrightarrow>\<^sub>! q)\<close>
    using PR2 by fast
  moreover have \<open>\<turnstile>\<^sub>! (K\<^sub>! i (p \<^bold>\<longrightarrow>\<^sub>! q) \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i p \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i q)\<close>
    using K'_A2' by fast
  ultimately show ?thesis
    using PR1 by fast
qed

lemma ConI:
  assumes \<open>\<turnstile>\<^sub>! p\<close> \<open>\<turnstile>\<^sub>! q\<close>
  shows \<open>\<turnstile>\<^sub>! (p \<^bold>\<and>\<^sub>! q)\<close>
proof -
  have \<open>\<turnstile>\<^sub>! (p \<^bold>\<longrightarrow>\<^sub>! q \<^bold>\<longrightarrow>\<^sub>! p \<^bold>\<and>\<^sub>! q)\<close>
    by (simp add: PA1)
  then show ?thesis
    using assms PR1 by blast
qed

lemma Iff_wk:
  assumes \<open>\<turnstile>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! q)\<close>
  shows \<open>\<turnstile>\<^sub>! ((r \<^bold>\<longrightarrow>\<^sub>! p) \<^bold>\<longleftrightarrow>\<^sub>! (r \<^bold>\<longrightarrow>\<^sub>! q))\<close>
proof -
  have \<open>\<turnstile>\<^sub>! ((p \<^bold>\<longleftrightarrow>\<^sub>! q) \<^bold>\<longrightarrow>\<^sub>! ((r \<^bold>\<longrightarrow>\<^sub>! p) \<^bold>\<longleftrightarrow>\<^sub>! (r \<^bold>\<longrightarrow>\<^sub>! q)))\<close>
    by (simp add: PA1)
  then show ?thesis
    using assms PR1 by blast
qed

lemma Iff_reduce':
  assumes \<open>static p\<close>
  shows \<open>\<turnstile>\<^sub>! ([r]\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! reduce' r p)\<close>
  using assms
proof (induct p rule: pfm.induct)
  case FF
  then show ?case
    by (simp add: PFF)
next
  case (Pro' x)
  then show ?case
    by (simp add: PPro)
next
  case (Dis p q)
  then have \<open>\<turnstile>\<^sub>! ([r]\<^sub>! p \<^bold>\<or>\<^sub>! [r]\<^sub>! q \<^bold>\<longleftrightarrow>\<^sub>! reduce' r (p \<^bold>\<or>\<^sub>! q))\<close>
    using Iff_Dis by force
  moreover have \<open>\<turnstile>\<^sub>! (([r]\<^sub>! p \<^bold>\<or>\<^sub>! [r]\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! ([r]\<^sub>! (p \<^bold>\<or>\<^sub>! q)))\<close>
    using PDis Iff_sym by fastforce
  ultimately show ?case
    using PA1 PR1 Iff_Iff by blast
next
  case (Con p q)
  then have \<open>\<turnstile>\<^sub>! ([r]\<^sub>! p \<^bold>\<and>\<^sub>! [r]\<^sub>! q \<^bold>\<longleftrightarrow>\<^sub>! reduce' r (p \<^bold>\<and>\<^sub>! q))\<close>
    using Iff_Con by force
  moreover have \<open>\<turnstile>\<^sub>! (([r]\<^sub>! p \<^bold>\<and>\<^sub>! [r]\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! ([r]\<^sub>! (p \<^bold>\<and>\<^sub>! q)))\<close>
    using PCon Iff_sym by fastforce
  ultimately show ?case
    using PA1 PR1 Iff_Iff by blast
next
  case (Imp p q)
  then have \<open>\<turnstile>\<^sub>! (([r]\<^sub>! p \<^bold>\<longrightarrow>\<^sub>! [r]\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! reduce' r (p \<^bold>\<longrightarrow>\<^sub>! q))\<close>
    using Iff_Imp by force
  moreover have \<open>\<turnstile>\<^sub>! (([r]\<^sub>! p \<^bold>\<longrightarrow>\<^sub>! [r]\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! ([r]\<^sub>! (p \<^bold>\<longrightarrow>\<^sub>! q)))\<close>
    using PImp Iff_sym by fastforce
  ultimately show ?case
    using PA1 PR1 Iff_Iff by blast
next
  case (K' i p)
  then have \<open>\<turnstile>\<^sub>! ([r]\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! reduce' r p)\<close>
    by simp
  then have \<open>\<turnstile>\<^sub>! (K\<^sub>! i ([r]\<^sub>! p) \<^bold>\<longleftrightarrow>\<^sub>! K\<^sub>! i (reduce' r p))\<close>
    using K'_map ConE ConI by metis
  moreover have \<open>\<turnstile>\<^sub>! ([r]\<^sub>! K\<^sub>! i p \<^bold>\<longleftrightarrow>\<^sub>! r \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i ([r]\<^sub>! p))\<close>
    using PK .
  ultimately have \<open>\<turnstile>\<^sub>! ([r]\<^sub>! K\<^sub>! i p \<^bold>\<longleftrightarrow>\<^sub>! r \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i (reduce' r p))\<close>
    by (meson Iff_Iff Iff_sym Iff_wk)
  then show ?case
    by simp
next
  case (Ann r p)
  then show ?case
    by simp
qed

lemma Iff_Ann1:
  assumes r: \<open>\<turnstile>\<^sub>! (r \<^bold>\<longleftrightarrow>\<^sub>! r')\<close> and \<open>static p\<close>
  shows \<open>\<turnstile>\<^sub>! ([r]\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! [r']\<^sub>! p)\<close>
  using assms(2-)
proof (induct p)
  case FF
  have \<open>\<turnstile>\<^sub>! ((r \<^bold>\<longleftrightarrow>\<^sub>! r') \<^bold>\<longrightarrow>\<^sub>! ((r \<^bold>\<longrightarrow>\<^sub>! \<^bold>\<bottom>\<^sub>!) \<^bold>\<longleftrightarrow>\<^sub>! (r' \<^bold>\<longrightarrow>\<^sub>! \<^bold>\<bottom>\<^sub>!)))\<close>
    by (auto intro: PA1)
  then have \<open>\<turnstile>\<^sub>! ((r \<^bold>\<longrightarrow>\<^sub>! \<^bold>\<bottom>\<^sub>!) \<^bold>\<longleftrightarrow>\<^sub>! (r' \<^bold>\<longrightarrow>\<^sub>! \<^bold>\<bottom>\<^sub>!))\<close>
    using r PR1 by blast
  then show ?case
    by (meson PFF Iff_Iff Iff_sym)
next
  case (Pro' x)
  have \<open>\<turnstile>\<^sub>! ((r \<^bold>\<longleftrightarrow>\<^sub>! r') \<^bold>\<longrightarrow>\<^sub>! ((r \<^bold>\<longrightarrow>\<^sub>! Pro\<^sub>! x) \<^bold>\<longleftrightarrow>\<^sub>! (r' \<^bold>\<longrightarrow>\<^sub>! Pro\<^sub>! x)))\<close>
    by (auto intro: PA1)
  then have \<open>\<turnstile>\<^sub>! ((r \<^bold>\<longrightarrow>\<^sub>! Pro\<^sub>! x) \<^bold>\<longleftrightarrow>\<^sub>! (r' \<^bold>\<longrightarrow>\<^sub>! Pro\<^sub>! x))\<close>
    using r PR1 by blast
  then show ?case
    by (meson PPro Iff_Iff Iff_sym)
next
  case (Dis p q)
  then have \<open>\<turnstile>\<^sub>! ([r]\<^sub>! p \<^bold>\<or>\<^sub>! [r]\<^sub>! q \<^bold>\<longleftrightarrow>\<^sub>! [r']\<^sub>! p \<^bold>\<or>\<^sub>! [r']\<^sub>! q)\<close>
    by (simp add: Iff_Dis)
  then show ?case
    by (meson PDis Iff_Iff Iff_sym)
next
  case (Con p q)
  then have \<open>\<turnstile>\<^sub>! ([r]\<^sub>! p \<^bold>\<and>\<^sub>! [r]\<^sub>! q \<^bold>\<longleftrightarrow>\<^sub>! [r']\<^sub>! p \<^bold>\<and>\<^sub>! [r']\<^sub>! q)\<close>
    by (simp add: Iff_Con)
  then show ?case
    by (meson PCon Iff_Iff Iff_sym)
next
  case (Imp p q)
  then have \<open>\<turnstile>\<^sub>! (([r]\<^sub>! p \<^bold>\<longrightarrow>\<^sub>! [r]\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! ([r']\<^sub>! p \<^bold>\<longrightarrow>\<^sub>! [r']\<^sub>! q))\<close>
    by (simp add: Iff_Imp)
  then show ?case
    by (meson PImp Iff_Iff Iff_sym)
next
  case (K' i p)
  then have \<open>\<turnstile>\<^sub>! ([r]\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! [r']\<^sub>! p)\<close>
    by simp
  then have \<open>\<turnstile>\<^sub>! (K\<^sub>! i ([r]\<^sub>! p) \<^bold>\<longleftrightarrow>\<^sub>! K\<^sub>! i ([r']\<^sub>! p))\<close>
    using K'_map ConE ConI by metis
  then show ?case
    by (meson Iff_Iff Iff_Imp Iff_sym PK r)
next
  case (Ann s p)
  then show ?case
    by simp
qed

lemma Iff_Ann2:
  assumes \<open>\<turnstile>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! p')\<close>
  shows \<open>\<turnstile>\<^sub>! ([r]\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! [r]\<^sub>! p')\<close>
  using assms ConE ConI PImp PR1 PR3 by metis

lemma Iff_reduce: \<open>\<turnstile>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! reduce p)\<close>
proof (induct p)
  case (Dis p q)
  then show ?case
    by (simp add: Iff_Dis)
next
  case (Con p q)
  then show ?case
    by (simp add: Iff_Con)
next
  case (Imp p q)
  then show ?case
    by (simp add: Iff_Imp)
next
  case (K' i p)
  have
    \<open>\<turnstile>\<^sub>! (K\<^sub>! i p \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i (reduce p))\<close>
    \<open>\<turnstile>\<^sub>! (K\<^sub>! i (reduce p) \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i p)\<close>
    using K' K'_map ConE by fast+
  then have \<open>\<turnstile>\<^sub>! (K\<^sub>! i p \<^bold>\<longleftrightarrow>\<^sub>! K\<^sub>! i (reduce p))\<close>
    using ConI by blast
  then show ?case
    by simp
next
  case (Ann r p)
  have \<open>\<turnstile>\<^sub>! ([reduce r]\<^sub>! reduce p \<^bold>\<longleftrightarrow>\<^sub>! reduce' (reduce r) (reduce p))\<close>
    using Iff_reduce' static_reduce by blast
  moreover have \<open>\<turnstile>\<^sub>! ([r]\<^sub>! reduce p \<^bold>\<longleftrightarrow>\<^sub>! [reduce r]\<^sub>! reduce p)\<close>
    using Ann(1) Iff_Ann1 static_reduce by blast
  ultimately have \<open>\<turnstile>\<^sub>! ([r]\<^sub>! reduce p \<^bold>\<longleftrightarrow>\<^sub>! reduce' (reduce r) (reduce p))\<close>
    using Iff_Iff Iff_sym by blast
  moreover have \<open>\<turnstile>\<^sub>! ([r]\<^sub>! reduce p \<^bold>\<longleftrightarrow>\<^sub>! [r]\<^sub>! p)\<close>
    by (meson Ann(2) static_reduce Iff_Ann2 Iff_sym)
  ultimately have \<open>\<turnstile>\<^sub>! ([r]\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! reduce' (reduce r) (reduce p))\<close>
    using Iff_Iff by blast
  then show ?case
    by simp
qed (simp_all add: PA1)

theorem completeness:
  assumes \<open>\<forall>(M :: ('i :: countable, 'i fm set) kripke) w. M, w \<Turnstile>\<^sub>! p\<close>
  shows \<open>\<turnstile>\<^sub>! p\<close>
proof -
  have \<open>\<forall>(M :: ('i :: countable, 'i fm set) kripke) w. M, w \<Turnstile>\<^sub>! reduce p\<close>
    using assms reduce_semantics by fast
  moreover have \<open>static (reduce p)\<close>
    using static_reduce by fast
  ultimately have \<open>\<turnstile>\<^sub>! reduce p\<close>
    using static_completeness by blast
  moreover have \<open>\<turnstile>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! reduce p)\<close>
    using Iff_reduce by blast
  ultimately show ?thesis
    using ConE(2) PR1 by blast
qed

end
