(* Title: Computational_Model.thy
  Author: Andreas Lochbihler, ETH Zurich *)

section \<open>Oracle combinators\<close>

theory Computational_Model imports 
  Generative_Probabilistic_Value
begin

type_synonym security = nat
type_synonym advantage = "security \<Rightarrow> real"

type_synonym ('\<sigma>, 'call, 'ret) oracle' = "'\<sigma> \<Rightarrow> 'call \<Rightarrow> ('ret \<times> '\<sigma>) spmf"
type_synonym ('\<sigma>, 'call, 'ret) "oracle" = "security \<Rightarrow> ('\<sigma>, 'call, 'ret) oracle' \<times> '\<sigma>"

print_translation \<comment> \<open>pretty printing for @{typ "('\<sigma>, 'call, 'ret) oracle"}\<close> \<open>
  let
    fun tr' [Const (@{type_syntax nat}, _), 
      Const (@{type_syntax prod}, _) $ 
        (Const (@{type_syntax fun}, _) $ s1 $ 
          (Const (@{type_syntax fun}, _) $ call $
            (Const (@{type_syntax pmf}, _) $
              (Const (@{type_syntax option}, _) $
                (Const (@{type_syntax prod}, _) $ ret $ s2))))) $
        s3] =
      if s1 = s2 andalso s1 = s3 then Syntax.const @{type_syntax oracle} $ s1 $ call $ ret
      else raise Match;
  in [(@{type_syntax "fun"}, K tr')]
  end
\<close>
typ "('\<sigma>, 'call, 'ret) oracle"

subsection \<open>Shared state\<close>

context includes \<I>.lifting lifting_syntax begin

lift_definition plus_\<I> :: "('out, 'ret) \<I> \<Rightarrow> ('out', 'ret') \<I> \<Rightarrow> ('out + 'out', 'ret + 'ret') \<I>" (infix "\<oplus>\<^sub>\<I>" 500)
is "\<lambda>resp1 resp2. \<lambda>out. case out of Inl out' \<Rightarrow> Inl ` resp1 out' | Inr out' \<Rightarrow> Inr ` resp2 out'" .

lemma plus_\<I>_sel [simp]:
  shows outs_plus_\<I>: "outs_\<I> (plus_\<I> \<I>l \<I>r) = outs_\<I> \<I>l <+> outs_\<I> \<I>r"
  and responses_plus_\<I>_Inl: "responses_\<I> (plus_\<I> \<I>l \<I>r) (Inl x) = Inl ` responses_\<I> \<I>l x"
  and responses_plus_\<I>_Inr: "responses_\<I> (plus_\<I> \<I>l \<I>r) (Inr y) = Inr ` responses_\<I> \<I>r y"
by(transfer; auto split: sum.split_asm; fail)+

lemma vimage_Inl_Plus [simp]: "Inl -` (A <+> B) = A" 
  and vimage_Inr_Plus [simp]: "Inr -` (A <+> B) = B"
by auto

lemma vimage_Inl_image_Inr: "Inl -` Inr ` A = {}"
  and vimage_Inr_image_Inl: "Inr -` Inl ` A = {}"
by auto

lemma plus_\<I>_parametric [transfer_rule]:
  "(rel_\<I> C R ===> rel_\<I> C' R' ===> rel_\<I> (rel_sum C C') (rel_sum R R')) plus_\<I> plus_\<I>"
apply(rule rel_funI rel_\<I>I)+
subgoal premises [transfer_rule] by(simp; rule conjI; transfer_prover)
apply(erule rel_sum.cases; clarsimp simp add: inj_vimage_image_eq vimage_Inl_image_Inr empty_transfer vimage_Inr_image_Inl)
subgoal premises [transfer_rule] by transfer_prover
subgoal premises [transfer_rule] by transfer_prover
done

lifting_update \<I>.lifting
lifting_forget \<I>.lifting

lemma \<I>_trivial_plus_\<I> [simp]: "\<I>_trivial (\<I>\<^sub>1 \<oplus>\<^sub>\<I> \<I>\<^sub>2) \<longleftrightarrow> \<I>_trivial \<I>\<^sub>1 \<and> \<I>_trivial \<I>\<^sub>2"
by(auto simp add: \<I>_trivial_def)

end

lemma map_\<I>_plus_\<I> [simp]: 
  "map_\<I> (map_sum f1 f2) (map_sum g1 g2) (\<I>1 \<oplus>\<^sub>\<I> \<I>2) = map_\<I> f1 g1 \<I>1 \<oplus>\<^sub>\<I> map_\<I> f2 g2 \<I>2"
proof(rule \<I>_eqI[OF Set.set_eqI], goal_cases)
  case (1 x)
  then show ?case by(cases x) auto
qed (auto simp add: image_image)

lemma le_plus_\<I>_iff [simp]:
  "\<I>1 \<oplus>\<^sub>\<I> \<I>2 \<le> \<I>1' \<oplus>\<^sub>\<I> \<I>2' \<longleftrightarrow> \<I>1 \<le> \<I>1' \<and> \<I>2 \<le> \<I>2'"
  by(auto 4 4 simp add: le_\<I>_def dest: bspec[where x="Inl _"] bspec[where x="Inr _"])

lemma \<I>_full_le_plus_\<I>: "\<I>_full \<le> plus_\<I> \<I>1 \<I>2" if "\<I>_full \<le> \<I>1" "\<I>_full \<le> \<I>2"
  using that by(auto simp add: le_\<I>_def top_unique)

lemma plus_\<I>_mono: "plus_\<I> \<I>1 \<I>2 \<le> plus_\<I> \<I>1' \<I>2'" if "\<I>1 \<le> \<I>1'" "\<I>2 \<le> \<I>2'" 
  using that by(fastforce simp add: le_\<I>_def)

context
  fixes left :: "('s, 'a, 'b) oracle'"
  and right :: "('s,'c, 'd) oracle'"
  and s :: "'s"
begin

primrec plus_oracle :: "'a + 'c \<Rightarrow> (('b + 'd) \<times> 's) spmf"
where
  "plus_oracle (Inl a) = map_spmf (apfst Inl) (left s a)"
| "plus_oracle (Inr b) = map_spmf (apfst Inr) (right s b)"

lemma lossless_plus_oracleI [intro, simp]:
  "\<lbrakk> \<And>a. x = Inl a \<Longrightarrow> lossless_spmf (left s a); 
     \<And>b. x = Inr b \<Longrightarrow> lossless_spmf (right s b) \<rbrakk>
  \<Longrightarrow> lossless_spmf (plus_oracle x)"
by(cases x) simp_all

lemma plus_oracle_split:
  "P (plus_oracle lr) \<longleftrightarrow>
  (\<forall>x. lr = Inl x \<longrightarrow> P (map_spmf (apfst Inl) (left s x))) \<and>
  (\<forall>y. lr = Inr y \<longrightarrow> P (map_spmf (apfst Inr) (right s y)))"
by(cases lr) auto

lemma plus_oracle_split_asm:
  "P (plus_oracle lr) \<longleftrightarrow>
  \<not> ((\<exists>x. lr = Inl x \<and> \<not> P (map_spmf (apfst Inl) (left s x))) \<or>
     (\<exists>y. lr = Inr y \<and> \<not> P (map_spmf (apfst Inr) (right s y))))"
by(cases lr) auto

end

notation plus_oracle (infix "\<oplus>\<^sub>O" 500)

context
  fixes left :: "('s, 'a, 'b) oracle'"
  and right :: "('s,'c, 'd) oracle'"
begin

lemma WT_plus_oracleI [intro!]:
  "\<lbrakk> \<I>l \<turnstile>c left s \<surd>; \<I>r \<turnstile>c right s \<surd> \<rbrakk> \<Longrightarrow> \<I>l \<oplus>\<^sub>\<I> \<I>r \<turnstile>c (left \<oplus>\<^sub>O right) s \<surd>"
by(rule WT_calleeI)(auto elim!: WT_calleeD simp add: inj_image_mem_iff)

lemma WT_plus_oracleD1:
  assumes "\<I>l \<oplus>\<^sub>\<I> \<I>r \<turnstile>c (left \<oplus>\<^sub>O right) s \<surd> " (is "?\<I> \<turnstile>c ?callee s \<surd>")
  shows "\<I>l \<turnstile>c left s \<surd>"
proof(rule WT_calleeI)
  fix call ret s'
  assume "call \<in> outs_\<I> \<I>l" "(ret, s') \<in> set_spmf (left s call)"
  hence "(Inl ret, s') \<in> set_spmf (?callee s (Inl call))" "Inl call \<in> outs_\<I> (\<I>l \<oplus>\<^sub>\<I> \<I>r)"
    by(auto intro: rev_image_eqI)
  hence "Inl ret \<in> responses_\<I> ?\<I> (Inl call)" by(rule WT_calleeD[OF assms])
  then show "ret \<in> responses_\<I> \<I>l call" by(simp add: inj_image_mem_iff)
qed

lemma WT_plus_oracleD2:
  assumes "\<I>l \<oplus>\<^sub>\<I> \<I>r \<turnstile>c (left \<oplus>\<^sub>O right) s \<surd> " (is "?\<I> \<turnstile>c ?callee s \<surd>")
  shows "\<I>r \<turnstile>c right s \<surd>"
proof(rule WT_calleeI)
  fix call ret s'
  assume "call \<in> outs_\<I> \<I>r" "(ret, s') \<in> set_spmf (right s call)"
  hence "(Inr ret, s') \<in> set_spmf (?callee s (Inr call))" "Inr call \<in> outs_\<I> (\<I>l \<oplus>\<^sub>\<I> \<I>r)"
    by(auto intro: rev_image_eqI)
  hence "Inr ret \<in> responses_\<I> ?\<I> (Inr call)" by(rule WT_calleeD[OF assms])
  then show "ret \<in> responses_\<I> \<I>r call" by(simp add: inj_image_mem_iff)
qed

lemma WT_plus_oracle_iff [simp]: "\<I>l \<oplus>\<^sub>\<I> \<I>r \<turnstile>c (left \<oplus>\<^sub>O right) s \<surd> \<longleftrightarrow> \<I>l \<turnstile>c left s \<surd> \<and> \<I>r \<turnstile>c right s \<surd>"
by(blast dest: WT_plus_oracleD1 WT_plus_oracleD2)

lemma callee_invariant_on_plus_oracle [simp]:
  "callee_invariant_on (left \<oplus>\<^sub>O right) I (\<I>l \<oplus>\<^sub>\<I> \<I>r) \<longleftrightarrow>
   callee_invariant_on left I \<I>l \<and> callee_invariant_on right I \<I>r"
   (is "?lhs \<longleftrightarrow> ?rhs")
proof(intro iffI conjI)
  assume ?lhs
  then interpret plus: callee_invariant_on "left \<oplus>\<^sub>O right" I "\<I>l \<oplus>\<^sub>\<I> \<I>r" .
  show "callee_invariant_on left I \<I>l"
  proof
    fix s x y s'
    assume "(y, s') \<in> set_spmf (left s x)" and "I s" and "x \<in> outs_\<I> \<I>l"
    then have "(Inl y, s') \<in> set_spmf ((left \<oplus>\<^sub>O right) s (Inl x))"
      by(auto intro: rev_image_eqI)
    then show "I s'" using \<open>I s\<close> by(rule plus.callee_invariant)(simp add: \<open>x \<in> outs_\<I> \<I>l\<close>)
  next
    show "\<I>l \<turnstile>c left s \<surd>" if "I s" for s using plus.WT_callee[OF that] by simp
  qed
  show "callee_invariant_on right I \<I>r"
  proof
    fix s x y s'
    assume "(y, s') \<in> set_spmf (right s x)" and "I s" and "x \<in> outs_\<I> \<I>r"
    then have "(Inr y, s') \<in> set_spmf ((left \<oplus>\<^sub>O right) s (Inr x))"
      by(auto intro: rev_image_eqI)
    then show "I s'" using \<open>I s\<close> by(rule plus.callee_invariant)(simp add: \<open>x \<in> outs_\<I> \<I>r\<close>)
  next
    show "\<I>r \<turnstile>c right s \<surd>" if "I s" for s using plus.WT_callee[OF that] by simp
  qed
next
  assume ?rhs
  interpret left: callee_invariant_on left I \<I>l using \<open>?rhs\<close> by simp
  interpret right: callee_invariant_on right I \<I>r using \<open>?rhs\<close> by simp
  show ?lhs
  proof
    fix s x y s'
    assume "(y, s') \<in> set_spmf ((left \<oplus>\<^sub>O right) s x)" and "I s" and "x \<in> outs_\<I> (\<I>l \<oplus>\<^sub>\<I> \<I>r)"
    then have "(projl y, s') \<in> set_spmf (left s (projl x)) \<and> projl x \<in> outs_\<I> \<I>l \<or>
      (projr y, s') \<in> set_spmf (right s (projr x)) \<and> projr x \<in> outs_\<I> \<I>r"
      by (cases x)  auto
    then show "I s'" using \<open>I s\<close> 
      by (auto dest: left.callee_invariant right.callee_invariant)
  next
    show "\<I>l \<oplus>\<^sub>\<I> \<I>r \<turnstile>c (left \<oplus>\<^sub>O right) s \<surd>" if "I s" for s 
      using left.WT_callee[OF that] right.WT_callee[OF that] by simp
  qed
qed

lemma callee_invariant_plus_oracle [simp]:
  "callee_invariant (left \<oplus>\<^sub>O right) I \<longleftrightarrow>
   callee_invariant left I \<and> callee_invariant right I"
  (is "?lhs \<longleftrightarrow>  ?rhs")
proof -
  have "?lhs \<longleftrightarrow> callee_invariant_on (left \<oplus>\<^sub>O right) I (\<I>_full \<oplus>\<^sub>\<I> \<I>_full)"
    by(rule callee_invariant_on_cong)(auto split: plus_oracle_split_asm)
  also have "\<dots> \<longleftrightarrow> ?rhs" by(rule callee_invariant_on_plus_oracle)
  finally show ?thesis .
qed

lemma plus_oracle_parametric [transfer_rule]:
  includes lifting_syntax shows
  "((S ===> A ===> rel_spmf (rel_prod B S))
   ===> (S ===> C ===> rel_spmf (rel_prod D S))
   ===> S ===> rel_sum A C ===> rel_spmf (rel_prod (rel_sum B D) S))
   plus_oracle plus_oracle"
unfolding plus_oracle_def[abs_def] by transfer_prover

lemma rel_spmf_plus_oracle:
  "\<lbrakk> \<And>q1' q2'. \<lbrakk> q1 = Inl q1'; q2 = Inl q2' \<rbrakk> \<Longrightarrow> rel_spmf (rel_prod B S) (left1 s1 q1') (left2 s2 q2');
    \<And>q1' q2'. \<lbrakk> q1 = Inr q1'; q2 = Inr q2' \<rbrakk> \<Longrightarrow> rel_spmf (rel_prod D S) (right1 s1 q1') (right2 s2 q2');
    S s1 s2; rel_sum A C q1 q2 \<rbrakk>
  \<Longrightarrow> rel_spmf (rel_prod (rel_sum B D) S) ((left1 \<oplus>\<^sub>O right1) s1 q1) ((left2 \<oplus>\<^sub>O right2) s2 q2)"
apply(erule rel_sum.cases; clarsimp)
 apply(erule meta_allE)+
 apply(erule meta_impE, rule refl)+
 subgoal premises [transfer_rule] by transfer_prover
apply(erule meta_allE)+
apply(erule meta_impE, rule refl)+
subgoal premises [transfer_rule] by transfer_prover
done

end

subsection \<open>Shared state with aborts\<close>

context
  fixes left :: "('s, 'a, 'b option) oracle'"
  and right :: "('s,'c, 'd option) oracle'"
  and s :: "'s"
begin

primrec plus_oracle_stop :: "'a + 'c \<Rightarrow> (('b + 'd) option \<times> 's) spmf"
where
  "plus_oracle_stop (Inl a) = map_spmf (apfst (map_option Inl)) (left s a)"
| "plus_oracle_stop (Inr b) = map_spmf (apfst (map_option Inr)) (right s b)"

lemma lossless_plus_oracle_stopI [intro, simp]:
  "\<lbrakk> \<And>a. x = Inl a \<Longrightarrow> lossless_spmf (left s a); 
     \<And>b. x = Inr b \<Longrightarrow> lossless_spmf (right s b) \<rbrakk>
  \<Longrightarrow> lossless_spmf (plus_oracle_stop x)"
by(cases x) simp_all

lemma plus_oracle_stop_split:
  "P (plus_oracle_stop lr) \<longleftrightarrow>
  (\<forall>x. lr = Inl x \<longrightarrow> P (map_spmf (apfst (map_option Inl)) (left s x))) \<and>
  (\<forall>y. lr = Inr y \<longrightarrow> P (map_spmf (apfst (map_option Inr)) (right s y)))"
by(cases lr) auto

lemma plus_oracle_stop_split_asm:
  "P (plus_oracle_stop lr) \<longleftrightarrow>
  \<not> ((\<exists>x. lr = Inl x \<and> \<not> P (map_spmf (apfst (map_option Inl)) (left s x))) \<or>
     (\<exists>y. lr = Inr y \<and> \<not> P (map_spmf (apfst (map_option Inr)) (right s y))))"
by(cases lr) auto

end

notation plus_oracle_stop (infix "\<oplus>\<^sub>O\<^sup>S" 500)

subsection \<open>Disjoint state\<close>

context
  fixes left :: "('s1, 'a, 'b) oracle'"
  and right :: "('s2, 'c, 'd) oracle'"
begin

fun parallel_oracle :: "('s1 \<times> 's2, 'a + 'c, 'b + 'd) oracle'"
where
  "parallel_oracle (s1, s2) (Inl a) = map_spmf (map_prod Inl (\<lambda>s1'. (s1', s2))) (left s1 a)"
| "parallel_oracle (s1, s2) (Inr b) = map_spmf (map_prod Inr (Pair s1)) (right s2 b)"

lemma parallel_oracle_def:
  "parallel_oracle = (\<lambda>(s1, s2). case_sum (\<lambda>a. map_spmf (map_prod Inl (\<lambda>s1'. (s1', s2))) (left s1 a)) (\<lambda>b. map_spmf (map_prod Inr (Pair s1)) (right s2 b)))"
by(auto intro!: ext split: sum.split)

lemma lossless_parallel_oracle [simp]:
  "lossless_spmf (parallel_oracle s12 xy) \<longleftrightarrow>
   (\<forall>x. xy = Inl x \<longrightarrow> lossless_spmf (left (fst s12) x)) \<and>
   (\<forall>y. xy = Inr y \<longrightarrow> lossless_spmf (right (snd s12) y))"
by(cases s12; cases xy) simp_all

lemma parallel_oracle_split:
  "P (parallel_oracle s1s2 lr) \<longleftrightarrow>
  (\<forall>s1 s2 x. s1s2 = (s1, s2) \<longrightarrow> lr = Inl x \<longrightarrow> P (map_spmf (map_prod Inl (\<lambda>s1'. (s1', s2))) (left s1 x))) \<and>
  (\<forall>s1 s2 y. s1s2 = (s1, s2) \<longrightarrow> lr = Inr y \<longrightarrow> P (map_spmf (map_prod Inr (Pair s1)) (right s2 y)))"
by(cases s1s2; cases lr) auto

lemma parallel_oracle_split_asm:
  "P (parallel_oracle s1s2 lr) \<longleftrightarrow>
  \<not> ((\<exists>s1 s2 x. s1s2 = (s1, s2) \<and> lr = Inl x \<and> \<not> P (map_spmf (map_prod Inl (\<lambda>s1'. (s1', s2))) (left s1 x))) \<or>
     (\<exists>s1 s2 y. s1s2 = (s1, s2) \<and> lr = Inr y \<and> \<not> P (map_spmf (map_prod Inr (Pair s1)) (right s2 y))))"
by(cases s1s2; cases lr) auto

lemma WT_parallel_oracle [intro!, simp]:
  "\<lbrakk> \<I>l \<turnstile>c left sl \<surd>; \<I>r \<turnstile>c right sr \<surd> \<rbrakk> \<Longrightarrow> plus_\<I> \<I>l \<I>r \<turnstile>c parallel_oracle (sl, sr) \<surd>"
by(rule WT_calleeI)(auto elim!: WT_calleeD simp add: inj_image_mem_iff)

lemma callee_invariant_parallel_oracleI [simp, intro]:
  assumes "callee_invariant_on left Il \<I>l" "callee_invariant_on right Ir \<I>r"
  shows "callee_invariant_on parallel_oracle (pred_prod Il Ir) (\<I>l \<oplus>\<^sub>\<I> \<I>r)"
proof
  interpret left: callee_invariant_on left Il \<I>l by fact
  interpret right: callee_invariant_on right Ir \<I>r by fact

  show "pred_prod Il Ir s12'"
    if "(y, s12') \<in> set_spmf (parallel_oracle s12 x)" and "pred_prod Il Ir s12" and "x \<in> outs_\<I> (\<I>l \<oplus>\<^sub>\<I> \<I>r)"
    for s12 x y s12' using that
    by(cases s12; cases s12; cases x)(auto dest: left.callee_invariant right.callee_invariant)

  show "\<I>l \<oplus>\<^sub>\<I> \<I>r \<turnstile>c local.parallel_oracle s \<surd>" if "pred_prod Il Ir s" for s using that
    by(cases s)(simp add: left.WT_callee right.WT_callee)
qed

end

lemma parallel_oracle_parametric:
  includes lifting_syntax shows
  "((S1 ===> CALL1 ===> rel_spmf (rel_prod (=) S1)) 
  ===> (S2 ===> CALL2 ===> rel_spmf (rel_prod (=) S2))
  ===> rel_prod S1 S2 ===> rel_sum CALL1 CALL2 ===> rel_spmf (rel_prod (=) (rel_prod S1 S2)))
  parallel_oracle parallel_oracle"
unfolding parallel_oracle_def[abs_def] by (fold relator_eq)transfer_prover

subsection \<open>Indexed oracles\<close>

definition family_oracle :: "('i \<Rightarrow> ('s, 'a, 'b) oracle') \<Rightarrow> ('i \<Rightarrow> 's, 'i \<times> 'a, 'b) oracle'"
where "family_oracle f s = (\<lambda>(i, x). map_spmf (\<lambda>(y, s'). (y, s(i := s'))) (f i (s i) x))"

lemma family_oracle_apply [simp]:
  "family_oracle f s (i, x) = map_spmf (apsnd (fun_upd s i)) (f i (s i) x)"
by(simp add: family_oracle_def apsnd_def map_prod_def)

lemma lossless_family_oracle:
  "lossless_spmf (family_oracle f s ix) \<longleftrightarrow> lossless_spmf (f (fst ix) (s (fst ix)) (snd ix))"
by(simp add: family_oracle_def split_beta)

subsection \<open>State extension\<close>

definition extend_state_oracle :: "('call, 'ret, 's) callee \<Rightarrow> ('call, 'ret, 's' \<times> 's) callee" ("\<dagger>_" [1000] 1000)
where "extend_state_oracle callee = (\<lambda>(s', s) x. map_spmf (\<lambda>(y, s). (y, (s', s))) (callee s x))"

lemma extend_state_oracle_simps [simp]:
  "extend_state_oracle callee (s', s) x = map_spmf (\<lambda>(y, s). (y, (s', s))) (callee s x)"
by(simp add: extend_state_oracle_def)

context includes lifting_syntax begin
lemma extend_state_oracle_parametric [transfer_rule]:
  "((S ===> C ===> rel_spmf (rel_prod R S)) ===> rel_prod S' S ===> C ===> rel_spmf (rel_prod R (rel_prod S' S)))
  extend_state_oracle extend_state_oracle"
unfolding extend_state_oracle_def[abs_def] by transfer_prover

lemma extend_state_oracle_transfer:
  "((S ===> C ===> rel_spmf (rel_prod R S)) 
  ===> rel_prod2 S ===> C ===> rel_spmf (rel_prod R (rel_prod2 S)))
  (\<lambda>oracle. oracle) extend_state_oracle"
unfolding extend_state_oracle_def[abs_def]
apply(rule rel_funI)+
apply clarsimp
apply(drule (1) rel_funD)+
apply(auto simp add: spmf_rel_map split_def dest: rel_funD intro: rel_spmf_mono)
done
end

lemma callee_invariant_extend_state_oracle_const [simp]:
  "callee_invariant \<dagger>oracle (\<lambda>(s', s). I s')"
by unfold_locales auto

lemma callee_invariant_extend_state_oracle_const':
  "callee_invariant \<dagger>oracle (\<lambda>s. I (fst s))"
by unfold_locales auto

definition lift_stop_oracle :: "('call, 'ret, 's) callee \<Rightarrow> ('call, 'ret option, 's) callee"
where "lift_stop_oracle oracle s x = map_spmf (apfst Some) (oracle s x)"

lemma lift_stop_oracle_apply [simp]: "lift_stop_oracle  oracle s x = map_spmf (apfst Some) (oracle s x)"
  by(fact lift_stop_oracle_def)
  
context includes lifting_syntax begin

lemma lift_stop_oracle_transfer:
  "((S ===> C ===> rel_spmf (rel_prod R S)) ===> (S ===> C ===> rel_spmf (rel_prod (pcr_Some R) S)))
   (\<lambda>x. x) lift_stop_oracle"
unfolding lift_stop_oracle_def
apply(rule rel_funI)+
apply(drule (1) rel_funD)+
apply(simp add: spmf_rel_map apfst_def prod.rel_map)
done

end

definition extend_state_oracle2 :: "('call, 'ret, 's) callee \<Rightarrow> ('call, 'ret, 's \<times> 's') callee" ("_\<dagger>" [1000] 1000)
  where "extend_state_oracle2 callee = (\<lambda>(s, s') x. map_spmf (\<lambda>(y, s). (y, (s, s'))) (callee s x))"

lemma extend_state_oracle2_simps [simp]:
  "extend_state_oracle2 callee (s, s') x = map_spmf (\<lambda>(y, s). (y, (s, s'))) (callee s x)"
  by(simp add: extend_state_oracle2_def)

lemma extend_state_oracle2_parametric [transfer_rule]: includes lifting_syntax shows
  "((S ===> C ===> rel_spmf (rel_prod R S)) ===> rel_prod S S' ===> C ===> rel_spmf (rel_prod R (rel_prod S S')))
  extend_state_oracle2 extend_state_oracle2"
  unfolding extend_state_oracle2_def[abs_def] by transfer_prover

lemma callee_invariant_extend_state_oracle2_const [simp]:
  "callee_invariant oracle\<dagger> (\<lambda>(s, s'). I s')"
  by unfold_locales auto

lemma callee_invariant_extend_state_oracle2_const':
  "callee_invariant oracle\<dagger> (\<lambda>s. I (snd s))"
  by unfold_locales auto

lemma extend_state_oracle2_plus_oracle: 
  "extend_state_oracle2 (plus_oracle oracle1 oracle2) = plus_oracle (extend_state_oracle2 oracle1) (extend_state_oracle2 oracle2)"
proof((rule ext)+; goal_cases)
  case (1 s q)
  then show ?case by (cases s; cases q) (simp_all add: apfst_def spmf.map_comp o_def split_def)
qed

lemma parallel_oracle_conv_plus_oracle:
  "parallel_oracle oracle1 oracle2 = plus_oracle (oracle1\<dagger>) (\<dagger>oracle2)"
proof((rule ext)+; goal_cases)
  case (1 s q)
  then show ?case by (cases s; cases q) (auto simp add: spmf.map_comp apfst_def o_def split_def map_prod_def)
qed

lemma map_sum_parallel_oracle: includes lifting_syntax shows
  "(id ---> map_sum f g ---> map_spmf (map_prod (map_sum h k) id)) (parallel_oracle oracle1 oracle2)
  = parallel_oracle ((id ---> f ---> map_spmf (map_prod h id)) oracle1) ((id ---> g ---> map_spmf (map_prod k id)) oracle2)"
proof((rule ext)+; goal_cases)
  case (1 s q)
  then show ?case by (cases s; cases q) (simp_all add: spmf.map_comp o_def apfst_def prod.map_comp)
qed

lemma map_sum_plus_oracle: includes lifting_syntax shows
  "(id ---> map_sum f g ---> map_spmf (map_prod (map_sum h k) id)) (plus_oracle oracle1 oracle2)
  = plus_oracle ((id ---> f ---> map_spmf (map_prod h id)) oracle1) ((id ---> g ---> map_spmf (map_prod k id)) oracle2)"
proof((rule ext)+; goal_cases)
  case (1 s q)
  then show ?case by (cases q) (simp_all add: spmf.map_comp o_def apfst_def prod.map_comp)
qed

lemma map_rsuml_plus_oracle: includes lifting_syntax shows
  "(id ---> rsuml ---> (map_spmf (map_prod lsumr id))) (oracle1 \<oplus>\<^sub>O (oracle2 \<oplus>\<^sub>O oracle3)) =
   ((oracle1 \<oplus>\<^sub>O oracle2) \<oplus>\<^sub>O oracle3)"
proof((rule ext)+; goal_cases)
  case (1 s q)
  then show ?case 
  proof(cases q)
    case (Inl ql)
    then show ?thesis by(cases ql)(simp_all add: spmf.map_comp o_def apfst_def prod.map_comp)
  qed (simp add: spmf.map_comp o_def apfst_def prod.map_comp id_def)
qed

lemma map_lsumr_plus_oracle: includes lifting_syntax shows
  "(id ---> lsumr ---> (map_spmf (map_prod rsuml id))) ((oracle1 \<oplus>\<^sub>O oracle2) \<oplus>\<^sub>O oracle3) =
   (oracle1 \<oplus>\<^sub>O (oracle2 \<oplus>\<^sub>O oracle3))"
proof((rule ext)+; goal_cases)
  case (1 s q)
  then show ?case 
  proof(cases q)
    case (Inr qr)
    then show ?thesis by(cases qr)(simp_all add: spmf.map_comp o_def apfst_def prod.map_comp)
  qed (simp add: spmf.map_comp o_def apfst_def prod.map_comp id_def)
qed

context includes lifting_syntax begin

definition lift_state_oracle
  :: "(('s \<Rightarrow> 'a \<Rightarrow> (('b \<times> 't) \<times> 's) spmf) \<Rightarrow> ('s' \<Rightarrow> 'a \<Rightarrow> (('b \<times> 't) \<times> 's') spmf)) 
  \<Rightarrow> ('t \<times> 's \<Rightarrow> 'a \<Rightarrow> ('b \<times> 't \<times> 's) spmf) \<Rightarrow> ('t \<times> 's' \<Rightarrow> 'a \<Rightarrow> ('b \<times> 't \<times> 's') spmf)" where
  "lift_state_oracle F oracle = 
   (\<lambda>(t, s') a. map_spmf rprodl (F ((Pair t ---> id ---> map_spmf lprodr) oracle) s' a))"

lemma lift_state_oracle_simps [simp]:
  "lift_state_oracle F oracle (t, s') a = map_spmf rprodl (F ((Pair t ---> id ---> map_spmf lprodr) oracle) s' a)"
  by(simp add: lift_state_oracle_def)

lemma lift_state_oracle_parametric [transfer_rule]: includes lifting_syntax shows
  "(((S ===> A ===> rel_spmf (rel_prod (rel_prod B T) S)) ===> S' ===> A ===> rel_spmf (rel_prod (rel_prod B T) S'))
  ===> (rel_prod T S ===> A ===> rel_spmf (rel_prod B (rel_prod T S)))
  ===> rel_prod T S' ===> A ===> rel_spmf (rel_prod B (rel_prod T S')))
  lift_state_oracle lift_state_oracle"
  unfolding lift_state_oracle_def map_fun_def o_def by transfer_prover

lemma lift_state_oracle_extend_state_oracle:
  includes lifting_syntax
  assumes "\<And>B. Transfer.Rel (((=) ===> (=) ===> rel_spmf (rel_prod B (=))) ===> (=) ===> (=) ===> rel_spmf (rel_prod B (=))) G F"
    (* TODO: implement simproc to discharge parametricity assumptions like this one *)
  shows "lift_state_oracle F (extend_state_oracle oracle) = extend_state_oracle (G oracle)"
  unfolding lift_state_oracle_def extend_state_oracle_def
  apply(clarsimp simp add: fun_eq_iff map_fun_def o_def spmf.map_comp split_def rprodl_def)
  subgoal for t s a
    apply(rule sym)
    apply(fold spmf_rel_eq)
    apply(simp add: spmf_rel_map)
    apply(rule rel_spmf_mono)
     apply(rule assms[unfolded Rel_def, where B="\<lambda>x (y, z). x = y \<and> z = t", THEN rel_funD, THEN rel_funD, THEN rel_funD])
       apply(auto simp add: rel_fun_def spmf_rel_map intro!: rel_spmf_reflI)
    done
  done

lemma lift_state_oracle_compose: 
  "lift_state_oracle F (lift_state_oracle G oracle) = lift_state_oracle (F \<circ> G) oracle"
  by(simp add: lift_state_oracle_def map_fun_def o_def split_def spmf.map_comp)

lemma lift_state_oracle_id [simp]: "lift_state_oracle id = id"
  by(simp add: fun_eq_iff spmf.map_comp o_def)

lemma rprodl_extend_state_oracle: includes lifting_syntax shows
  "(rprodl ---> id ---> map_spmf (map_prod id lprodr)) (extend_state_oracle (extend_state_oracle oracle)) = 
  extend_state_oracle oracle"
  by(simp add: fun_eq_iff spmf.map_comp o_def split_def)

end

section \<open>Combining GPVs\<close>

subsection \<open>Shared state without interrupts\<close>

context
  fixes left :: "'s \<Rightarrow> 'x1 \<Rightarrow> ('y1 \<times> 's, 'call, 'ret) gpv"
  and right :: "'s \<Rightarrow> 'x2 \<Rightarrow> ('y2 \<times> 's, 'call, 'ret) gpv"
begin

primrec plus_intercept :: "'s \<Rightarrow> 'x1 + 'x2 \<Rightarrow> (('y1 + 'y2) \<times> 's, 'call, 'ret) gpv"
where
  "plus_intercept s (Inl x) = map_gpv (apfst Inl) id (left s x)"
| "plus_intercept s (Inr x) = map_gpv (apfst Inr) id (right s x)"

end

lemma plus_intercept_parametric [transfer_rule]:
  includes lifting_syntax shows
  "((S ===> X1 ===> rel_gpv (rel_prod Y1 S) C)
  ===> (S ===> X2 ===> rel_gpv (rel_prod Y2 S) C)
  ===> S ===> rel_sum X1 X2 ===> rel_gpv (rel_prod (rel_sum Y1 Y2) S) C)
  plus_intercept plus_intercept"
unfolding plus_intercept_def[abs_def] by transfer_prover

lemma interaction_bounded_by_plus_intercept [interaction_bound]:
  fixes left right
  shows "\<lbrakk> \<And>x'. x = Inl x' \<Longrightarrow> interaction_bounded_by P (left s x') (n x');
    \<And>y. x = Inr y \<Longrightarrow> interaction_bounded_by P (right s y) (m y) \<rbrakk>
  \<Longrightarrow> interaction_bounded_by P (plus_intercept left right s x) (case x of Inl x \<Rightarrow> n x | Inr y \<Rightarrow> m y)"
by(simp split!: sum.split add: interaction_bounded_by_map_gpv_id)

subsection \<open>Shared state with interrupts\<close>

context 
  fixes left :: "'s \<Rightarrow> 'x1 \<Rightarrow> ('y1 option \<times> 's, 'call, 'ret) gpv"
  and right :: "'s \<Rightarrow> 'x2 \<Rightarrow> ('y2 option \<times> 's, 'call, 'ret) gpv"
begin

primrec plus_intercept_stop :: "'s \<Rightarrow> 'x1 + 'x2 \<Rightarrow> (('y1 + 'y2) option \<times> 's, 'call, 'ret) gpv"
where
  "plus_intercept_stop s (Inl x) = map_gpv (apfst (map_option Inl)) id (left s x)"
| "plus_intercept_stop s (Inr x) = map_gpv (apfst (map_option Inr)) id (right s x)"

end

lemma plus_intercept_stop_parametric [transfer_rule]:
  includes lifting_syntax shows
  "((S ===> X1 ===> rel_gpv (rel_prod (rel_option Y1) S) C)
  ===> (S ===> X2 ===> rel_gpv (rel_prod (rel_option Y2) S) C)
  ===> S ===> rel_sum X1 X2 ===> rel_gpv (rel_prod (rel_option (rel_sum Y1 Y2)) S) C)
  plus_intercept_stop plus_intercept_stop"
unfolding plus_intercept_stop_def by transfer_prover

subsection \<open>One-sided shifts\<close>

primcorec (transfer) left_gpv :: "('a, 'out, 'in) gpv \<Rightarrow> ('a, 'out + 'out', 'in + 'in') gpv" where
  "the_gpv (left_gpv gpv) = 
   map_spmf (map_generat id Inl (\<lambda>rpv input. case input of Inl input' \<Rightarrow> left_gpv (rpv input') | _ \<Rightarrow> Fail)) (the_gpv gpv)"

abbreviation left_rpv :: "('a, 'out, 'in) rpv \<Rightarrow> ('a, 'out + 'out', 'in + 'in') rpv" where
  "left_rpv rpv \<equiv> \<lambda>input. case input of Inl input' \<Rightarrow> left_gpv (rpv input') | _ \<Rightarrow> Fail"

primcorec (transfer) right_gpv :: "('a, 'out, 'in) gpv \<Rightarrow> ('a, 'out' + 'out, 'in' + 'in) gpv" where
  "the_gpv (right_gpv gpv) =
   map_spmf (map_generat id Inr (\<lambda>rpv input. case input of Inr input' \<Rightarrow> right_gpv (rpv input') | _ \<Rightarrow> Fail)) (the_gpv gpv)"

abbreviation right_rpv :: "('a, 'out, 'in) rpv \<Rightarrow> ('a, 'out' + 'out, 'in' + 'in) rpv" where
  "right_rpv rpv \<equiv> \<lambda>input. case input of Inr input' \<Rightarrow> right_gpv (rpv input') | _ \<Rightarrow> Fail"

context 
  includes lifting_syntax
  notes [transfer_rule] = corec_gpv_parametric' Fail_parametric' the_gpv_parametric'
begin

lemmas left_gpv_parametric = left_gpv.transfer

lemma left_gpv_parametric':
  "(rel_gpv'' A C R ===> rel_gpv'' A (rel_sum C C') (rel_sum R R')) left_gpv left_gpv"
  unfolding left_gpv_def by transfer_prover

lemmas right_gpv_parametric = right_gpv.transfer

lemma right_gpv_parametric':
  "(rel_gpv'' A C' R' ===> rel_gpv'' A (rel_sum C C') (rel_sum R R')) right_gpv right_gpv"
  unfolding right_gpv_def by transfer_prover

end

lemma left_gpv_Done [simp]: "left_gpv (Done x) = Done x"
  by(rule gpv.expand) simp

lemma right_gpv_Done [simp]: "right_gpv (Done x) = Done x"
  by(rule gpv.expand) simp

lemma left_gpv_Pause [simp]:
  "left_gpv (Pause x rpv) = Pause (Inl x) (\<lambda>input. case input of Inl input' \<Rightarrow> left_gpv (rpv input') | _ \<Rightarrow> Fail)"
  by(rule gpv.expand) simp

lemma right_gpv_Pause [simp]:
  "right_gpv (Pause x rpv) = Pause (Inr x) (\<lambda>input. case input of Inr input' \<Rightarrow> right_gpv (rpv input') | _ \<Rightarrow> Fail)"
  by(rule gpv.expand) simp

lemma left_gpv_map: "left_gpv (map_gpv f g gpv) = map_gpv f (map_sum g h) (left_gpv gpv)"
  using left_gpv.transfer[of "BNF_Def.Grp UNIV f" "BNF_Def.Grp UNIV g" "BNF_Def.Grp UNIV h"]
  unfolding sum.rel_Grp gpv.rel_Grp
  by(auto simp add: rel_fun_def Grp_def)

lemma right_gpv_map: "right_gpv (map_gpv f g gpv) = map_gpv f (map_sum h g) (right_gpv gpv)"
  using right_gpv.transfer[of "BNF_Def.Grp UNIV f" "BNF_Def.Grp UNIV g" "BNF_Def.Grp UNIV h"]
  unfolding sum.rel_Grp gpv.rel_Grp
  by(auto simp add: rel_fun_def Grp_def)

lemma results'_gpv_left_gpv [simp]: 
  "results'_gpv (left_gpv gpv :: ('a, 'out + 'out', 'in + 'in') gpv) = results'_gpv gpv" (is "?lhs = ?rhs")
proof(rule Set.set_eqI iffI)+
  show "x \<in> ?rhs" if "x \<in> ?lhs" for x using that
    by(induction gpv'\<equiv>"left_gpv gpv :: ('a, 'out + 'out', 'in + 'in') gpv" arbitrary: gpv)
      (fastforce simp add: elim!: generat.set_cases intro: results'_gpvI split: sum.splits)+
  show "x \<in> ?lhs" if "x \<in> ?rhs" for x using that
    by(induction)
      (auto 4 3 elim!: generat.set_cases intro: results'_gpv_Pure rev_image_eqI results'_gpv_Cont[where input="Inl _"])
qed

lemma results'_gpv_right_gpv [simp]: 
  "results'_gpv (right_gpv gpv :: ('a, 'out' + 'out, 'in' + 'in) gpv) = results'_gpv gpv" (is "?lhs = ?rhs")
proof(rule Set.set_eqI iffI)+
  show "x \<in> ?rhs" if "x \<in> ?lhs" for x using that
    by(induction gpv'\<equiv>"right_gpv gpv :: ('a, 'out' + 'out, 'in' + 'in) gpv" arbitrary: gpv)
      (fastforce simp add: elim!: generat.set_cases intro: results'_gpvI split: sum.splits)+
  show "x \<in> ?lhs" if "x \<in> ?rhs" for x using that
    by(induction)
      (auto 4 3 elim!: generat.set_cases intro: results'_gpv_Pure rev_image_eqI results'_gpv_Cont[where input="Inr _"])
qed

lemma left_gpv_Inl_transfer: "rel_gpv'' (=) (\<lambda>l r. l = Inl r) (\<lambda>l r. l = Inl r) (left_gpv gpv) gpv"
  by(coinduction arbitrary: gpv)
    (auto simp add: spmf_rel_map generat.rel_map del: rel_funI intro!: rel_spmf_reflI generat.rel_refl_strong rel_funI)

lemma right_gpv_Inr_transfer: "rel_gpv'' (=) (\<lambda>l r. l = Inr r) (\<lambda>l r. l = Inr r) (right_gpv gpv) gpv"
  by(coinduction arbitrary: gpv)
    (auto simp add: spmf_rel_map generat.rel_map del: rel_funI intro!: rel_spmf_reflI generat.rel_refl_strong rel_funI)

lemma exec_gpv_plus_oracle_left: "exec_gpv (plus_oracle oracle1 oracle2) (left_gpv gpv) s = exec_gpv oracle1 gpv s"
  unfolding spmf_rel_eq[symmetric] prod.rel_eq[symmetric]
  by(rule exec_gpv_parametric'[where A="(=)" and S="(=)" and CALL="\<lambda>l r. l = Inl r" and R="\<lambda>l r. l = Inl r", THEN rel_funD, THEN rel_funD, THEN rel_funD])
    (auto intro!: rel_funI simp add: spmf_rel_map apfst_def map_prod_def rel_prod_conv intro: rel_spmf_reflI left_gpv_Inl_transfer)

lemma exec_gpv_plus_oracle_right: "exec_gpv (plus_oracle oracle1 oracle2) (right_gpv gpv) s = exec_gpv oracle2 gpv s"
  unfolding spmf_rel_eq[symmetric] prod.rel_eq[symmetric]
  by(rule exec_gpv_parametric'[where A="(=)" and S="(=)" and CALL="\<lambda>l r. l = Inr r" and R="\<lambda>l r. l = Inr r", THEN rel_funD, THEN rel_funD, THEN rel_funD])
    (auto intro!: rel_funI simp add: spmf_rel_map apfst_def map_prod_def rel_prod_conv intro: rel_spmf_reflI right_gpv_Inr_transfer)

lemma left_gpv_bind_gpv: "left_gpv (bind_gpv gpv f) = bind_gpv (left_gpv gpv) (left_gpv \<circ> f)"
  by(coinduction arbitrary:gpv f rule: gpv.coinduct_strong)
    (auto 4 4 simp add: bind_map_spmf spmf_rel_map intro!: rel_spmf_reflI rel_spmf_bindI[of "(=)"] generat.rel_refl rel_funI split: sum.splits)

lemma inline1_left_gpv:
  "inline1 (\<lambda>s q. left_gpv (callee s q)) gpv s = 
   map_spmf (map_sum id (map_prod Inl (map_prod left_rpv id))) (inline1 callee gpv s)"
proof(induction arbitrary: gpv s rule: parallel_fixp_induct_2_2[OF partial_function_definitions_spmf partial_function_definitions_spmf inline1.mono inline1.mono inline1_def inline1_def, unfolded lub_spmf_empty, case_names adm bottom step])
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step inline1' inline1'')
  then show ?case
    by(auto simp add: map_spmf_bind_spmf o_def bind_map_spmf intro!: ext bind_spmf_cong split: generat.split)
qed

lemma left_gpv_inline: "left_gpv (inline callee gpv s) = inline (\<lambda>s q. left_gpv (callee s q)) gpv s"
  by(coinduction arbitrary: callee gpv s rule: gpv_coinduct_bind)
    (fastforce simp add: inline_sel spmf_rel_map inline1_left_gpv left_gpv_bind_gpv o_def split_def intro!: rel_spmf_reflI split: sum.split intro!: rel_funI gpv.rel_refl_strong)

lemma right_gpv_bind_gpv: "right_gpv (bind_gpv gpv f) = bind_gpv (right_gpv gpv) (right_gpv \<circ> f)"
  by(coinduction arbitrary:gpv f rule: gpv.coinduct_strong)
    (auto 4 4 simp add: bind_map_spmf spmf_rel_map intro!: rel_spmf_reflI rel_spmf_bindI[of "(=)"] generat.rel_refl rel_funI split: sum.splits)

lemma inline1_right_gpv:
  "inline1 (\<lambda>s q. right_gpv (callee s q)) gpv s = 
   map_spmf (map_sum id (map_prod Inr (map_prod right_rpv id))) (inline1 callee gpv s)"
proof(induction arbitrary: gpv s rule: parallel_fixp_induct_2_2[OF partial_function_definitions_spmf partial_function_definitions_spmf inline1.mono inline1.mono inline1_def inline1_def, unfolded lub_spmf_empty, case_names adm bottom step])
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step inline1' inline1'')
  then show ?case
    by(auto simp add: map_spmf_bind_spmf o_def bind_map_spmf intro!: ext bind_spmf_cong split: generat.split)
qed

lemma right_gpv_inline: "right_gpv (inline callee gpv s) = inline (\<lambda>s q. right_gpv (callee s q)) gpv s"
  by(coinduction arbitrary: callee gpv s rule: gpv_coinduct_bind)
    (fastforce simp add: inline_sel spmf_rel_map inline1_right_gpv right_gpv_bind_gpv o_def split_def intro!: rel_spmf_reflI split: sum.split intro!: rel_funI gpv.rel_refl_strong)

lemma WT_gpv_left_gpv: "\<I>1 \<turnstile>g gpv \<surd> \<Longrightarrow> \<I>1 \<oplus>\<^sub>\<I> \<I>2 \<turnstile>g left_gpv gpv \<surd>"
  by(coinduction arbitrary: gpv)(auto 4 4 dest: WT_gpvD)

lemma WT_gpv_right_gpv: "\<I>2 \<turnstile>g gpv \<surd> \<Longrightarrow> \<I>1 \<oplus>\<^sub>\<I> \<I>2 \<turnstile>g right_gpv gpv \<surd>"
  by(coinduction arbitrary: gpv)(auto 4 4 dest: WT_gpvD)

lemma results_gpv_left_gpv [simp]: "results_gpv (\<I>1 \<oplus>\<^sub>\<I> \<I>2) (left_gpv gpv) = results_gpv \<I>1 gpv"
  (is "?lhs = ?rhs")
proof(rule Set.set_eqI iffI)+
  show "x \<in> ?rhs" if "x \<in> ?lhs" for x using that
    by(induction gpv'\<equiv>"left_gpv gpv :: ('a, 'b + 'c, 'd + 'e) gpv" arbitrary: gpv rule: results_gpv.induct)
      (fastforce intro: results_gpv.intros)+
  show "x \<in> ?lhs" if "x \<in> ?rhs" for x using that
    by(induction)(fastforce intro: results_gpv.intros)+
qed

lemma results_gpv_right_gpv [simp]: "results_gpv (\<I>1 \<oplus>\<^sub>\<I> \<I>2) (right_gpv gpv) = results_gpv \<I>2 gpv"
  (is "?lhs = ?rhs")
proof(rule Set.set_eqI iffI)+
  show "x \<in> ?rhs" if "x \<in> ?lhs" for x using that
    by(induction gpv'\<equiv>"right_gpv gpv :: ('a, 'b + 'c, 'd + 'e) gpv" arbitrary: gpv rule: results_gpv.induct)
      (fastforce intro: results_gpv.intros)+
  show "x \<in> ?lhs" if "x \<in> ?rhs" for x using that
    by(induction)(fastforce intro: results_gpv.intros)+
qed

lemma left_gpv_Fail [simp]: "left_gpv Fail = Fail"
  by(rule gpv.expand) auto

lemma right_gpv_Fail [simp]: "right_gpv Fail = Fail"
  by(rule gpv.expand) auto

lemma rsuml_lsumr_left_gpv_left_gpv:"map_gpv' id rsuml lsumr (left_gpv (left_gpv gpv)) = left_gpv gpv"
  by(coinduction arbitrary: gpv)
    (auto 4 3 simp add: spmf_rel_map generat.rel_map intro!: rel_spmf_reflI rel_generat_reflI rel_funI split!: sum.split elim!: lsumr.elims intro: exI[where x=Fail])

lemma rsuml_lsumr_left_gpv_right_gpv: "map_gpv' id rsuml lsumr (left_gpv (right_gpv gpv)) = right_gpv (left_gpv gpv)"
  by(coinduction arbitrary: gpv)
    (auto 4 3 simp add: spmf_rel_map generat.rel_map intro!: rel_spmf_reflI rel_generat_reflI rel_funI split!: sum.split elim!: lsumr.elims intro: exI[where x=Fail])

lemma rsuml_lsumr_right_gpv: "map_gpv' id rsuml lsumr (right_gpv gpv) = right_gpv (right_gpv gpv)"
  by(coinduction arbitrary: gpv)
    (auto 4 3 simp add: spmf_rel_map generat.rel_map intro!: rel_spmf_reflI rel_generat_reflI rel_funI split!: sum.split elim!: lsumr.elims intro: exI[where x=Fail])

lemma map_gpv'_map_gpv_swap:
  "map_gpv' f g h (map_gpv f' id gpv) = map_gpv (f \<circ> f') id (map_gpv' id g h gpv)"
  by(simp add: map_gpv_conv_map_gpv' map_gpv'_comp)

lemma lsumr_rsuml_left_gpv: "map_gpv' id lsumr rsuml (left_gpv gpv) = left_gpv (left_gpv gpv)"
  by(coinduction arbitrary: gpv)
    (auto 4 3 simp add: spmf_rel_map generat.rel_map intro!: rel_spmf_reflI rel_generat_reflI rel_funI split!: sum.split intro: exI[where x=Fail])

lemma lsumr_rsuml_right_gpv_left_gpv:
  "map_gpv' id lsumr rsuml (right_gpv (left_gpv gpv)) = left_gpv (right_gpv gpv)"
  by(coinduction arbitrary: gpv)
    (auto 4 3 simp add: spmf_rel_map generat.rel_map intro!: rel_spmf_reflI rel_generat_reflI rel_funI split!: sum.split intro: exI[where x=Fail])

lemma lsumr_rsuml_right_gpv_right_gpv:
  "map_gpv' id lsumr rsuml (right_gpv (right_gpv gpv)) = right_gpv gpv"
  by(coinduction arbitrary: gpv)
    (auto 4 3 simp add: spmf_rel_map generat.rel_map intro!: rel_spmf_reflI rel_generat_reflI rel_funI split!: sum.split elim!: rsuml.elims intro: exI[where x=Fail])


lemma in_set_spmf_extend_state_oracle [simp]:
  "x \<in> set_spmf (extend_state_oracle oracle s y) \<longleftrightarrow>
   fst (snd x) = fst s \<and> (fst x, snd (snd x)) \<in> set_spmf (oracle (snd s) y)"
  by(auto 4 4 simp add: extend_state_oracle_def split_beta intro: rev_image_eqI prod.expand)

lemma extend_state_oracle_plus_oracle: 
  "extend_state_oracle (plus_oracle oracle1 oracle2) = plus_oracle (extend_state_oracle oracle1) (extend_state_oracle oracle2)"
proof ((rule ext)+; goal_cases)
  case (1 s q)
  then show ?case by (cases s; cases q) (simp_all add: apfst_def spmf.map_comp o_def split_def)
qed


definition stateless_callee :: "('a \<Rightarrow> ('b, 'out, 'in) gpv) \<Rightarrow> ('s \<Rightarrow> 'a \<Rightarrow> ('b \<times> 's, 'out, 'in) gpv)" where
  "stateless_callee callee s = map_gpv (\<lambda>b. (b, s)) id \<circ> callee"

lemma stateless_callee_parametric': 
  includes lifting_syntax notes [transfer_rule] = map_gpv_parametric' shows
    "((A ===> rel_gpv'' B C R) ===> S ===> A ===> (rel_gpv'' (rel_prod B S) C R))
   stateless_callee stateless_callee"
  unfolding stateless_callee_def by transfer_prover

lemma id_oralce_alt_def: "id_oracle = stateless_callee (\<lambda>x. Pause x Done)"
  by(simp add: id_oracle_def fun_eq_iff stateless_callee_def)

context
  fixes left :: "'s1 \<Rightarrow> 'x1 \<Rightarrow> ('y1 \<times> 's1, 'call1, 'ret1) gpv"
    and right :: "'s2 \<Rightarrow> 'x2 \<Rightarrow> ('y2 \<times> 's2, 'call2, 'ret2) gpv"
begin

fun parallel_intercept :: "'s1 \<times> 's2 \<Rightarrow> 'x1 + 'x2 \<Rightarrow> (('y1 + 'y2) \<times> ('s1 \<times> 's2), 'call1 + 'call2, 'ret1 + 'ret2) gpv"
  where
    "parallel_intercept (s1, s2) (Inl a) = left_gpv (map_gpv (map_prod Inl (\<lambda>s1'. (s1', s2))) id (left s1 a))"
  | "parallel_intercept (s1, s2) (Inr b) = right_gpv (map_gpv (map_prod Inr (Pair s1)) id (right s2 b))"

end

end
