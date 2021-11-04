section \<open>Exchange Protocol\label{sec:exchange}\<close>

(*<*)
theory Exchange
  imports
    "HOL-Library.While_Combinator"
    Auxiliary
begin
(*>*)

subsection\<open>Specification\<close>

record ('p, 't) configuration =
  c_temp :: "'p \<Rightarrow> 't zmultiset"
  c_msg :: "'p \<Rightarrow> 'p \<Rightarrow> 't zmultiset list"
  c_glob :: "'p \<Rightarrow> 't zmultiset"
  c_caps :: "'p \<Rightarrow> 't zmultiset"
  c_data_msg :: "('p \<times> 't) multiset"

text\<open>
Description of the configuration:
@{term "c_msg c p q"} global, all progress messages currently in-flight from p to q
@{term "c_data_msg c"} global, capabilities carried by in-flight data messages
@{term "c_temp c p"} local, aggregated progress updates of worker p that haven't been sent yet
@{term "c_glob c p"} local, worker p's conservative approximation of all capabilities in the system
@{term "c_caps c p"} local, worker p's capabilities

global = state of the whole system to which no worker has access
local = state that is kept locally by each worker and which it can access
\<close>

type_synonym ('p, 't) computation = "('p, 't) configuration stream"

context order begin

abbreviation "timestamps M \<equiv> {# t. (x,t) \<in>#\<^sub>z M #}"

definition vacant_upto :: "'a zmultiset \<Rightarrow> 'a \<Rightarrow> bool" where
  "vacant_upto a t \<equiv> (\<forall>s. s \<le> t \<longrightarrow> zcount a s = 0)"

definition nonpos_upto :: "'a zmultiset \<Rightarrow> 'a \<Rightarrow> bool" where
  "nonpos_upto a t = (\<forall>s. s \<le> t \<longrightarrow> zcount a s \<le> 0)"

definition supported :: "'a zmultiset \<Rightarrow> 'a \<Rightarrow> bool" where
  "supported a t \<equiv> (\<exists>s. s < t \<and> zcount a s < 0)"

definition supported_strong :: "'a zmultiset \<Rightarrow> 'a \<Rightarrow> bool" where
  "supported_strong a t \<equiv> (\<exists>s. s < t \<and> zcount a s < 0 \<and> nonpos_upto a s)"

definition justified where
  "justified C M = (\<forall>t. 0 < zcount M t \<longrightarrow> supported M t \<or> (\<exists>t'<t. 0 < zcount C t') \<or> zcount M t < zcount C t)"

lemma justified_alt:
  "justified C M = (\<forall>t. 0 < zcount M t \<longrightarrow> supported_strong M t \<or> (\<exists>t'<t. 0 < zcount C t') \<or> zcount M t < zcount C t)"
  unfolding justified_def supported_def supported_strong_def
  apply (rule iffI)
   apply clarsimp
   apply (drule order_zmset_exists_foundation')
   apply clarsimp
  subgoal for t s
    apply (drule spec[of _ s])
    apply safe
      apply (meson le_less_trans less_le_trans nonpos_upto_def)
    using order.strict_trans2 apply blast
    using order.order_iff_strict apply auto
    done
  apply blast
  done

definition justified_with where
  "justified_with C M N =
    (\<forall>t. 0 < zcount M t \<longrightarrow>
       (\<exists>s<t. (zcount M s < 0 \<or> zcount N s < 0)) \<or>
       (\<exists>s<t. 0 < zcount C s) \<or>
       zcount (M+N) t < zcount C t)"

lemma justified_with_alt: "justified_with C M N =
  (\<forall>t. 0 < zcount M t \<longrightarrow>
    (\<exists>s<t. (zcount M s < 0 \<or> zcount N s < 0) \<and> (\<forall>s'<s. zcount M s' \<le> 0)) \<or>
    (\<exists>s<t. 0 < zcount C s) \<or>
    zcount (M+N) t < zcount C t)"
  unfolding justified_with_def
  apply (rule iffI)
   apply clarsimp
   apply (drule order_zmset_exists_foundation')
   apply clarsimp
  subgoal for t s
    apply (drule spec[of _ s])
    apply safe
    using order.strict_trans order.strict_trans2 apply blast+
    apply (metis add_less_zeroD order.order_iff_strict not_less_iff_gr_or_eq order_class.order.strict_trans)
    done
  apply blast
  done

definition PositiveImplies where
  "PositiveImplies v w \<equiv> \<forall>t. zcount v t > 0 \<longrightarrow> zcount w t > 0"

\<comment> \<open>A worker can mint capabilities greater or equal to any owned capability\<close>
definition minting_self where
  "minting_self C M = (\<forall>t\<in>#M. \<exists>t'\<le>t. 0 < zcount C t')"

\<comment> \<open>Sending messages mints a capability at a strictly greater pointstamp\<close>
definition minting_msg where
  "minting_msg C M = (\<forall>(p,t)\<in>#M. \<exists>t'<t. 0 < zcount C t')"

definition records where
  "records c = (\<Sum>p\<in>UNIV. c_caps c p) + timestamps (zmset_of (c_data_msg c))"

definition InfoAt where
  "InfoAt c k p q = (if 0 \<le> k \<and> k < length (c_msg c p q) then (c_msg c p q) ! k else {#}\<^sub>z)"

definition IncomingInfo :: "('p, 'a) configuration \<Rightarrow> nat \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'a zmultiset" where
  "IncomingInfo c k p q \<equiv> sum_list (drop k (c_msg c p q)) + c_temp c p"

definition GlobalIncomingInfo :: "('p :: finite, 'a) configuration \<Rightarrow> nat \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'a zmultiset" where
  "GlobalIncomingInfo c k p q \<equiv> \<Sum>p' \<in> UNIV. IncomingInfo c (if p' = p then k else 0) p' q"

(* (GlobalIncomingInfo c 0 q q) sums up all info incoming at q *)
abbreviation GlobalIncomingInfoAt where
  "GlobalIncomingInfoAt c q \<equiv> GlobalIncomingInfo c 0 q q"

definition init_config :: "('p :: finite, 'a) configuration \<Rightarrow> bool" where
  "init_config c \<equiv>
      (\<forall>p. c_temp c p = {#}\<^sub>z) \<and>
      (\<forall>p1 p2. c_msg c p1 p2 = []) \<and>
      \<comment> \<open>Capabilities have non-negative multiplicities\<close>
      (\<forall>p t. 0 \<le> zcount (c_caps c p) t) \<and>
      \<comment> \<open>The pointstamps in glob are exactly those in @{term records}\<close>
      (\<forall>p. c_glob c p = records c) \<and>
      \<comment> \<open>All capabilities are being tracked\<close>
      c_data_msg c = {#}"

(* Processor receives a capability, i.e. in timely: receives a data message *)
definition next_recvcap' :: "('p :: finite, 'a) configuration \<Rightarrow> ('p, 'a) configuration \<Rightarrow> 'p \<Rightarrow> 'a \<Rightarrow> bool" where
  "next_recvcap' c0 c1 p t = (
      (p,t) \<in># c_data_msg c0
    \<and> c1 = c0\<lparr>c_caps := (c_caps c0)(p := c_caps c0 p + {#t#}\<^sub>z),
              c_data_msg := c_data_msg c0 - {#(p,t)#}\<rparr>)"

abbreviation next_recvcap where
  "next_recvcap c0 c1 \<equiv> \<exists>p t. next_recvcap' c0 c1 p t"

text\<open>
Can minting of capabilities be described as a refinement of the Abadi model?
Short answer: No, not in general.
Long answer:
Could slightly modify Abadi model, such that a capability always comes with a multiplicity $2^64$ (or
similar, could be parametrized over arbitrarily large constant). In that case minting new
capabilities can be described as an upright change, dropping one of the capabilities, to make the
change upright. This only works as long as no capability is required more than the constant number
of times.
Issues:
- Not fully general, due to the arbitrary constant
- Not clear whether refinement proofs would be easier than simply altering the model to support the operations
\<close>

text\<open>Rationale for the condition on @{term "c_caps c0 p"}:
In Abadi, the operation @{term next_performop'} has the premise @{term "\<forall>t. int (count \<Delta>neg t) \<le> zcount (records c0) t"},
(records corresponds to the global field @{term nrec} in that model)
which means the processor performing the transition must verify that this condition is met.
Since @{term "records c"} is "global" state, which no processor can know, an implementation of
this protocol has to include some other protocol or reasoning for when it is safe to do this
transition.

Naively using a processor's @{term "c_glob c p"} to approximate @{term "records c"} and justify
transitions can cause a race condition, where a processor drops a pointstamp, e.g.,
@{term "\<Delta>neg = {#t#}"}, after which @{term "zcount (records c) t = 0"} but other processors might still
use the pointstamp to justify the creation of pointstamps that violate the safety property.

Instead we model ownership of pointstamps, calling "owned pointstamps" \<^bold>\<open>capabilities\<close>, which are
tracked in @{term "c_caps c"}. In place of @{term nrec} we define @{term "records c"}, which is the sum of
all capabilities, as well as @{term "c_data_msg c"}, which contains the capabilities carried by data
messages. Since @{term "\<forall>p t. zcount (c_caps c p) t \<le> zcount (records c) t"}, our condition
@{term "\<forall>t. int (count \<Delta>neg t) \<le> zcount (c_caps c0 p) t"} implies the one on @{term nrec} in Abadi's model.
\<close>

text\<open>Conditions in performop:

The performop transition takes three msets of pointstamps, @{term \<Delta>neg}, @{term \<Delta>mint_msg}, and @{term \<Delta>mint_self}
@{term \<Delta>neg} contains dropped capabilities (a subset of @{term c_caps})
@{term \<Delta>mint_msg} contains pairs @{term "(p,t)"}, where a data message is sent (i.e. capability added to the pool), creating a capability at t, owned by p
@{term \<Delta>mint_self} contains pointstamps minted and owned by worker @{term p}

@{term \<Delta>neg} in combination with @{term \<Delta>mint_msg} also allows any upright updates to be made as in the Abadi model,
meaning this definition allows strictly more behaviors.

The @{term "\<Delta>mint_msg \<noteq> {#} \<or> zmset_of \<Delta>mint_self - zmset_of \<Delta>neg \<noteq> {#}\<^sub>z"} condition ensures that
no-ops aren't possible. However, it's still possible that the combined @{term \<Delta>} is empty. E.g. a processor
has capabilities 1 and 2, uses cap 1 to send a message, minting capability 2. Simultaneously it
drops a capability 2 (for unrelated reasons), cancelling out the overall change but shifting a
capability to the pool, possibly with a different owner than itself.\<close>

definition next_performop' :: "('p::finite, 'a) configuration \<Rightarrow> ('p, 'a) configuration \<Rightarrow> 'p \<Rightarrow> 'a multiset \<Rightarrow> ('p \<times> 'a) multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  "next_performop' c0 c1 p \<Delta>neg \<Delta>mint_msg \<Delta>mint_self =
    \<comment> \<open>@{term \<Delta>pos} contains all positive changes, @{term \<Delta>} the combined positive and negative changes\<close>
   (let \<Delta>pos = timestamps (zmset_of \<Delta>mint_msg) + zmset_of \<Delta>mint_self;
        \<Delta> = \<Delta>pos - zmset_of \<Delta>neg
    in
      (\<Delta>mint_msg \<noteq> {#} \<or> zmset_of \<Delta>mint_self - zmset_of \<Delta>neg \<noteq> {#}\<^sub>z)
    \<and> (\<forall>t. int (count \<Delta>neg t) \<le> zcount (c_caps c0 p) t)
    \<comment> \<open>Pointstamps added in @{term \<Delta>mint_self} are minted at p\<close>
    \<and> minting_self (c_caps c0 p) \<Delta>mint_self
    \<comment> \<open>Pointstamps added in @{term \<Delta>mint_msg} correspond to sent data messages\<close>
    \<and> minting_msg (c_caps c0 p) \<Delta>mint_msg
    \<comment> \<open>Worker immediately knows about dropped and minted capabilities\<close>
    \<and> c1 = c0\<lparr>c_caps := (c_caps c0)(p := c_caps c0 p + zmset_of \<Delta>mint_self - zmset_of \<Delta>neg),
    \<comment> \<open>Sending a data message creates a capability, once that message arrives. This is modelled as
        a pool of capabilities that may (will) appear at processors at some point.\<close>
              c_data_msg := c_data_msg c0 + \<Delta>mint_msg,
              c_temp := (c_temp c0)(p := c_temp c0 p + \<Delta>)\<rparr>)"

abbreviation next_performop where
  "next_performop c0 c1 \<equiv> (\<exists>p \<Delta>neg \<Delta>mint_msg \<Delta>mint_self. next_performop' c0 c1 p \<Delta>neg \<Delta>mint_msg \<Delta>mint_self)"

definition next_sendupd' :: "('p::finite, 'a) configuration \<Rightarrow> ('p, 'a) configuration \<Rightarrow> 'p \<Rightarrow> 'a set \<Rightarrow> bool" where
  "next_sendupd' c0 c1 p tt =
   (let \<gamma> = {#t \<in>#\<^sub>z c_temp c0 p. t \<in> tt#} in
      \<gamma> \<noteq> 0
    \<and> justified (c_caps c0 p) (c_temp c0 p - \<gamma>)
    \<and> c1 = c0\<lparr>c_msg := (c_msg c0)(p := \<lambda>q. c_msg c0 p q @ [\<gamma>]),
              c_temp := (c_temp c0)(p := c_temp c0 p - \<gamma>)\<rparr>)"

abbreviation next_sendupd where
  "next_sendupd c0 c1 \<equiv> (\<exists>p tt. next_sendupd' c0 c1 p tt)"

definition next_recvupd' :: "('p::finite, 'a) configuration \<Rightarrow> ('p, 'a) configuration \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool" where
  "next_recvupd' c0 c1 p q \<equiv>
      c_msg c0 p q \<noteq> []
    \<and> c1 = c0\<lparr>c_msg := (c_msg c0)(p := (c_msg c0 p)(q := tl (c_msg c0 p q))),
              c_glob := (c_glob c0)(q := c_glob c0 q + hd (c_msg c0 p q))\<rparr>"

abbreviation next_recvupd where
  "next_recvupd c0 c1 \<equiv> (\<exists>p q. next_recvupd' c0 c1 p q)"

definition "next'" where
  "next' c0 c1 = (next_performop c0 c1 \<or> next_sendupd c0 c1 \<or> next_recvupd c0 c1 \<or> next_recvcap c0 c1 \<or> c1 = c0)"

abbreviation "next" where
  "next s \<equiv> next' (shd s) (shd (stl s))"

definition spec :: "('p :: finite, 'a) computation \<Rightarrow> bool" where
  "spec s \<equiv> holds init_config s \<and> alw next s"

abbreviation GlobVacantUpto where
  "GlobVacantUpto c q t \<equiv> vacant_upto (c_glob c q) t"

abbreviation GlobNonposUpto where
  "GlobNonposUpto c q t \<equiv> nonpos_upto (c_glob c q) t"

abbreviation RecordsVacantUpto where
  "RecordsVacantUpto c t \<equiv> vacant_upto (records c) t"

definition SafeGlobVacantUptoImpliesStickyNrec :: "('p :: finite, 'a) computation \<Rightarrow> bool" where
  "SafeGlobVacantUptoImpliesStickyNrec s =
     (let c = shd s in \<forall>t q. GlobVacantUpto c q t \<longrightarrow> alw (holds (\<lambda>c. RecordsVacantUpto c t)) s)"

subsection\<open>Auxiliary Lemmas\<close>

lemma finite_induct_select [consumes 1, case_names empty select]:
  assumes "finite S"
    and empty: "P {}"
    and select: "\<And>T. finite T \<Longrightarrow> T \<subset> S \<Longrightarrow> P T \<Longrightarrow> \<exists>s\<in>S - T. P (insert s T)"
  shows "P S"
proof -
  from assms(1) have "P S \<and> finite S"
    by (induct S rule: finite_induct_select) (auto intro: empty select)
  then show ?thesis by blast
qed

lemma finite_induct_decompose_sum:
  fixes f :: "'c \<Rightarrow> ('b :: comm_monoid_add)"
  assumes "finite X"
    and     "x\<in>X"
    and     "A (f x)"
    and     "\<forall>Z. B (sum f Z)"
    and     "\<And>x Z. A (f x) \<Longrightarrow> B (sum f Z) \<Longrightarrow> A (f x + sum f Z)"
    and     "\<And>x Z. B (f x) \<Longrightarrow> A (sum f Z) \<Longrightarrow> A (f x + sum f Z)"
  shows "A (\<Sum>x\<in>X. f x)"
  using assms(1,2,3)
  apply (induct X rule: finite_induct_select)
   apply simp
  apply (simp add: sum.insert_remove)
  subgoal for T
    apply (cases "x \<in> T"; simp add: assms(3))
     apply (drule psubset_imp_ex_mem)
     apply clarsimp
    subgoal for z
      apply (rule bexI[of _ z])
       apply (rule conjI)
        apply clarsimp
       apply (rule assms(6)[of z T])
        apply (rule assms(4)[THEN spec, of "{z}", simplified])
       apply simp
      apply simp
      done
    apply clarsimp
    apply (drule bspec[of _ _ x])
     apply safe
     apply (rule assms(2))
    using assms(4) assms(5) apply blast
    done
  done

lemma minting_msg_add_records: "minting_msg C1 M \<Longrightarrow> \<forall>t. 0 \<le> zcount C2 t \<Longrightarrow> minting_msg (C1+C2) M"
  by (auto simp: minting_msg_def intro: add_strict_increasing dest!: bspec)

lemma add_less: "(a::int) < c \<Longrightarrow> b \<le> 0 \<Longrightarrow> a + b < c"
  by linarith

lemma disj3_split: "P \<or> Q \<or> R \<Longrightarrow> (P \<Longrightarrow> thesis) \<Longrightarrow> (\<not> P \<and> Q \<Longrightarrow> thesis) \<Longrightarrow> (\<not> P \<Longrightarrow> \<not> Q \<Longrightarrow> R \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by blast

lemma filter_zmset_conclude_predicate: "0 < zcount {# x \<in>#\<^sub>z M. P x #} x \<Longrightarrow> 0 < zcount M x \<Longrightarrow> P x"
  by (auto split: if_splits)

lemma alw_holds2: "alw (holds P) ss = (P (shd ss) \<and> alw (holds P) (stl ss))"
  by (meson alw.simps holds.elims(2) holds.elims(3))

lemma zmset_of_remove1_mset: "x \<in># M \<Longrightarrow> zmset_of (remove1_mset x M) = zmset_of M - {#x#}\<^sub>z"
  by (induct M) auto

lemma timestamps_zmset_of_pair_image[simp]: "timestamps (zmset_of {# (c,t). t \<in># M #}) = zmset_of M"
  by (induct M) auto

lemma timestamps_image_zmset_fst[simp]: "timestamps {# (f x, t). (x, t) \<in>#\<^sub>z M #} = timestamps M"
  apply transfer
  apply (clarsimp simp: equiv_zmset_def)
  apply (metis (no_types, lifting) case_prod_unfold image_mset_cong prod.collapse prod.inject)
  done

lemma lift_invariant_to_spec:
  assumes "(\<And>c. init_config c \<Longrightarrow> P c)"
    and   "(\<And>s. holds P s \<Longrightarrow> next s \<Longrightarrow> nxt (holds P) s)"
  shows   "spec s \<Longrightarrow> alw (holds P) s"
  unfolding spec_def
  apply (elim conjE)
  apply (coinduction arbitrary: s)
  apply clarsimp
  apply (intro conjI assms(1))
   apply safe
  subgoal
  proof -
    fix sa :: "('b, 'a) configuration stream"
    assume a1: "init_config (shd sa)"
    assume a2: "alw next sa"
    assume "\<not> alw (holds P) (stl sa)"
    then have "\<not> alw (\<lambda>s. holds P s \<longrightarrow> nxt (holds P) s) sa"
      using a1 by (metis (no_types) alw.cases alw_invar assms(1) holds.elims(3))
    then show "init_config (shd (stl sa))"
      using a2 by (metis (lifting) alw_iff_sdrop assms(2))
  qed
  apply auto
  done

lemma timestamps_sum_distrib[simp]: "(\<Sum>p \<in> A. timestamps (f p)) = timestamps (\<Sum>p \<in> A. f p)"
  by (induction A rule: infinite_finite_induct) auto

lemma timestamps_zmset_of[simp]: "timestamps (zmset_of M) = zmset_of {# t. (p,t) \<in># M #}"
  by (induct M) auto

lemma vacant_upto_add: "vacant_upto a t \<Longrightarrow> vacant_upto b t \<Longrightarrow> vacant_upto (a+b) t"
  by (simp add: vacant_upto_def)

lemma nonpos_upto_add: "nonpos_upto a t \<Longrightarrow> nonpos_upto b t \<Longrightarrow> nonpos_upto (a+b) t"
  by (auto intro: add_nonpos_nonpos simp: nonpos_upto_def)

lemma nonzero_lt_gtD: "(n::_::linorder) \<noteq> 0 \<Longrightarrow> 0 < n \<or> n < 0"
  by auto

lemma zero_lt_diff: "(0::int) < a - b \<Longrightarrow> b \<ge> 0 \<Longrightarrow> 0 < a"
  by auto

lemma zero_lt_add_disj: "0 < (a::int) + b \<Longrightarrow> 0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 < a \<or> 0 < b"
  by auto

subsubsection\<open>Transition lemmas\<close>

lemma next_performopD:
  assumes "next_performop' c0 c1 p \<Delta>neg \<Delta>mint_msg \<Delta>mint_self"
  shows
    "\<Delta>mint_msg \<noteq> {#} \<or> zmset_of \<Delta>mint_self - zmset_of \<Delta>neg \<noteq> {#}\<^sub>z"
    "\<forall>t. int (count \<Delta>neg t) \<le> zcount (c_caps c0 p) t"
    "minting_self (c_caps c0 p) \<Delta>mint_self"
    "minting_msg (c_caps c0 p) \<Delta>mint_msg"
    "c_temp c1 = (c_temp c0)(p := c_temp c0 p + (timestamps (zmset_of \<Delta>mint_msg) + zmset_of \<Delta>mint_self - zmset_of \<Delta>neg))"
    "c_msg c1  = c_msg c0"
    "c_glob c1 = c_glob c0"
    "c_data_msg c1 = c_data_msg c0 + \<Delta>mint_msg"
    "c_caps c1 = (c_caps c0)(p := c_caps c0 p + (zmset_of \<Delta>mint_self - zmset_of \<Delta>neg))"
  using assms by (simp_all add: next_performop'_def Let_def algebra_simps)

lemma next_performop_complexD:
  assumes "next_performop' c0 c1 p \<Delta>neg \<Delta>mint_msg \<Delta>mint_self"
  shows
    "records c1 = records c0 + (timestamps (zmset_of \<Delta>mint_msg) + zmset_of \<Delta>mint_self - zmset_of \<Delta>neg)"
    "GlobalIncomingInfoAt c1 q = GlobalIncomingInfoAt c0 q + (timestamps (zmset_of \<Delta>mint_msg) + zmset_of \<Delta>mint_self - zmset_of \<Delta>neg)"
    "IncomingInfo c1 k p' q = (if p' = p
      then IncomingInfo c0 k p' q + (timestamps (zmset_of \<Delta>mint_msg) + zmset_of \<Delta>mint_self - zmset_of \<Delta>neg)
      else IncomingInfo c0 k p' q)"
    "\<forall>t'<t. zcount (c_caps c0 p) t' = 0 \<Longrightarrow> zcount (timestamps (zmset_of \<Delta>mint_msg)) t = 0"
    "InfoAt c1 k p' q = InfoAt c0 k p' q"
proof -
  let ?\<Delta> = "timestamps (zmset_of \<Delta>mint_msg) + zmset_of \<Delta>mint_self - zmset_of \<Delta>neg"
  note change = next_performopD[OF assms(1)]
  show "records c1 = records c0 + ?\<Delta>"
    unfolding records_def change
    apply simp
    apply (subst add_diff_eq[symmetric])
    apply (subst sum_if_distrib_add)
      apply (simp_all add: algebra_simps zmset_of_plus)
    done
  show "IncomingInfo c1 k p' q = (if p' = p
      then IncomingInfo c0 k p' q + (timestamps (zmset_of \<Delta>mint_msg) + zmset_of \<Delta>mint_self - zmset_of \<Delta>neg)
      else IncomingInfo c0 k p' q)"
    unfolding IncomingInfo_def change
    by (auto simp: algebra_simps)
  show "GlobalIncomingInfoAt c1 q = GlobalIncomingInfoAt c0 q + ?\<Delta>" for q
    unfolding GlobalIncomingInfo_def IncomingInfo_def
    by (rule Sum_eq_pick_changed_elem[where m = p]) (simp_all add: change algebra_simps)
  show "\<forall>t'<t. zcount (c_caps c0 p) t' = 0 \<Longrightarrow> zcount (timestamps (zmset_of \<Delta>mint_msg)) t = 0" for t
    by (rule ccontr) (clarsimp dest!: image_zmset_pre change(4)[unfolded minting_msg_def, rule_format])
  show "InfoAt c1 k p' q = InfoAt c0 k p' q"
    unfolding InfoAt_def change by simp
qed

lemma next_sendupdD:
  assumes "next_sendupd' c0 c1 p tt"
  shows
    "{#t \<in>#\<^sub>z c_temp c0 p. t \<in> tt#} \<noteq> {#}\<^sub>z"
    "justified (c_caps c0 p) (c_temp c0 p - {#t \<in>#\<^sub>z c_temp c0 p. t \<in> tt#})"
    "c_temp c1 p' = (if p' = p then c_temp c0 p - {#t \<in>#\<^sub>z c_temp c0 p. t \<in> tt#} else c_temp c0 p')"
    "c_msg c1 = (\<lambda>p' q. if p' = p then c_msg c0 p q @ [{#t \<in>#\<^sub>z c_temp c0 p. t \<in> tt#}] else c_msg c0 p' q)"
    "c_glob c1 = c_glob c0"
    "c_caps c1 = c_caps c0"
    "c_data_msg c1 = c_data_msg c0"
  using assms by (simp_all add: next_sendupd'_def Let_def fun_eq_iff)

lemma next_sendupd_complexD:
  assumes "next_sendupd' c0 c1 p tt"
  shows
    "records c1 = records c0"
    "IncomingInfo c1 0 = IncomingInfo c0 0"
    "IncomingInfo c1 k p' q = (if p' = p \<and> length (c_msg c0 p q) < k
                               then IncomingInfo c0 k p' q - {#t \<in>#\<^sub>z c_temp c0 p'. t \<in> tt#}
                               else IncomingInfo c0 k p' q)"
    "k \<le> length (c_msg c0 p q) \<Longrightarrow> IncomingInfo c1 k p' q = IncomingInfo c0 k p' q"
    "length (c_msg c0 p q) < k \<Longrightarrow>
     IncomingInfo c1 k p' q = (if p' = p
                               then IncomingInfo c0 k p' q - {#t \<in>#\<^sub>z c_temp c0 p'. t \<in> tt#}
                               else IncomingInfo c0 k p' q)"
    "GlobalIncomingInfoAt c1 q = GlobalIncomingInfoAt c0 q"
    "InfoAt c1 k p' q = (if p' = p \<and> k = length (c_msg c0 p q) then {#t \<in>#\<^sub>z c_temp c0 p'. t \<in> tt#} else InfoAt c0 k p' q)"
proof -
  note change = next_sendupdD[OF assms]
  show "records c1 = records c0"
    by (simp add: records_def change)
  show ii: "IncomingInfo c1 k p' q = (if p' = p \<and> length (c_msg c0 p q) < k
                                      then IncomingInfo c0 k p' q - {#t \<in>#\<^sub>z c_temp c0 p'. t \<in> tt#}
                                      else IncomingInfo c0 k p' q)"
    by (simp add: algebra_simps IncomingInfo_def change)
  then show "k \<le> length (c_msg c0 p q) \<Longrightarrow> IncomingInfo c1 k p' q = IncomingInfo c0 k p' q"
    by auto
  from ii show "length (c_msg c0 p q) < k \<Longrightarrow>
     IncomingInfo c1 k p' q = (if p' = p
                               then IncomingInfo c0 k p' q - {#t \<in>#\<^sub>z c_temp c0 p'. t \<in> tt#}
                               else IncomingInfo c0 k p' q)"
    by auto
  have "IncomingInfo c1 0 p q = IncomingInfo c0 0 p q" for p q
    by (simp add: algebra_simps IncomingInfo_def change)
  then show "IncomingInfo c1 0 = IncomingInfo c0 0"
    by auto
  then show "GlobalIncomingInfoAt c1 q = GlobalIncomingInfoAt c0 q"
    unfolding GlobalIncomingInfo_def by auto
  show "InfoAt c1 k p' q = (if p' = p \<and> k = length (c_msg c0 p q) then {#t \<in>#\<^sub>z c_temp c0 p'. t \<in> tt#} else InfoAt c0 k p' q)"
    unfolding InfoAt_def change
    by (auto simp: nth_append)
qed

lemma next_recvupdD:
  assumes "next_recvupd' c0 c1 p q"
  shows
    "c_msg c0 p q \<noteq> []"
    "c_temp c1 = c_temp c0"
    "c_msg c1 = (\<lambda>p' q'. if p' = p \<and> q' = q then tl (c_msg c0 p q) else c_msg c0 p' q')"
    "c_glob c1 = (c_glob c0)(q := c_glob c0 q + hd (c_msg c0 p q))"
    "c_caps c1 = c_caps c0"
    "c_data_msg c1 = c_data_msg c0"
  using assms by (simp_all add: next_recvupd'_def fun_eq_iff)

lemma next_recvupd_complexD:
  assumes "next_recvupd' c0 c1 p q"
  shows
    "records c1 = records c0"
    "IncomingInfo c1 0 p' q' = (if p' = p \<and> q' = q then IncomingInfo c0 0 p' q' - hd (c_msg c0 p q) else IncomingInfo c0 0 p' q')"
    "IncomingInfo c1 k p' q' = (if p' = p \<and> q' = q
                                then IncomingInfo c0 (k+1) p' q'
                                else IncomingInfo c0 k p' q')"
    "GlobalIncomingInfoAt c1 q' = (if q' = q then GlobalIncomingInfoAt c0 q' - hd (c_msg c0 p q) else GlobalIncomingInfoAt c0 q')"
    "InfoAt c1 k p q = InfoAt c0 (k+1) p q"
    "InfoAt c1 k p' q' = (if p' = p \<and> q' = q then InfoAt c0 (k+1) p q else InfoAt c0 k p' q')"
proof -
  note change = next_recvupdD[OF assms]
  show "records c1 = records c0"
    by (simp add: records_def change)
  show ii: "IncomingInfo c1 0 p' q' = (if p' = p \<and> q' = q then IncomingInfo c0 0 p' q' - hd (c_msg c0 p q) else IncomingInfo c0 0 p' q')" for p' q'
    by (auto simp: IncomingInfo_def change algebra_simps sum_list_hd_tl)
  show "IncomingInfo c1 k p' q' = (if p' = p \<and> q' = q
                                   then IncomingInfo c0 (k+1) p' q'
                                   else IncomingInfo c0 k p' q')"
    by (auto simp:  IncomingInfo_def change algebra_simps sum_list_hd_tl drop_Suc)
  show "GlobalIncomingInfoAt c1 q' = (if q' = q then GlobalIncomingInfoAt c0 q' - hd (c_msg c0 p q) else GlobalIncomingInfoAt c0 q')"
    unfolding GlobalIncomingInfo_def
    apply (cases "q'=q")
     apply simp
     apply (subst diff_conv_add_uminus)
     apply (intro Sum_eq_pick_changed_elem[where m = p])
        apply (simp_all add: ii)
    done
  show "InfoAt c1 k p q = InfoAt c0 (k+1) p q"
    unfolding InfoAt_def change
    by (auto simp: nth_tl)
  show "InfoAt c1 k p' q' = (if p' = p \<and> q' = q then InfoAt c0 (k+1) p q else InfoAt c0 k p' q')"
    unfolding InfoAt_def change
    by (auto simp: nth_tl)
qed

lemma next_recvcapD:
  assumes "next_recvcap' c0 c1 p t"
  shows
    "(p,t) \<in># c_data_msg c0"
    "c_temp c1 = c_temp c0"
    "c_msg c1 = c_msg c0"
    "c_glob c1 = c_glob c0"
    "c_caps c1 = (c_caps c0)(p := c_caps c0 p + {#t#}\<^sub>z)"
    "c_data_msg c1 = c_data_msg c0 - {#(p,t)#}"
  using assms by (simp_all add: next_recvcap'_def)

lemma next_recvcap_complexD:
  assumes "next_recvcap' c0 c1 p t"
  shows
    "records c1 = records c0"
    "IncomingInfo c1 = IncomingInfo c0"
    "GlobalIncomingInfo c1 = GlobalIncomingInfo c0"
    "InfoAt c1 k p' q = InfoAt c0 k p' q"
proof -
  note change = next_recvcapD[OF assms]
  show "records c1 = records c0"
    unfolding records_def change fun_upd_apply
    apply (subst sum_if_distrib_add)
    using change(1) apply (simp_all add: zmset_of_remove1_mset algebra_simps records_def change)
    done
  show "IncomingInfo c1 = IncomingInfo c0"
    unfolding IncomingInfo_def change by simp
  then show "GlobalIncomingInfo c1 = GlobalIncomingInfo c0"
    unfolding GlobalIncomingInfo_def by simp
  show "InfoAt c1 k p' q = InfoAt c0 k p' q"
    unfolding InfoAt_def change by simp
qed

lemma ex_next_recvupd:
  assumes "c_msg c0 p q \<noteq> []"
  shows   "\<exists>c1. next_recvupd' c0 c1 p q"
  using assms unfolding next_recvupd'_def
  by (intro
      exI[of _ "c0\<lparr>c_msg := (\<lambda>p' q'. if p' = p \<and> q' = q then tl (c_msg c0 p q) else c_msg c0 p' q'),
                   c_glob := (\<lambda>q'. if q' = q then c_glob c0 q + hd (c_msg c0 p q) else c_glob c0 q')\<rparr>"])
        (auto simp: fun_eq_iff)

subsubsection\<open>Facts about @{term justified}'ness\<close>

lemma justified_empty[simp]: "justified {#}\<^sub>z {#}\<^sub>z"
  by (simp add: justified_def)

text\<open>It's sufficient to show justified for least pointstamps in M.\<close>
lemma justified_leastI:
  assumes "\<forall>t. 0 < zcount M t \<longrightarrow> (\<forall>t'<t. zcount M t' \<le> 0) \<longrightarrow> supported_strong M t \<or> (\<exists>t'<t. 0 < zcount C t') \<or> (zcount M t < zcount C t)"
  shows   "justified C M"
  unfolding justified_alt supported_strong_def
  apply (intro allI impI)
  apply (drule order_zmset_exists_foundation)
  apply (elim exE conjE)
  subgoal for t' s
    apply (drule assms(1)[unfolded supported_strong_def, rule_format])
     apply (auto intro: ccontr) []
    apply (elim disj3_split)
      apply (rule disjI1)
    using order.strict_trans2 apply blast
     apply (rule disjI2, rule disjI1)
    using order.strict_trans2 apply blast
    apply (clarsimp simp: nonpos_upto_def)
    apply (metis le_less_linear linear le_imp_less_or_eq preorder_class.le_less_trans)
    done
  done

lemma justified_add:
  assumes "justified C1 M1"
    and   "justified C2 M2"
    and   "\<forall>t. 0 \<le> zcount C1 t"
    and   "\<forall>t. 0 \<le> zcount C2 t"
  shows   "justified (C1+C2) (M1+M2)"
  apply (rule justified_leastI)
  apply (intro allI impI)
  subgoal for t
    apply (cases "0 < zcount M1 t") (* symmetric cases *)
    subgoal
      apply (drule assms(1)[unfolded justified_alt supported_strong_def, rule_format])
      apply (elim disj3_split)
      subgoal
        apply (elim exE conjE)
        apply (drule order_zmset_exists_foundation_neg)
        apply (elim exE conjE)
        subgoal for s s' (* anything less than s' is 0 in M1 *)
          apply (cases "zcount (M1 + M2) s' < 0")
          subgoal
            apply (rule disjI1)
            apply (auto intro!: exI[of _ s'] simp: nonpos_upto_def supported_strong_def) []
            done
          subgoal
            apply (subst (asm) not_less)
            apply (cases "0 < zcount M2 s'")
             prefer 2
            subgoal by auto (* trivial contradiction *)
            subgoal
              apply (drule assms(2)[unfolded justified_alt supported_strong_def, rule_format])
              apply (elim disj3_split)
              subgoal
                apply (rule disjI1)
                apply (elim exE)
                subgoal for s''
                  by (auto intro!: exI[of _ s''] simp: nonpos_upto_def supported_strong_def add_nonpos_neg)
                done
              subgoal
                apply (rule disjI2, rule disjI1)
                apply (elim exE conjE)
                subgoal for s''
                  using assms(3) by (auto simp: add_nonneg_pos intro!: exI[of _ s''])
                done
              subgoal
                by (metis add.right_neutral add_strict_increasing2 assms(3) less_add_same_cancel1 order.strict_trans1 pos_add_strict zcount_union)
              done
            done
          done
        done
      subgoal
        by (metis add.commute add_mono_thms_linordered_field(4) assms(4) add_0 zcount_union)
      subgoal
        apply (cases "supported_strong M2 t")
        subgoal
          apply (rule disjI1)
          using assms(1)[unfolded justified_alt]
          apply (subst supported_strong_def)
          apply (subst (asm) supported_strong_def)
          apply (elim exE conjE)
          unfolding not_ex
          subgoal for s
            apply clarsimp
            apply (rule exI[of _ s])
            apply (intro conjI)
              apply blast
             apply (rule add_nonpos_neg)
              apply (metis order.strict_trans1 less_imp_le not_le not_less_iff_gr_or_eq order_class.order.strict_trans2 supported_strong_def)
             apply simp
            apply (clarsimp simp: nonpos_upto_def)
            done
          done
        subgoal
          apply (cases "\<exists>t'<t. 0 < zcount C2 t'")
          subgoal
            by (metis add_cancel_left_left assms(3) order_class.order.not_eq_order_implies_strict zcount_union)
          subgoal
            apply (intro disjI2)
            apply clarsimp
            using assms(2)[unfolded justified_alt, rule_format, of t]
            apply (metis add.commute add_cancel_left_right add_mono_thms_linordered_field(5) add_strict_increasing2 assms(4) nonzero_lt_gtD)
            done
          done
        done
      done
    subgoal
      apply (cases "0 < zcount M2 t") (* symmetric case *)
       prefer 2
      subgoal by auto
      subgoal
        apply (drule assms(2)[unfolded justified_alt supported_strong_def, rule_format])
        apply (elim disj3_split)
        subgoal
          apply (elim exE conjE)
          apply (drule order_zmset_exists_foundation_neg)
          apply (elim exE conjE)
          subgoal for s s' (* anything less than s' is 0 in M1 *)
            apply (cases "zcount (M1 + M2) s' < 0")
            subgoal
              apply (rule disjI1)
              apply (auto intro!: exI[of _ s'] simp: nonpos_upto_def supported_strong_def) []
              done
            subgoal
              apply (subst (asm) not_less)
              apply (cases "0 < zcount M1 s'")
               prefer 2
              subgoal by auto (* trivial contradiction *)
              subgoal
                apply (drule assms(1)[unfolded justified_alt supported_strong_def, rule_format])
                apply (elim disj3_split)
                subgoal
                  apply (rule disjI1)
                  apply (elim exE)
                  subgoal for s''
                    by (auto intro!: exI[of _ s''] simp: nonpos_upto_def supported_strong_def add_neg_nonpos)
                  done
                subgoal
                  apply (rule disjI2, rule disjI1)
                  apply (elim exE conjE)
                  subgoal for s''
                    using assms(4) by (auto simp: add_pos_nonneg intro!: exI[of _ s''])
                  done
                subgoal
                  apply (rule disjI2, rule disjI1, rule exI[of _ s'], rule conjI)
                  using assms(4) by (auto intro!: add_pos_nonneg)
                done
              done
            done
          done
        subgoal
          by (metis add_mono_thms_linordered_field(4) assms(3) add_0 zcount_union)
        subgoal
          apply (cases "supported_strong M1 t")
          subgoal
            apply (rule disjI1)
            apply (simp only: supported_strong_def)
            apply (elim exE)
            subgoal for s
              apply (clarsimp simp: nonpos_upto_def intro!: exI[of _ s])
              using assms(2)[unfolded justified_alt nonpos_upto_def supported_strong_def, rule_format, of s]
                assms(4)[rule_format, of s]
              apply (metis (mono_tags, hide_lams) less_add_same_cancel1 order.strict_trans2 less_imp_le not_less order_class.order.not_eq_order_implies_strict order_class.order.strict_implies_order)
              done
            done
          subgoal
            apply (cases "\<exists>t'<t. 0 < zcount C1 t'")
            subgoal
              by (metis add.commute add_cancel_left_left assms(4) order_class.order.not_eq_order_implies_strict zcount_union)
            subgoal
              apply (intro disjI2)
              apply (metis add.commute add_strict_increasing2 assms(3) not_le sublist_order.add_less zcount_union)
              done
            done
          done
        done
      done
    done
  done

lemma justified_sum:
  assumes "\<forall>p\<in>P. justified (f p) (g p)"
    and   "\<forall>p\<in>P. \<forall>t. 0 \<le> zcount (f p) t"
  shows   "justified (\<Sum>p\<in>P. f p) (\<Sum>p\<in>P. g p)"
  using assms
  by (induct P rule: infinite_finite_induct)
    (auto intro!: justified_add sum_nonneg simp: zcount_sum)

lemma justified_add_records:
  assumes "justified C M"
    and   "\<forall>t. 0 \<le> zcount C' t"
  shows   "justified (C+C') M"
  using assms unfolding justified_def
  apply (clarsimp intro: add_pos_nonneg)
  apply (metis add.commute add_strict_increasing2 assms(2))
  done

lemma justified_add_zmset_records:
  assumes "justified C M"
  shows   "justified (add_zmset t C) M"
  using assms
  apply (subst add_zmset_add_single)
  apply (rule justified_add_records)
   apply simp_all
  done

lemma justified_diff:
  assumes "justified C M"
    and   "\<forall>t. 0 \<le> zcount C t"
    and   "\<forall>t. count \<Delta> t \<le> zcount C t"
  shows   "justified (C - zmset_of \<Delta>) (M - zmset_of \<Delta>)"
proof (intro justified_leastI allI impI)
  fix t
  assume least: "\<forall>t'<t. zcount (M - zmset_of \<Delta>) t' \<le> 0"
  assume "0 < zcount (M - zmset_of \<Delta>) t"
  then have Mt: "0 < zcount M t"
    by auto
  note assms(1)[unfolded justified_alt, rule_format, OF Mt]
  then consider "supported_strong M t" | "\<exists>t'<t. 0 < zcount C t'" | "zcount M t < zcount C t"
    by blast
  then show "supported_strong (M - zmset_of \<Delta>) t \<or> (\<exists>t'<t. 0 < zcount (C - zmset_of \<Delta>) t') \<or> zcount (M - zmset_of \<Delta>) t < zcount (C - zmset_of \<Delta>) t"
  proof cases
    case 1
    then show ?thesis
      unfolding supported_strong_def
      apply (elim exE)
      subgoal for s
        by (auto intro!: disjI1 exI[of _ s] simp: nonpos_upto_def)
      done
  next
    case 2
    then obtain s where s: "s < t" "0 < zcount C s" "\<forall>s'<s. zcount C s' = 0"
      apply atomize_elim
      apply (elim exE conjE)
      apply (drule order_zmset_exists_foundation')
      apply (elim exE conjE)
      subgoal for t' s
        apply (rule exI[of _ s])
        apply (intro conjI)
          apply auto [2]
        apply (intro allI impI)
        subgoal for s'
          using assms(2)[rule_format, of s']
          apply auto
          done
        done
      done
    then consider
      "0 < zcount (C - zmset_of \<Delta>) s" |
      "zcount (C - zmset_of \<Delta>) s = 0" "zcount (M - zmset_of \<Delta>) s < 0" |
      "zcount (C - zmset_of \<Delta>) s = 0" "zcount (M - zmset_of \<Delta>) s = 0" |
      "zcount (C - zmset_of \<Delta>) s = 0" "zcount (M - zmset_of \<Delta>) s > 0"
      using assms(3)[rule_format, of s] by atomize_elim auto
    then show ?thesis
    proof cases
      case 1
      then show ?thesis
        using s by auto
    next
      case 2
      then show ?thesis
        using s least by (auto simp: nonpos_upto_def supported_strong_def)
    next
      case 3
      note case3 = 3
      with s(2) have Ms: "0 < zcount M s"
        by - (rule ccontr, auto simp: not_less)
      note assms(1)[unfolded justified_alt, rule_format, OF Ms]
      then consider "supported_strong M s" | "\<exists>t'<s. 0 < zcount C t'" | "zcount M s < zcount C s"
        using not_less by blast
      then show ?thesis
      proof cases
        case 1
        then show ?thesis
          unfolding supported_strong_def
          apply (elim exE conjE)
          subgoal for s'
            apply (intro disjI1 exI[of _ s'])
            using s(1,2) apply (auto intro: exI[of _ s'] simp: nonpos_upto_def)
            done
          done
      next
        case 2
        then show ?thesis
          using s(3) by auto
      next
        case 3
        from case3 have "zcount C s = zcount M s"
          by auto
        with 3 show ?thesis
          by linarith
      qed
    next
      case 4
      then show ?thesis
        using least s(1) by auto
    qed
  next
    case 3
    then show ?thesis
      by auto
  qed
qed

lemma justified_add_msg_delta:
  assumes "justified C M"
    and   "minting_msg C \<Delta>"
    and   "\<forall>t. 0 \<le> zcount C t"
  shows   "justified C (M + timestamps (zmset_of \<Delta>))"
proof (intro allI impI justified_leastI)
  fix t
  assume t: "0 < zcount (M + timestamps (zmset_of \<Delta>)) t"
  assume least: "\<forall>t'<t. zcount (M + timestamps (zmset_of \<Delta>)) t' \<le> 0"
  have \<Delta>t: "0 < zcount (timestamps (zmset_of \<Delta>)) t \<Longrightarrow> supported_strong (M + timestamps (zmset_of \<Delta>)) t \<or> (\<exists>t'<t. 0 < zcount C t') \<or> zcount (M + timestamps (zmset_of \<Delta>)) t < zcount C t"
    by (auto dest: pos_image_zmset_obtain_pre[rotated] assms(2)[unfolded minting_msg_def, rule_format])
  { assume \<Delta>t: "zcount (timestamps (zmset_of \<Delta>)) t \<le> 0"
    with t have Mt: "0 < zcount M t"
      by auto
    note assms(1)[unfolded justified_alt, rule_format, OF Mt]
    then consider
      "supported_strong M t" "\<forall>t'<t. zcount C t' = 0" "zcount M t \<ge> zcount C t" |
      "\<exists>t'<t. 0 < zcount C t'" |
      "zcount M t < zcount C t"
      using not_less assms(3)
      by (metis order_class.order.not_eq_order_implies_strict)
    then have "supported_strong (M + timestamps (zmset_of \<Delta>)) t \<or> (\<exists>t'<t. 0 < zcount C t') \<or> zcount (M + timestamps (zmset_of \<Delta>)) t < zcount C t"
    proof cases
      case 1
      then obtain s where s: "s < t" "zcount M s < 0" "\<forall>s'<s. zcount M s' = 0"
        unfolding supported_strong_def
        apply atomize_elim
        apply (elim exE conjE)
        apply (drule order_zmset_exists_foundation_neg')
        apply (elim exE conjE)
        subgoal for s s'
          by (auto intro!: exI[of _ s'] simp: nonpos_upto_def order_class.antisym)
        done
      then show ?thesis
        apply (cases "\<exists>s'\<le>s. zcount (timestamps (zmset_of \<Delta>)) s' > 0")
         apply (elim exE conjE)
        subgoal for s'
          apply (drule pos_image_zmset_obtain_pre[rotated])
           apply simp
          apply (elim exE conjE)
          apply simp
          apply (drule assms(2)[unfolded minting_msg_def, rule_format])
          apply (auto simp: supported_strong_def)
          done
        subgoal
          apply (intro disjI1 exI[of _ s])
          unfolding not_less
          apply (metis (full_types) le_less_linear least eq_refl order.strict_trans1 nonpos_upto_def supported_strong_def sublist_order.add_less zcount_union)
          done
        done
    next
      case 2
      then show ?thesis by auto
    next
      case 3
      then show ?thesis
        using \<Delta>t by auto
    qed
  }
  then show "supported_strong (M + timestamps (zmset_of \<Delta>)) t \<or> (\<exists>t'<t. 0 < zcount C t') \<or> zcount (M + timestamps (zmset_of \<Delta>)) t < zcount C t"
    apply (cases "zcount (timestamps (zmset_of \<Delta>)) t \<le> 0")
     apply blast
    apply (rule \<Delta>t)
    apply auto
    done
qed

lemma justified_add_same:
  assumes "justified C M"
    and   "minting_self C \<Delta>"
    and   "\<forall>t. 0 \<le> zcount C t"
  shows   "justified (C + zmset_of \<Delta>) (M + zmset_of \<Delta>)"
proof (intro allI impI justified_leastI)
  fix t
  assume t: "0 < zcount (M + zmset_of \<Delta>) t"
  assume least: "\<forall>t'<t. zcount (M + zmset_of \<Delta>) t' \<le> 0"
  from t consider
    "0 < zcount M t" |
    "0 < zcount (zmset_of \<Delta>) t" "zcount M t \<le> 0"
    by atomize_elim (auto simp: not_less count_inI)
  then show "supported_strong (M + zmset_of \<Delta>) t \<or> (\<exists>t'<t. 0 < zcount (C + zmset_of \<Delta>) t') \<or> zcount (M + zmset_of \<Delta>) t < zcount (C + zmset_of \<Delta>) t"
  proof cases
    case 1
    note assms(1)[unfolded justified_alt, rule_format, OF 1]
    then consider
      "supported_strong M t" |
      "\<exists>t'<t. 0 < zcount C t'" |
      "zcount M t < zcount C t"
      by blast
    then show ?thesis
    proof cases
      case 1
      then show ?thesis
        unfolding supported_strong_def
        apply (elim exE conjE)
        subgoal for t'
          apply (cases "\<exists>s\<le>t'. zcount (zmset_of \<Delta>) s > 0")
           apply (elim exE conjE)
          subgoal for s
            apply simp
            apply (drule assms(2)[unfolded minting_self_def, rule_format])
            apply (meson add_pos_nonneg order.ordering_axioms of_nat_0_le_iff ordering.strict_trans1)
            done
          subgoal
            apply (intro disjI1 exI[of _ t'] conjI)
              apply simp
             apply simp
             apply (metis add_cancel_right_left add_mono_thms_linordered_field(1) count_eq_zero_iff order.order_iff_strict of_nat_eq_0_iff)
            using least nonpos_upto_def apply auto
            done
          done
        done
    next
      case 2
      then show ?thesis
        by auto
    next
      case 3
      then show ?thesis
        by auto
    qed
  next
    case 2
    then obtain t' where t': "t' \<le> t" "0 < zcount C t'"
      using assms(2)[unfolded minting_self_def]
      by auto
    then show ?thesis
      apply (cases "t'=t")
      subgoal
        using 2(2) by auto
      subgoal
        apply (rule disjI2, rule disjI1)
        using assms(3) order.not_eq_order_implies_strict apply fastforce
        done
      done
  qed
qed

subsubsection\<open>Facts about @{term justified_with}'ness\<close>

lemma justified_with_add_records:
  assumes "justified_with C1 M N"
    and   "\<forall>t. 0 \<le> zcount C2 t"
  shows   "justified_with (C1+C2) M N"
  unfolding justified_with_def
  apply (intro allI impI)
  subgoal for t
    apply (drule assms(1)[unfolded justified_with_def, rule_format])
    apply (elim disjE)
    subgoal
      by blast
    subgoal
      apply (elim exE)
      subgoal for s
        apply (rule disjI2, rule disjI1)
        using assms(2)[rule_format, of s] by auto
      done
    subgoal
      apply (intro disjI2)
      using assms(2)[rule_format, of t]
      by auto
    done
  done

lemma justified_with_leastI:
  assumes
    "(\<forall>t. 0 < zcount M t \<longrightarrow> (\<forall>t'<t. zcount M t' \<le> 0) \<longrightarrow>
       (\<exists>s<t. (zcount M s < 0 \<or> zcount N s < 0) \<and> (\<forall>s'<s. zcount M s' \<le> 0)) \<or>
       (\<exists>s<t. 0 < zcount C s) \<or>
       zcount (M+N) t < zcount C t)"
  shows   "justified_with C M N"
  unfolding justified_with_alt
proof (intro allI impI)
  fix t
  assume t: "0 < zcount M t"
  from t obtain t' where t': "t' \<le> t" "0 < zcount M t'" "\<forall>s<t'. zcount M s \<le> 0"
    by atomize_elim (drule order_zmset_exists_foundation')
  note assms[rule_format, OF t'(2)]
  with t'(3) consider
    "\<exists>s<t'. (zcount M s < 0 \<or> zcount N s < 0) \<and> (\<forall>s'<s. zcount M s' \<le> 0)" |
    "\<exists>s<t'. 0 < zcount C s" |
    "zcount (M+N) t' < zcount C t'"
    using not_less by blast
  then show "(\<exists>s<t. (zcount M s < 0 \<or> zcount N s < 0) \<and> (\<forall>s'<s. zcount M s' \<le> 0)) \<or> (\<exists>s<t. 0 < zcount C s) \<or> zcount (M+N) t < zcount C t"
  proof cases
    case 1
    then show ?thesis
      using order.strict_trans2 t'(1) by blast
  next
    case 2
    then show ?thesis
      using order.strict_trans2 t'(1) by blast
  next
    case 3
    then consider
      "zcount (M+N) t' < 0" |
      "zcount C t' > 0"
      by atomize_elim auto
    then show ?thesis
    proof cases
      case 1
      then have "zcount N t' < 0"
        using t'(2) by auto
      with t'(3) show ?thesis
        apply (cases "t'=t")
        subgoal
          using 3(1) by blast
        subgoal
          using t'(1) by (auto intro: exI[of _ t'])
        done
    next
      case 2
      then show ?thesis
        apply (cases "t'=t")
        subgoal
          apply (intro disjI2)
          using 3(1) apply blast
          done
        subgoal
          apply (rule disjI2)
          apply (rule disjI1)
          using order.not_eq_order_implies_strict t'(1) apply blast
          done
        done
    qed
  qed
qed

lemma justified_with_add:
  assumes "justified_with C1 M N1"
    and   "justified C1 N1"
    and   "justified C2 N2"
    and   "\<forall>t. 0 \<le> zcount C1 t"
    and   "\<forall>t. 0 \<le> zcount C2 t"
  shows   "justified_with (C1+C2) M (N1+N2)"
proof (intro justified_with_leastI allI impI)
  fix t
  assume count_t: "0 < zcount M t"
  assume least: "\<forall>t'<t. zcount M t' \<le> 0"
  note assms(1)[unfolded justified_with_alt, rule_format, OF count_t]
  then consider
    "\<exists>s<t. zcount M s < 0 \<and> (\<forall>s'<s. zcount M s' \<le> 0)" |
    "\<exists>s<t. zcount N1 s < 0 \<and> (\<forall>s'<s. zcount M s' \<le> 0)" |
    "\<exists>s<t. 0 < zcount C1 s" |
    "zcount (M + N1) t < zcount C1 t"
    by blast
  then show "(\<exists>s<t. (zcount M s < 0 \<or> zcount (N1 + N2) s < 0) \<and> (\<forall>s'<s. zcount M s' \<le> 0)) \<or>
         (\<exists>s<t. 0 < zcount (C1 + C2) s) \<or> zcount (M + (N1 + N2)) t < zcount (C1 + C2) t"
  proof cases
    case 1
    then show ?thesis
      by blast
  next
    case 2
    then obtain s where s: "s < t" "zcount N1 s < 0" "\<forall>s'<s. 0 \<le> zcount N1 s'"
      apply atomize_elim
      apply (elim exE conjE)
      apply (drule order_zmset_exists_foundation_neg')
      using order.strict_trans order.strict_trans1 apply blast
      done
    then consider
      "zcount (N1 + N2) s < 0" |
      "0 < zcount N2 s" "zcount (N1 + N2) s \<ge> 0"
      by atomize_elim auto
    then show ?thesis
    proof cases
      case 1
      then show ?thesis
        using least order.strict_trans s(1) by blast
    next
      case 2
      note assms(3)[unfolded justified_alt, rule_format, OF 2(1)]
      then consider
        "supported_strong N2 s" "\<forall>t'<s. zcount C2 t' \<le> 0" "zcount N2 s \<ge> zcount C2 s" |
        "\<exists>t'<s. 0 < zcount C2 t'" |
        "zcount N2 s < zcount C2 s"
        using not_less by blast
      then show ?thesis
      proof cases
        case 1
        then obtain s' where s': "s' < s" "zcount N2 s' < 0" "nonpos_upto N2 s'"
          unfolding supported_strong_def
          by blast
        from s'(2) have nonneg: "0 \<le> zcount (N1+N2) s' \<Longrightarrow> 0 < zcount N1 s'"
          by auto
        show ?thesis
          apply (cases "zcount (N1 + N2) s' < 0")
          subgoal
            using least order.strict_trans s'(1) s(1) by (intro disjI1) blast
          subgoal
            unfolding not_less
            apply (drule nonneg)
            apply (drule assms(2)[unfolded justified_alt supported_strong_def, rule_format])
            apply (elim disjE exE conjE)
            subgoal for u
              by (metis (full_types) order.ordering_axioms order_class.order.irrefl order_class.order.strict_trans2 ordering.strict_trans s'(1) s(3))
            subgoal for u
              by (metis (no_types, hide_lams) 1(2) add_cancel_left_right assms(5) less_trans order_class.antisym s'(1) s(1) zcount_union)
            subgoal
              by (metis (no_types, hide_lams) 1(2) add_cancel_left_right assms(5) less_trans not_le order_class.antisym order_class.order.strict_trans2 s'(1) s(1) s(3) zcount_union)
            done
          done
      next
        case 2
        then show ?thesis
          apply (elim exE conjE)
          subgoal for s'
            apply (rule disjI2)
            apply (rule disjI1)
            using assms(4)[rule_format, of s'] s(1)
            apply (auto intro!: exI[of _ s'])
            done
          done
      next
        case 3
        then show ?thesis
          by (metis 2(1) add_cancel_left_right add_strict_increasing2 assms(4) not_le order_class.order.irrefl order_class.order.strict_trans2 pos_add_strict s(1) zcount_union)
      qed
    qed
  next
    case 3
    then show ?thesis
      using assms(5)
      apply -
      apply (rule disjI2)
      apply (rule disjI1)
      apply (metis order_class.order.strict_trans2 subset_zmset.le_add_same_cancel1 subseteq_zmset_def zcount_empty)
      done
  next
    case 4
    then show ?thesis
    proof (cases "zcount (M + (N1 + N2)) t < zcount (C1 + C2) t")
      case True
      then show ?thesis
        by blast
    next
      case False
      then have N2t: "0 < zcount N2 t"
        using 4 assms(5)[rule_format, of t]
        unfolding not_less zcount_union
        by linarith
      then show ?thesis
        using assms(3)[unfolded justified_alt supported_strong_def, rule_format, OF N2t]
        apply (elim exE conjE disjE)
        subgoal for s
          apply (cases "0 < zcount N1 s")
          subgoal
            apply (drule assms(2)[unfolded justified_alt supported_strong_def, rule_format])
            apply (elim exE conjE disjE)
            subgoal for s'
              apply (rule disjI1)
              apply (rule exI[of _ s'])
              apply (intro conjI)
                apply simp
               apply (metis add_cancel_right_right add_neg_neg order.strict_implies_order nonpos_upto_def order_class.order.not_eq_order_implies_strict zcount_union)
              apply (meson least less_trans)
              done
            subgoal for s'
              by (metis add_pos_nonneg assms(5) less_trans zcount_union)
            subgoal
              apply (rule ccontr)
              apply (clarsimp simp: not_le not_less)
              apply (metis (no_types, hide_lams) add_cancel_right_right add_neg_neg assms(4) assms(5) least less_trans not_less order_class.order.not_eq_order_implies_strict pos_add_strict)
              done
            done
          subgoal
            apply (intro disjI1 exI[of _ s])
            apply (intro disjI2 conjI)
              apply simp
             apply simp
            using least apply simp
            done
          done
        subgoal for s
          by (metis add.comm_neutral add_mono_thms_linordered_field(4) assms(4) zcount_union)
        subgoal
          using 4 by auto
        done
    qed
  qed
qed

lemma justified_with_sum':
  assumes "finite X" "X\<noteq>{}"
    and   "\<forall>x\<in>X. justified_with (C x) M (N x)"
    and   "\<forall>x\<in>X. justified (C x) (N x)"
    and   "\<forall>x\<in>X. \<forall>t. 0 \<le> zcount (C x) t"
  shows   "justified_with (\<Sum>x\<in>X. C x) M (\<Sum>x\<in>X. N x)"
  using assms
proof (induct X rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  show ?case
    apply (cases "F={}")
    subgoal
      using insert(5) by simp
    subgoal
      apply (subst (1 2) sum.insert_remove)
      using insert(1) apply simp
      using insert(2) apply simp
      apply (rule justified_with_add)
      using insert(5) apply simp
      using insert(6) apply simp
        apply (rule justified_sum)
      using insert(6) apply simp
      using insert(7) apply simp
      using insert(7) apply simp
      apply (intro allI)
      unfolding zcount_sum
      apply (rule sum_nonneg)
      using insert(7) apply simp
      done
    done
qed

lemma justified_with_sum:
  assumes "finite X" "X\<noteq>{}"
    and   "x \<in> X"
    and   "justified_with (C x) M (N x)"
    and   "\<forall>x\<in>X. justified (C x) (N x)"
    and   "\<forall>x\<in>X. \<forall>t. 0 \<le> zcount (C x) t"
  shows   "justified_with (\<Sum>x\<in>X. C x) M (\<Sum>x\<in>X. N x)"
  using assms
proof (induct X rule: finite_induct)
  case empty
  then show ?case
    by simp
next
  case (insert y F)
  thm insert
  show ?case
    apply (cases "F={}")
    subgoal
      using insert by simp
    subgoal
      apply (subst (1 2) sum.insert_remove)
      using insert(1) apply simp
      using insert(2) apply simp
      apply (cases "y=x")
      subgoal
        apply (rule justified_with_add)
        using insert(6) apply simp
        using insert(7) apply simp
          apply (rule justified_sum)
        using insert(7) apply simp
        using insert(8) apply simp
        using insert(8) apply simp
        apply (intro allI)
        unfolding zcount_sum
        apply (rule sum_nonneg)
        using insert(8) apply simp
        done
      subgoal
        apply (subst (1 2) add.commute)
        apply (rule justified_with_add)
            apply (rule insert(3))
                apply simp
        using insert(5) apply simp
        using insert(6) apply simp
        using insert(7) apply simp
        using insert(8) apply simp
           apply (rule justified_sum)
        using insert(7) apply simp
        using insert(8) apply simp
        using insert(7) apply simp
         apply (intro allI)
        unfolding zcount_sum
         apply (rule sum_nonneg)
        using insert(8) apply simp
        using insert(8) apply simp
        done
      done
    done
qed

lemma justified_with_add_same:
  assumes "justified_with C M N"
    and   "\<forall>t. 0 \<le> zcount C t"
  shows   "justified_with (C + zmset_of \<Delta>) M (N + zmset_of \<Delta>)"
  unfolding justified_with_def
proof (intro allI impI)
  fix t
  assume Mt: "0 < zcount M t"
  note assms(1)[unfolded justified_with_alt, rule_format, OF Mt]
  with Mt consider
    "\<exists>s<t. zcount M s < 0 \<and> (\<forall>s'<s. zcount M s' \<le> 0)" |
    "\<exists>s<t. zcount N s < 0 \<and> (\<forall>s'<s. zcount M s' \<le> 0)" |
    "\<exists>s<t. 0 < zcount C s" |
    "zcount (M + N) t < zcount C t"
    using not_less by blast
  then show "(\<exists>s<t. (zcount M s < 0 \<or> zcount (N + zmset_of \<Delta>) s < 0)) \<or>
         (\<exists>s<t. 0 < zcount (C + zmset_of \<Delta>) s) \<or> zcount (M + (N + zmset_of \<Delta>)) t < zcount (C + zmset_of \<Delta>) t"
  proof cases
    case 1
    then show ?thesis
      by blast
  next
    case 2
    then show ?thesis
      by (metis add_less_same_cancel2 assms(2) not_less preorder_class.le_less_trans zcount_union)
  next
    case 3
    then show ?thesis
      by fastforce
  next
    case 4
    then show ?thesis
      by auto
  qed
qed

lemma justified_with_add_msg_delta:
  assumes "justified_with C M N"
    and   "minting_msg C \<Delta>"
    and   "\<forall>t. 0 \<le> zcount C t"
  shows   "justified_with C M (N + timestamps (zmset_of \<Delta>))"
  unfolding justified_with_def
proof (intro allI impI)
  fix t
  assume Mt: "0 < zcount M t"
  note assms(1)[unfolded justified_with_alt, rule_format, OF Mt]
  with Mt consider
    "\<exists>s<t. zcount M s < 0 \<and> (\<forall>s'<s. zcount M s' \<le> 0)" |
    "\<exists>s<t. zcount N s < 0 \<and> (\<forall>s'<s. zcount M s' \<le> 0)" |
    "\<exists>s<t. 0 < zcount C s" |
    "zcount (M + N) t < zcount C t"
    using not_less by blast
  then show "(\<exists>s<t. (zcount M s < 0 \<or> zcount (N + timestamps (zmset_of \<Delta>)) s < 0)) \<or>
         (\<exists>s<t. 0 < zcount C s) \<or> zcount (M + (N + timestamps (zmset_of \<Delta>))) t < zcount C t"
  proof cases
    case 1
    then show ?thesis
      by blast
  next
    case 2
    then obtain s where s: "s < t" "zcount N s < 0"
      by blast
    then show ?thesis
    proof (cases "\<exists>(p,s')\<in>#\<Delta>. s' \<le> s")
      case True
      then show ?thesis
        apply -
        apply clarsimp
        apply (drule assms(2)[unfolded minting_msg_def, rule_format])
        using order.strict_trans order.strict_trans1 s(1) not_less apply blast
        done
    next
      case False
      then have "zcount (timestamps (zmset_of \<Delta>)) s = 0"
        by (force intro: ccontr dest: pos_image_zmset_obtain_pre[rotated])
      then show ?thesis
        by (metis plus_int_code(1) s(1,2) zcount_union)
    qed
  next
    case 3
    then show ?thesis
      by blast
  next
    case 4
    then show ?thesis
      apply (cases "zcount (timestamps (zmset_of \<Delta>)) t > 0")
       apply (auto dest: pos_image_zmset_obtain_pre[rotated] assms(2)[unfolded minting_msg_def, rule_format]) []
      unfolding not_less apply auto
      done
  qed
qed

lemma justified_with_diff:
  assumes "justified_with C M N"
    and   "\<forall>t. 0 \<le> zcount C t"
    and   "\<forall>t. count \<Delta> t \<le> zcount C t"
    and   "justified C N"
  shows   "justified_with (C - zmset_of \<Delta>) M (N - zmset_of \<Delta>)"
proof (intro allI impI justified_with_leastI)
  fix t
  assume Mt: "0 < zcount M t"
  assume least: "\<forall>t'<t. zcount M t' \<le> 0"
  note assms(1)[unfolded justified_with_alt, rule_format, OF Mt]
  with Mt consider
    "\<exists>s<t. zcount M s < 0 \<and> (\<forall>s'<s. zcount M s' \<le> 0)" |
    "\<exists>s<t. zcount N s < 0 \<and> (\<forall>s'<s. zcount M s' \<le> 0)" |
    "\<exists>s<t. 0 < zcount C s" "\<forall>s<t. zcount M s \<ge> 0 \<or> \<not> (\<forall>s'<s. zcount M s' \<le> 0)" "\<forall>s<t. zcount N s \<ge> 0 \<or> \<not> (\<forall>s'<s. zcount M s' \<le> 0)" "zcount (M + N) t \<ge> zcount C t"  |
    "zcount (M + N) t < zcount C t"
    using not_less by blast
  then show "(\<exists>s<t. (zcount M s < 0 \<or> zcount (N - zmset_of \<Delta>) s < 0) \<and> (\<forall>s'<s. zcount M s' \<le> 0)) \<or>
         (\<exists>s<t. 0 < zcount (C - zmset_of \<Delta>) s) \<or> zcount (M + (N - zmset_of \<Delta>)) t < zcount (C - zmset_of \<Delta>) t"
  proof cases
    case 1
    then show ?thesis
      by blast
  next
    case 2
    then show ?thesis
      using diff_add_cancel zcount_union zcount_zmset_of_nonneg by auto
  next
    case 3
    then obtain s where s: "s < t" "0 < zcount C s" "\<forall>s'<s. zcount C s' = 0"
      apply atomize_elim
      apply (elim exE conjE)
      apply (drule order_zmset_exists_foundation')
      apply (elim exE conjE)
      subgoal for t' s
        apply (rule exI[of _ s])
        apply (intro conjI)
          apply auto [2]
        apply (intro allI impI)
        subgoal for s'
          using assms(2)[rule_format, of s'] by auto
        done
      done
    then consider
      "0 < zcount (C - zmset_of \<Delta>) s" |
      "zcount (C - zmset_of \<Delta>) s = 0" "zcount (N - zmset_of \<Delta>) s < 0" |
      "zcount (C - zmset_of \<Delta>) s = 0" "zcount (N - zmset_of \<Delta>) s = 0" |
      "zcount (C - zmset_of \<Delta>) s = 0" "zcount (N - zmset_of \<Delta>) s > 0"
      using assms(3)[rule_format, of s] by atomize_elim auto
    then show ?thesis
    proof cases
      case 1
      then show ?thesis
        using s by auto
    next
      case 2
      then show ?thesis
        using s least by (auto simp: nonpos_upto_def)
    next
      case 3
      note case3 = 3
      with s(2) have Ns: "0 < zcount N s"
        by (auto intro: ccontr simp: not_less)
      note assms(4)[unfolded justified_alt, rule_format, OF Ns]
      then consider "supported_strong N s" | "\<exists>t'<s. 0 < zcount C t'" | "zcount N s < zcount C s"
        using not_less by blast
      then show ?thesis
      proof cases
        case 1
        then show ?thesis
          unfolding supported_strong_def
          apply (elim exE conjE)
          subgoal for s'
            using s(1,2) least by (auto intro: exI[of _ s'] simp: nonpos_upto_def)
          done
      next
        case 2
        then show ?thesis
          using s(3) by auto
      next
        case 3
        from case3 have "zcount C s = zcount N s"
          by auto
        with 3 show ?thesis
          by linarith
      qed
    next
      case 4
      then have Ns: "0 < zcount N s"
        by auto
      note assms(4)[unfolded justified_alt, rule_format, OF Ns]
      then consider "supported_strong N s" | "\<exists>t'<s. 0 < zcount C t'" | "zcount N s < zcount C s"
        using not_less by blast
      then show ?thesis
      proof cases
        case 1
        then show ?thesis
          unfolding supported_strong_def
          apply (elim exE conjE)
          subgoal for s'
            using s(1,2) least by (auto intro: exI[of _ s'] simp: nonpos_upto_def)
          done
      next
        case 2
        then show ?thesis
          using s(3) by auto
      next
        case 3
        have "zcount C s = zcount N s"
          using 3 4(1,2) by auto
        with 3 show ?thesis
          by linarith
      qed
    qed
  next
    case 4
    then show ?thesis
      by auto
  qed
qed

lemma PositiveImplies_justified_with:
  assumes "justified C (M+N)"
    and   "PositiveImplies M (M+N)"
  shows   "justified_with C M N"
  unfolding justified_with_def
  apply (intro allI impI)
  apply (drule assms(2)[unfolded PositiveImplies_def, rule_format])
  apply (frule assms(1)[unfolded justified_alt supported_strong_def, rule_format])
  apply (elim disjE)
  subgoal for t
    apply (intro disjI1)
    apply (elim exE)
    subgoal for s
      apply (clarsimp intro!: exI[of _ s])
      done
    done
  subgoal for t
    using less_imp_le by blast
  subgoal for t
    by (intro disjI2 exI[of _ t]) auto
  done

lemma justified_with_add_zmset[simp]:
  assumes "justified_with C M N"
  shows   "justified_with (add_zmset c C) M N"
  using assms
  apply (subst add_zmset_add_single)
  apply (rule justified_with_add_records)
   apply simp_all
  done

lemma next_performop'_preserves_justified_with:
  assumes "justified_with (c_caps c0 p) M N"
    and   "next_performop' c0 c1 p \<Delta>neg \<Delta>mint_msg \<Delta>mint_self"
    and   "\<forall>t. 0 \<le> zcount (c_caps c0 p) t"
    and   "justified (c_caps c0 p) N"
  shows   "justified_with (c_caps c0 p + zmset_of \<Delta>mint_self - zmset_of \<Delta>neg) M (N + zmset_of \<Delta>mint_self + timestamps (zmset_of \<Delta>mint_msg) - zmset_of \<Delta>neg)"
  apply (rule justified_with_diff)
     apply (rule justified_with_add_msg_delta)
       apply (rule justified_with_add_same)
  using assms(1) apply simp
  using assms(3) apply simp
      apply (rule minting_msg_add_records)
  using next_performopD(4)[OF assms(2)] apply simp
      apply simp
  using assms(3) apply simp
  using assms(3) apply simp
  using next_performopD(2)[OF assms(2)] apply (simp add: add.commute add_increasing)
  apply (rule justified_add_msg_delta)
    apply (rule justified_add_same)
  using assms(4) apply simp
  using next_performopD(3)[OF assms(2)] apply simp
  using assms(3) apply simp
   apply (rule minting_msg_add_records)
  using next_performopD(4)[OF assms(2)] apply simp
   apply simp
  using assms(3) apply (simp add: add.commute add_increasing)
  done

subsection\<open>Invariants\<close>

subsubsection\<open>InvRecordCount\<close>

text\<open>InvRecordCount states that for every processor, its local approximation @{text "c_glob c q"}
and the sum of all incoming progress updates @{text "GlobalIncomingInfoAt c q"} together are equal
to the sum of all capabilities in the system.\<close>

definition InvRecordCount where
  "InvRecordCount c \<equiv> \<forall>q. records c = GlobalIncomingInfoAt c q + c_glob c q"

lemma init_config_implies_InvRecordCount: "init_config c \<Longrightarrow> InvRecordCount c"
  by (simp add: InvRecordCount_def init_config_def GlobalIncomingInfo_def IncomingInfo_def)

lemma performop_preserves_InvRecordCount:
  assumes "InvRecordCount c0"
    and   "next_performop' c0 c1 p \<Delta>neg \<Delta>mint_msg \<Delta>mint_self"
  shows   "InvRecordCount c1"
proof -
  note change = next_performopD[OF assms(2)]
  note complex_change = next_performop_complexD[OF assms(2)]
  show "InvRecordCount c1"
    unfolding InvRecordCount_def complex_change
    by (auto intro: assms(1)[unfolded InvRecordCount_def, rule_format] simp: change)
qed

lemma sendupd_preserves_InvRecordCount:
  assumes "InvRecordCount c0"
    and   "next_sendupd' c0 c1 p tt"
  shows   "InvRecordCount c1"
proof -
  note change = next_sendupdD[OF assms(2)]
  note complex_change = next_sendupd_complexD[OF assms(2)]
  from assms(1) show "InvRecordCount c1"
    unfolding InvRecordCount_def complex_change change(5) by assumption
qed

lemma recvupd_preserves_InvRecordCount:
  assumes "InvRecordCount c0"
    and   "next_recvupd' c0 c1 p q"
  shows   "InvRecordCount c1"
proof -
  note change = next_recvupdD[OF assms(2)]
  note complex_change = next_recvupd_complexD[OF assms(2)]
  show "InvRecordCount c1"
    unfolding InvRecordCount_def complex_change change(4)
    by (auto simp: assms(1)[unfolded InvRecordCount_def, rule_format])
qed

lemma recvcap_preserves_InvRecordCount:
  assumes "InvRecordCount c0"
    and   "next_recvcap' c0 c1 p t"
  shows   "InvRecordCount c1"
proof -
  note change = next_recvcapD[OF assms(2)]
  note complex_change = next_recvcap_complexD[OF assms(2)]
  show "InvRecordCount c1"
    unfolding InvRecordCount_def complex_change change(4)
    by (auto simp: assms(1)[unfolded InvRecordCount_def, rule_format])
qed

lemma next_preserves_InvRecordCount: "InvRecordCount c0 \<Longrightarrow> next' c0 c1 \<Longrightarrow> InvRecordCount c1"
  unfolding next'_def
  apply (elim disjE)
  subgoal
    using performop_preserves_InvRecordCount by auto
  subgoal
    using sendupd_preserves_InvRecordCount by auto
  subgoal
    using recvupd_preserves_InvRecordCount by auto
  subgoal
    using recvcap_preserves_InvRecordCount by auto
  subgoal
    by simp
  done

lemma alw_InvRecordCount: "spec s \<Longrightarrow> alw (holds InvRecordCount) s"
  using lift_invariant_to_spec init_config_implies_InvRecordCount next_preserves_InvRecordCount
  by (metis (mono_tags, lifting) holds.elims(2) holds.elims(3) nxt.simps)

subsubsection\<open>InvCapsNonneg and InvRecordsNonneg\<close>

text\<open>InvCapsNonneg states that elements in a processor's @{text "c_caps c p"} always have
non-negative cardinality. InvRecordsNonneg lifts this result to @{text "records c"}\<close>

definition InvCapsNonneg :: "('p :: finite, 'a) configuration \<Rightarrow> bool" where
  "InvCapsNonneg c = (\<forall>p t. 0 \<le> zcount (c_caps c p) t)"

definition InvRecordsNonneg where
  "InvRecordsNonneg c = (\<forall>t. 0 \<le> zcount (records c) t)"

lemma init_config_implies_InvCapsNonneg: "init_config c \<Longrightarrow> InvCapsNonneg c"
  unfolding init_config_def InvCapsNonneg_def by simp

lemma performop_preserves_InvCapsNonneg:
  assumes "InvCapsNonneg c0"
    and   "next_performop' c0 c1 p \<Delta>\<^sub>m \<Delta>\<^sub>p\<^sub>1 \<Delta>\<^sub>p\<^sub>2"
  shows   "InvCapsNonneg c1"
  using assms unfolding InvCapsNonneg_def next_performop'_def Let_def
  by clarsimp (metis add.right_neutral add_mono_thms_linordered_semiring(1) of_nat_0_le_iff)

lemma sendupd_performs_InvCapsNonneg:
  assumes "InvCapsNonneg c0"
    and   "next_sendupd' c0 c1 p tt"
  shows   "InvCapsNonneg c1"
  using assms by (simp add: InvCapsNonneg_def next_sendupd'_def Let_def)

lemma recvupd_preserves_InvCapsNonneg:
  assumes "InvCapsNonneg c0"
    and   "next_recvupd' c0 c1 p q"
  shows   "InvCapsNonneg c1"
  using assms unfolding InvCapsNonneg_def next_recvupd'_def
  by simp

lemma recvcap_preserves_InvCapsNonneg:
  assumes "InvCapsNonneg c0"
    and   "next_recvcap' c0 c1 p t"
  shows   "InvCapsNonneg c1"
  using assms unfolding InvCapsNonneg_def next_recvcap'_def
  by simp

lemma next_preserves_InvCapsNonneg: "holds InvCapsNonneg s \<Longrightarrow> next s \<Longrightarrow> nxt (holds InvCapsNonneg) s"
  unfolding next'_def
  apply (elim disjE)
  subgoal
    using performop_preserves_InvCapsNonneg by auto
  subgoal
    using sendupd_performs_InvCapsNonneg by auto
  subgoal
    using recvupd_preserves_InvCapsNonneg by auto
  subgoal
    using recvcap_preserves_InvCapsNonneg by auto
  subgoal
    by simp
  done

lemma alw_InvCapsNonneg: "spec s \<Longrightarrow> alw (holds InvCapsNonneg) s"
  using lift_invariant_to_spec next_preserves_InvCapsNonneg init_config_implies_InvCapsNonneg
  by blast

lemma alw_InvRecordsNonneg: "spec s \<Longrightarrow> alw (holds InvRecordsNonneg) s"
  apply (rule alw_mp[where \<phi> = "holds InvCapsNonneg"])
  using alw_InvCapsNonneg apply assumption
  apply (rule all_imp_alw)
  unfolding InvCapsNonneg_def InvRecordsNonneg_def records_def
  apply (auto intro!: add_nonneg_nonneg sum_nonneg simp: zcount_sum)
  done

subsubsection\<open>Resulting lemmas\<close>

lemma pos_caps_pos_records:
  assumes "InvCapsNonneg c"
  shows "0 < zcount (c_caps c p) x \<Longrightarrow> 0 < zcount (records c) x"
proof -
  fix x
  assume "0 < zcount (c_caps c p) x"
  then have "0 < zcount (\<Sum>p\<in>UNIV. c_caps c p) x"
    using assms(1)[unfolded InvCapsNonneg_def]
    by (auto intro!: sum_pos2 simp: zcount_sum)
  then show "0 < zcount (records c) x"
    unfolding records_def by simp
qed

subsubsection\<open>SafeRecordsMono\<close>

text\<open>The records in the system are monotonic, i.e. once @{text "records c"} contains no records up
to some timestamp t, then it will stay that way forever.\<close>

definition SafeRecordsMono :: "('p :: finite, 'a) computation \<Rightarrow> bool" where
  "SafeRecordsMono s = (\<forall>t. RecordsVacantUpto (shd s) t \<longrightarrow> alw (holds (\<lambda>c. RecordsVacantUpto c t)) s)"

lemma performop_preserves_RecordsVacantUpto:
  assumes "RecordsVacantUpto c0 t"
    and   "next_performop' c0 c1 p \<Delta>neg \<Delta>mint_msg \<Delta>mint_self"
    and   "InvRecordsNonneg c1"
    and   "InvCapsNonneg c0"
  shows   "RecordsVacantUpto c1 t"
proof -
  note InvRecordsNonneg = assms(3)[rule_format]
  { fix s
    let ?\<Delta>pos = "timestamps (zmset_of \<Delta>mint_msg) + zmset_of \<Delta>mint_self"
    let ?\<Delta> = "?\<Delta>pos - zmset_of \<Delta>neg"
    note change = next_performopD[OF assms(2)]
    note complex_change = next_performop_complexD[OF assms(2)]
    assume s: "s \<le> t" "zcount (records c1) s \<noteq> 0"
    then have s_pos: "0 < zcount (records c1) s"
      using InvRecordsNonneg
      by (simp add: order_class.order.not_eq_order_implies_strict InvRecordsNonneg_def)
    have \<Delta>_in_nrec: "0 < zcount ?\<Delta> t \<Longrightarrow> \<exists>t'\<le>t. 0 < zcount (records c0) t'" for t
      apply (subst (asm) zcount_diff)
      apply (subst (asm) zcount_union)
      apply (drule zero_lt_diff)
       apply simp
      apply (drule zero_lt_add_disj)
        apply simp
       apply simp
      apply (erule disjE)
      subgoal
        apply (drule pos_image_zmset_obtain_pre[rotated])
         apply (auto dest!: change(4)[unfolded minting_msg_def, rule_format] pos_caps_pos_records[OF assms(4)] less_imp_le)
        done
      subgoal
        by (auto dest!: change(3)[unfolded minting_self_def, rule_format] pos_caps_pos_records[OF assms(4)])
      done
    have nrec0s: "zcount (records c0) s = 0"
      by (rule assms(1)[unfolded vacant_upto_def, rule_format, OF s(1)])
    have "zcount (records c1) s \<le> 0"
      unfolding complex_change
      apply (subst zcount_union)
      apply (subst nrec0s)
      apply (subst add_0)
      apply (rule ccontr)
      unfolding not_le
      apply (drule \<Delta>_in_nrec[of s])
      apply (meson assms(1) order_trans pos_zcount_in_zmset s(1) vacant_upto_def zcount_ne_zero_iff)
      done
    with s_pos have False
      by linarith
  }
  note r = this
  from assms show ?thesis
    unfolding next_performop'_def Let_def vacant_upto_def
    apply clarify
    apply (rule ccontr)
    apply (rule r)
     apply auto
    done
qed

lemma next'_preserves_RecordsVacantUpto:
  fixes c0 :: "('p::finite, 'a) configuration"
  shows "InvCapsNonneg c0 \<Longrightarrow> InvRecordsNonneg c1 \<Longrightarrow> RecordsVacantUpto c0 t \<Longrightarrow> next' c0 c1 \<Longrightarrow> RecordsVacantUpto c1 t"
  unfolding next'_def
  apply (elim disjE)
  subgoal
    by (auto intro: performop_preserves_RecordsVacantUpto)
  subgoal
    by (auto simp: next_sendupd'_def Let_def records_def)
  subgoal
    by (auto simp: next_recvupd'_def records_def)
  subgoal
    by (auto dest: next_recvcap_complexD)
  subgoal
    by simp
  done

lemma alw_next_implies_alw_SafeRecordsMono:
  "alw next s \<Longrightarrow> alw (holds InvCapsNonneg) s \<Longrightarrow> alw (holds InvRecordsNonneg) s \<Longrightarrow> alw SafeRecordsMono s"
  apply (coinduction arbitrary: s)
  subgoal for s
    unfolding spec_def next'_def SafeRecordsMono_def Let_def
    apply (rule exI[of _ s])
    apply safe
    subgoal for t
      apply (coinduction arbitrary: s rule: alw.coinduct)
      apply clarsimp
      apply (rule conjI)
       apply blast
      apply (erule alw.cases)
      apply clarsimp
      apply (metis (no_types, lifting) next'_def next'_preserves_RecordsVacantUpto alw_holds2)
      done
    apply blast
    done
  done

lemma alw_SafeRecordsMono: "spec s \<Longrightarrow> alw SafeRecordsMono s"
  by (auto intro!: alw_next_implies_alw_SafeRecordsMono alw_InvRecordsNonneg alw_InvCapsNonneg simp: spec_def)


subsubsection\<open>InvJustifiedII and InvJustifiedGII\<close>

text\<open>These two invariants state that any net-positive change in the sum of incoming progress updates
is "justified" by one of several statements being true.\<close>

definition InvJustifiedII where
  "InvJustifiedII c = (\<forall>k p q. justified (c_caps c p) (IncomingInfo c k p q))"

definition InvJustifiedGII where
  "InvJustifiedGII c = (\<forall>k p q. justified (records c) (GlobalIncomingInfo c k p q))"

text\<open>Given some zmset @{term M} justified wrt to @{term "caps c0 p"}, after a performop @{term "M + \<Delta>"} is justified wrt to
@{term "c_caps c1 p"}. This lemma captures the identical argument used for preservation of InvTempJustified
and InvJustifiedII.\<close>
lemma next_performop'_preserves_justified:
  assumes "justified (c_caps c0 p) M"
    and   "next_performop' c0 c1 p \<Delta>neg \<Delta>mint_msg \<Delta>mint_self"
    and   "InvCapsNonneg c0"
  shows   "justified (c_caps c1 p) (M + (timestamps (zmset_of \<Delta>mint_msg) + zmset_of \<Delta>mint_self - zmset_of \<Delta>neg))"
proof -
  let ?\<Delta>pos = "timestamps (zmset_of \<Delta>mint_msg) + zmset_of \<Delta>mint_self"
  let ?\<Delta> = "?\<Delta>pos - zmset_of \<Delta>neg"
  let ?M1 = "M + ?\<Delta>"
  note change = next_performopD[OF assms(2)]
  note complex_change = next_performop_complexD[OF assms(2)]
  note inv0 = assms(1)[unfolded InvJustifiedII_def justified_alt, rule_format]
  { fix k q t
    assume t: "0 < zcount ?M1 t"
    assume least: "\<forall>t'<t. zcount ?M1 t' \<le> 0"
    from t consider "0 < zcount M t" | "zcount M t \<le> 0" "0 < zcount ?\<Delta> t"
      by atomize_elim (auto simp: complex_change)
    then have "supported_strong ?M1 t \<or> (\<exists>t'<t. 0 < zcount (c_caps c1 p) t') \<or> zcount ?M1 t < zcount (c_caps c1 p) t"
    proof cases
      case 1 \<comment> \<open>@{term M} was already positive at @{term t} in @{term c0}\<close>
      note Mcount = 1
      note assms(1)[unfolded InvJustifiedII_def justified_alt, rule_format, OF Mcount]
      then consider
        "supported_strong M t" |
        "\<not> supported_strong M t" "\<exists>t'<t. 0 < zcount (c_caps c0 p) t'" |
        "\<forall>t'<t. zcount (c_caps c0 p) t' \<le> 0" "zcount M t < zcount (c_caps c0 p) t"
        by atomize_elim auto
      then show ?thesis
      proof cases
        case 1
        { assume nosupp: "\<not> supported_strong ?M1 t"
          assume "\<forall>t'<t. \<not> 0 < zcount (c_caps c1 p) t'"
          then have nocaps: "\<forall>t'<t. zcount (c_caps c1 p) t' = 0"
            using InvCapsNonneg_def assms(2) assms(3) order_class.le_less performop_preserves_InvCapsNonneg by fastforce
          from 1 obtain s where s: "s < t" "zcount M s < 0" "\<And>s'. s' < s \<Longrightarrow> zcount M s' = 0"
            unfolding nonpos_upto_def supported_strong_def
            apply atomize_elim
            apply (elim exE conjE)
            apply (drule order_zmset_exists_foundation_neg)
            apply (elim exE)
            subgoal for _ s
              apply (rule exI[of _ s])
              apply (rule conjI)
              using le_less_trans apply blast
              using less_imp_le order_trans order_class.order.not_eq_order_implies_strict apply blast
              done
            done
          have count1s: "0 \<le> zcount ?M1 s"
            apply (rule ccontr)
            apply (subst (asm) not_le)
            using nosupp[unfolded nonpos_upto_def supported_strong_def, simplified, rule_format]
            using least order.strict_trans2 s(1) apply fastforce
            done
          have \<Delta>inc: "0 < zcount ?\<Delta> s"
            using complex_change(3) count1s s(2) by auto
          have "0 < zcount (timestamps (zmset_of \<Delta>mint_msg)) s"
            using \<Delta>inc change(2)[rule_format, of s] nocaps[rule_format, OF s(1)]
            unfolding change(9) fun_upd_same zcount_union zcount_diff
            by linarith
          then obtain u where u: "u < s" "0 < zcount (c_caps c0 p) u" "\<forall>u'<u. zcount (c_caps c0 p) u' = 0"
            apply atomize_elim
            apply (drule pos_image_zmset_obtain_pre[rotated])
             apply simp
            apply clarify
            subgoal for p'
              apply simp
              apply (drule change(4)[unfolded minting_msg_def, rule_format])
              apply simp
              apply (elim exE conjE)
              apply (drule order_zmset_exists_foundation)
              apply clarsimp
              subgoal for s' u
                apply (rule exI[of _ u])
                apply clarsimp
                using assms(3)[unfolded InvCapsNonneg_def, rule_format]
                apply (metis le_less_trans order_class.order.not_eq_order_implies_strict)
                done
              done
            done
          have count1u: "zcount ?M1 u < 0"
            using complex_change(4)[of u] nocaps[unfolded change(9) fun_upd_same] order.strict_trans[OF u(1) s(1)] s(3)[OF u(1)] u(2) u(3)
            by auto
          then have "nonpos_upto ?M1 u"
            unfolding nonpos_upto_def
            using least order.strict_implies_order order.strict_trans1 s(1) u(1) by blast
          then have "supported_strong ?M1 t"
            using count1u order.strict_trans s(1) u(1) supported_strong_def by blast
          with nosupp have False
            by blast
        }
        then show ?thesis
          by blast
      next
        case 2
        { assume nosupp: "\<not> supported_strong ?M1 t"
          assume "\<forall>t'<t. \<not> 0 < zcount (c_caps c1 p) t'"
          then have nocaps: "\<forall>t'<t. zcount (c_caps c1 p) t' = 0"
            using InvCapsNonneg_def assms(2) assms(3) order_class.le_less performop_preserves_InvCapsNonneg by fastforce
          from 2(2) obtain s where s: "s < t" "0 < zcount (c_caps c0 p) s" "\<forall>s'<s. zcount (c_caps c0 p) s' = 0"
            apply atomize_elim
            apply (elim exE conjE)
            apply (drule order_zmset_exists_foundation)
            apply (elim exE conjE)
            subgoal for _ s
              apply (rule exI[of _ s])
              apply (rule conjI, simp)
              apply (rule conjI, simp)
              apply (intro allI impI)
              apply (rule ccontr)
              subgoal
              using assms(3)[unfolded InvCapsNonneg_def, rule_format]
              by (simp add: order_class.order.not_eq_order_implies_strict)
              done
            done
          have \<Delta>counts:
            "\<And>s. s < t \<Longrightarrow> count \<Delta>neg s = zcount (c_caps c0 p) s"
            "\<And>s. s < t \<Longrightarrow> count \<Delta>mint_self s = 0"
            "\<And>p s'. s' \<le> s \<Longrightarrow> count \<Delta>mint_msg (p,s') = 0"
            subgoal for s'
              using change(2) nocaps s(1) order_class.order.not_eq_order_implies_strict
              by (fastforce simp: change(9))
            subgoal for s'
              using nocaps[rule_format, of s']
              by (simp add: change(9) \<open>\<And>s'. s' < t \<Longrightarrow> int (count \<Delta>neg s') = zcount (c_caps c0 p) s'\<close>)
            subgoal for p s'
              using change(4)[unfolded minting_msg_def, rule_format, of "(p,s')"] s(3)
              by (force intro: ccontr)
            done
          have caps_le_ii0: "zcount (c_caps c0 p) s \<le> zcount M s"
          proof (rule ccontr)
            assume nle: "\<not> zcount (c_caps c0 p) s \<le> zcount M s"
            have "zcount ?M1 s < 0"
              unfolding complex_change(3)
              using complex_change(4) nle s(3) by (auto simp: \<Delta>counts(1,2)[OF s(1)])
            then show False
              using s(1) least
              by (force dest!: nosupp[unfolded supported_strong_def, simplified, rule_format] simp: nonpos_upto_def)
          qed
          with s(2) have count0s: "0 < zcount M s"
            by auto
          have False
            using inv0[OF count0s]
            apply (elim disj3_split)
            using 2(1) order.strict_trans s(1) supported_strong_def apply blast
            using s(3) apply auto []
            using caps_le_ii0 apply linarith
            done
        }
        then show ?thesis
          by blast
      next
        case 3
        then show ?thesis (* positive and negative changes to a least pointstamp are directly reflected in c_caps *)
          apply (intro disjI2)
          unfolding complex_change(3) change(9)
          apply (simp only: if_P zcount_union zcount_diff)
          apply (subst complex_change(4)[of t])
          using assms(3)[unfolded InvCapsNonneg_def, rule_format]
           apply (simp add: order_class.antisym)
          apply simp
          done
      qed
    next \<comment> \<open>Adding @{term \<Delta>} made @{term M} positive at @{term t} in @{term c}1\<close>
      case 2
      { assume nosupp: "\<not> supported_strong ?M1 t"
        assume "\<forall>t'<t. \<not> 0 < zcount (c_caps c1 p) t'"
        then have nocaps: "\<forall>t'<t. zcount (c_caps c1 p) t' = 0"
          using InvCapsNonneg_def assms(2) assms(3) order_class.le_less performop_preserves_InvCapsNonneg by metis
        assume "\<not> zcount ?M1 t < zcount (c_caps c1 p) t"
        then have caps_le: "zcount (c_caps c1 p) t \<le> zcount ?M1 t"
          by linarith
        from 2 have "count \<Delta>neg t < zcount ?\<Delta>pos t"
          by auto
        then have "0 < count \<Delta>mint_self t \<or> 0 < zcount (timestamps (zmset_of \<Delta>mint_msg)) t"
          by (metis 2(2) add.commute add.left_neutral not_gr_zero of_nat_0 zero_lt_diff zcount_diff zcount_of_mset zcount_union zcount_zmset_of_nonneg)
        then obtain s where s: "s \<le> t" "0 < zcount (c_caps c0 p) s" "\<forall>s'<s. zcount (c_caps c0 p) s' = 0"
          apply atomize_elim
          apply (elim disjE)
          subgoal
            apply simp
            apply (drule change(3)[unfolded minting_self_def, rule_format])
            apply (elim exE conjE)
            apply (drule order_zmset_exists_foundation)
            apply clarsimp
            subgoal for s' u
              apply (rule exI[of _ u])
              apply clarsimp
              using assms(3)[unfolded InvCapsNonneg_def, rule_format]
              apply (metis order.trans order_class.order.not_eq_order_implies_strict)
              done
            done
          subgoal
            apply (drule pos_image_zmset_obtain_pre[rotated])
             apply simp
            apply clarify
            subgoal for p'
              apply simp
              apply (drule change(4)[unfolded minting_msg_def, rule_format])
              apply simp
              apply (elim exE conjE)
              apply (drule order_zmset_exists_foundation)
              apply clarsimp
              subgoal for s' u
                apply (rule exI[of _ u])
                apply clarsimp
                using assms(3)[unfolded InvCapsNonneg_def, rule_format]
                apply (metis order.strict_trans1 less_imp_le order_class.order.not_eq_order_implies_strict)
                done
              done
            done
          done
        have \<Delta>counts:
          "\<And>s. s < t \<Longrightarrow> count \<Delta>neg s = zcount (c_caps c0 p) s"
          "\<And>s. s < t \<Longrightarrow> count \<Delta>mint_self s = 0"
          "\<And>p s'. s' \<le> s \<Longrightarrow> count \<Delta>mint_msg (p,s') = 0"
          subgoal for s'
            using change(2) nocaps s(1) order_class.order.not_eq_order_implies_strict
            by (fastforce simp: change(9))
          subgoal for s'
            using nocaps[rule_format, of s']
            by (simp add: change(9) \<open>\<And>s'. s' < t \<Longrightarrow> int (count \<Delta>neg s') = zcount (c_caps c0 p) s'\<close>)
          subgoal for p s'
            using change(4)[unfolded minting_msg_def, rule_format, of "(p,s')"] s(3)
            by (force intro: ccontr)
          done
        { assume less: "s < t"
          have caps_le_ii0: "zcount (c_caps c0 p) s \<le> zcount M s"
          proof (rule ccontr)
            assume nle: "\<not> zcount (c_caps c0 p) s \<le> zcount M s"
            have "zcount ?M1 s < 0"
              unfolding complex_change(3)
              using complex_change(4) nle s(3) by (auto simp: \<Delta>counts(1,2)[OF less])
            then show False
              using less least order.strict_trans2
              by (force dest!: nosupp[unfolded supported_strong_def, simplified, rule_format] simp: nonpos_upto_def)
          qed
          with s(2) have count0s: "0 < zcount M s"
            by auto
          have False
            using inv0[OF count0s]
            apply (elim disj3_split)
            subgoal
            proof -
              assume "supported_strong M s"
              then obtain u where u: "u < s" "zcount M u < 0"
                unfolding supported_strong_def
                by blast
              have "0 \<le> zcount ?M1 u"
                using least nosupp[unfolded supported_strong_def nonpos_upto_def, simplified, rule_format, of u] order.strict_trans[OF u(1) less]
                by fastforce
              then have "0 < zcount ?\<Delta>pos u"
                using \<Delta>counts(1)[of u] s(3) u(1) u(2) less by force
              then have "0 < count \<Delta>mint_self u \<or> 0 < zcount (timestamps (zmset_of \<Delta>mint_msg)) u"
                using gr0I by fastforce
              then obtain u' where "u' \<le> u" "0 < zcount (c_caps c0 p) u'"
                apply atomize_elim
                apply (elim disjE)
                subgoal
                  apply simp
                  apply (drule change(3)[unfolded minting_self_def, rule_format])
                  using s(1) s(2) apply blast
                  done
                subgoal
                  apply (drule pos_image_zmset_obtain_pre[rotated])
                   apply simp
                  apply clarify
                  subgoal for p'
                    apply simp
                    apply (drule change(4)[unfolded minting_msg_def, rule_format])
                    using order.strict_iff_order apply auto
                    done
                  done
                done
              then show False
                using s(3) u(1) by auto
            qed
            using s(3) apply auto []
            using caps_le_ii0 apply linarith
            done
        }
        moreover
        { assume eq: "s = t"
          have count0t: "0 < zcount M t"
            using eq caps_le change(9) complex_change(3,4) s(2,3) by auto
          have False
            using 2(1) count0t by auto
        }
        ultimately have False
          using order.not_eq_order_implies_strict s(1) by blast
      }
      then show ?thesis
        by blast
    qed
  }
  then show "justified (c_caps c1 p) ?M1"
    by (intro justified_leastI) blast
qed

lemma InvJustifiedII_implies_InvJustifiedGII:
  assumes "InvJustifiedII c"
    and   "InvCapsNonneg c"
  shows   "InvJustifiedGII c"
  using assms
  unfolding
    InvJustifiedGII_def
    InvJustifiedII_def
    GlobalIncomingInfo_def
    records_def
    InvCapsNonneg_def
  by (auto intro!: justified_add_records justified_sum)

lemma init_config_implies_InvJustifiedII: "init_config c \<Longrightarrow> InvJustifiedII c"
  by (simp add: init_config_def InvJustifiedII_def justified_alt IncomingInfo_def)

lemma performop_preserves_InvJustifiedII:
  assumes "InvJustifiedII c0"
    and   "next_performop' c0 c1 p \<Delta>neg \<Delta>mint_msg \<Delta>mint_self"
    and   "InvCapsNonneg c0"
  shows   "InvJustifiedII c1"
  unfolding InvJustifiedII_def
  apply clarify
  subgoal for k p' q
    apply (cases "p'=p")
    subgoal
      unfolding next_performop_complexD[OF assms(2)]
      apply (simp only: if_P)
      apply (rule next_performop'_preserves_justified[
            OF assms(1)[unfolded InvJustifiedII_def, rule_format, of p k q],
            OF assms(2,3)])
      done
    subgoal
      unfolding
        next_performopD[OF assms(2)]
        next_performop_complexD[OF assms(2)]
      using assms(1)[unfolded InvJustifiedII_def]
      by simp
    done
  done

lemma sendupd_preserves_InvJustifiedII:
  assumes "InvJustifiedII c0"
    and   "next_sendupd' c0 c1 p tt"
  shows   "InvJustifiedII c1"
  unfolding InvJustifiedII_def justified_alt supported_strong_def next_sendupdD(6)[OF assms(2)]
  apply (intro allI)
  subgoal for k p' q t
    apply (cases "k \<le> length (c_msg c0 p q)")
    subgoal
      apply (drule next_sendupd_complexD(4)[OF assms(2), of _ _ p'])
      apply (auto dest: assms(1)[unfolded InvJustifiedII_def justified_alt supported_strong_def, rule_format])
      done
    subgoal
      apply (subst (asm) not_le)
      apply (subst (1 2 3 4) next_sendupd_complexD(5)[OF assms(2), of _ _ p'])
        apply simp
       apply simp
      apply (cases "p'=p")
      subgoal
        apply rule
        apply (subst (asm) if_P)
         apply simp
        apply (subst (1 2 3) if_P)
          apply simp
         apply simp
        unfolding IncomingInfo_def
        apply (subst (asm) drop_all)
         apply simp
        apply (subst drop_all)
         apply simp
        apply (simp del: zcount_diff)
          \<comment> \<open>The justified condition ensures that anything remaining in temp satisfies this invariant\<close>
        apply (drule next_sendupdD(2)[OF assms(2), unfolded justified_alt supported_strong_def, rule_format])
        apply simp
        done
      subgoal
        by (auto intro!: assms(1)[unfolded InvJustifiedII_def justified_alt supported_strong_def, rule_format])
      done
    done
  done

lemma recvupd_preserves_InvJustifiedII:
  assumes "InvJustifiedII c0"
    and   "next_recvupd' c0 c1 p q"
  shows   "InvJustifiedII c1"
  using assms(1)
  unfolding
    InvJustifiedII_def
    next_recvupd_complexD[OF assms(2)]
    next_recvupdD[OF assms(2)]
  by auto

lemma recvcap_preserves_InvJustifiedII:
  assumes "InvJustifiedII c0"
    and   "next_recvcap' c0 c1 p t"
  shows   "InvJustifiedII c1"
  unfolding InvJustifiedII_def justified_alt supported_strong_def next_recvcap_complexD[OF assms(2)] next_recvcapD(5)[OF assms(2)]
  by (auto dest!: assms(1)[unfolded InvJustifiedII_def justified_alt supported_strong_def, rule_format])

lemma next'_preserves_InvJustifiedII:
  "InvCapsNonneg c0 \<Longrightarrow> InvJustifiedII c0 \<Longrightarrow> next' c0 c1 \<Longrightarrow> InvJustifiedII c1"
  using
    next'_def
    performop_preserves_InvJustifiedII
    recvcap_preserves_InvJustifiedII
    recvupd_preserves_InvJustifiedII
    sendupd_preserves_InvJustifiedII
  by blast

lemma alw_InvJustifiedII: "spec s \<Longrightarrow> alw (holds InvJustifiedII) s"
  apply (frule alw_InvCapsNonneg)
  unfolding spec_def
  apply (elim conjE)
  apply (subst (asm) holds.simps)
  apply (drule init_config_implies_InvJustifiedII)
  apply (coinduction arbitrary: s rule: alw.coinduct)
  apply (subst (asm) (1 2) alw_nxt)
  apply clarsimp
  using next'_preserves_InvJustifiedII apply blast
  done

lemma alw_InvJustifiedGII: "spec s \<Longrightarrow> alw (holds InvJustifiedGII) s"
  apply (frule alw_InvJustifiedII)
  apply (drule alw_InvCapsNonneg)
  apply (simp add: alw_iff_sdrop InvJustifiedII_implies_InvJustifiedGII)
  done

subsubsection\<open>InvTempJustified\<close>

definition InvTempJustified where
  "InvTempJustified c = (\<forall>p. justified (c_caps c p) (c_temp c p))"

lemma init_config_implies_InvTempJustified: "init_config c \<Longrightarrow> InvTempJustified c"
  unfolding init_config_def InvTempJustified_def
  using justified_add_records[OF justified_empty]
  by auto

lemma recvcap_preserves_InvTempJustified:
  assumes "InvTempJustified c0"
    and   "next_recvcap' c0 c1 p t"
  shows   "InvTempJustified c1"
  using assms(1)[unfolded InvTempJustified_def, rule_format, of p] assms(1)
  unfolding next_recvcapD[OF assms(2)] InvTempJustified_def
  by - (frule justified_add_records[of _ _ "{#t#}\<^sub>z"], auto)

lemma recvupd_preserves_InvTempJustified:
  assumes "InvTempJustified c0"
    and   "next_recvupd' c0 c1 p t"
  shows   "InvTempJustified c1"
  using assms(1)
  unfolding next_recvupdD[OF assms(2)] InvTempJustified_def
  by assumption

lemma sendupd_preserves_InvTempJustified:
  assumes "InvTempJustified c0"
    and   "next_sendupd' c0 c1 p tt"
  shows   "InvTempJustified c1"
  using assms(1)
  unfolding next_sendupdD[OF assms(2)] InvTempJustified_def
  using next_sendupdD(2)[OF assms(2)]
  by auto

lemma performop_preserves_InvTempJustified:
  assumes "InvTempJustified c0"
    and   "next_performop' c0 c1 p \<Delta>neg \<Delta>mint_msg \<Delta>mint_self"
    and   "InvCapsNonneg c0"
  shows   "InvTempJustified c1"
  unfolding InvTempJustified_def
  apply clarify
  subgoal for p'
    apply (cases "p'=p")
    subgoal
      unfolding next_performopD(5)[OF assms(2)] fun_upd_apply
      apply (simp only: if_P)
      apply (rule next_performop'_preserves_justified[
            OF assms(1)[unfolded InvTempJustified_def, rule_format, of p],
            OF assms(2,3)])
      done
    subgoal
      unfolding
        next_performopD[OF assms(2)]
        next_performop_complexD[OF assms(2)]
      using assms(1)[unfolded InvTempJustified_def]
      by simp
    done
  done

lemma next'_preserves_InvTempJustified:
  "InvCapsNonneg c0 \<Longrightarrow> InvTempJustified c0 \<Longrightarrow> next' c0 c1 \<Longrightarrow> InvTempJustified c1"
  using
    next'_def
    performop_preserves_InvTempJustified
    recvcap_preserves_InvTempJustified
    recvupd_preserves_InvTempJustified
    sendupd_preserves_InvTempJustified
  by blast

lemma alw_InvTempJustified: "spec s \<Longrightarrow> alw (holds InvTempJustified) s"
  apply (frule alw_InvCapsNonneg)
  unfolding spec_def
  apply (elim conjE)
  apply (subst (asm) holds.simps)
  apply (drule init_config_implies_InvTempJustified)
  apply (coinduction arbitrary: s rule: alw.coinduct)
  apply (subst (asm) (1 2) alw_nxt)
  apply clarsimp
  using next'_preserves_InvTempJustified apply blast
  done

subsubsection\<open>InvGlobNonposImpRecordsNonpos\<close>

text\<open>InvGlobNonposImpRecordsNonpos states that each processor's @{term "c_glob c q"} is a conservative
approximation of @{term "records c"}.\<close>

definition InvGlobNonposImpRecordsNonpos :: "('p :: finite, 'a) configuration \<Rightarrow> bool" where
  "InvGlobNonposImpRecordsNonpos c = (\<forall>t q. nonpos_upto (c_glob c q) t \<longrightarrow> nonpos_upto (records c) t)"

definition InvGlobVacantImpRecordsVacant :: "('p :: finite, 'a) configuration \<Rightarrow> bool" where
  "InvGlobVacantImpRecordsVacant c = (\<forall>t q. GlobVacantUpto c q t \<longrightarrow> RecordsVacantUpto c t)"

lemma invs_imp_InvGlobNonposImpRecordsNonpos:
  assumes "InvJustifiedGII c"
    and   "InvRecordCount c"
    and   "InvRecordsNonneg c"
  shows   "InvGlobNonposImpRecordsNonpos c"
  unfolding InvGlobNonposImpRecordsNonpos_def
  apply (rule ccontr)
  apply (clarsimp simp: nonpos_upto_def)
  subgoal for t q u
  proof -
    let ?GII = "GlobalIncomingInfoAt c q"
    assume gvu: "\<forall>sa\<le>t. zcount (c_glob c q) sa \<le> 0"
    assume uleqt: "u \<le> t"
    assume "\<not> zcount (records c) u \<le> 0"
      \<comment> \<open>u is pointstamp that violates @{term InvGlobNonposImpRecordsNonpos}\<close>
    with assms(2) have u: "0 < zcount (records c) u"
      by linarith
        \<comment> \<open>u' is the least pointstamp with positive @{term records}\<close>
    with uleqt obtain u' where u': "0 < zcount (records c) u'" "\<forall>u. 0 < zcount (records c) u \<longrightarrow> \<not> u < u'" "u' \<le> t"
      using order_zmset_exists_foundation[OF u] by auto
        \<comment> \<open>from the @{term records} count we know that GII also has positive count\<close>
    from u'(1,3) assms(2) gvu have pos_gii: "0 < zcount ?GII u'"
      unfolding InvRecordCount_def
      by (metis add_diff_cancel_left' diff_eq_eq less_add_same_cancel1 order_class.order.strict_trans1 zcount_diff)
        \<comment> \<open>Case distinction on which part of the partition GII's u is in\<close>
    { \<comment> \<open>Original proof from Abadi paper, change is justified by uprightness\<close>
      assume "supported_strong ?GII u'"
        \<comment> \<open>uprightness gives us a lesser pointstamp with negative count in GII..\<close>
      then obtain v where v: "v \<le> u'" "zcount ?GII v < 0"
        using order.strict_implies_order supported_strong_def by blast
          \<comment> \<open>..which is also negative in @{term records}..\<close>
      with u'(3) v(1) assms(2) have "zcount (records c) v < 0"
        by (metis (no_types, hide_lams) InvRecordCount_def add.commute gvu less_add_same_cancel2 order.trans not_le order_class.order.strict_trans2 zcount_union)
          \<comment> \<open>..contradicting InvNrecNonneg\<close>
      with assms(3) have "False"
        unfolding InvRecordsNonneg_def
        using order_class.leD by blast
    }
    moreover
    { \<comment> \<open>Change is justified by strictly lesser pointstamp in @{term records}\<close>
      assume "\<exists>t'<u'. 0 < zcount (records c) t'"
        \<comment> \<open>v is a strictly lesser positive count in @{term records}..\<close>
      then obtain v where v: "v < u'" "0 < zcount (records c) v"
        by auto
          \<comment> \<open>..which contradicts the fact that we obtained @{term u'} as the least, positive pointstamp in @{term records}\<close>
      with u'(2) have "False"
        by auto
    }
    moreover
    { \<comment> \<open>Change is justified by records\<close>
      assume "zcount ?GII u' < zcount (records c) u'"
      then have "0 < zcount (c_glob c q) u'"
        by (simp add: assms(2)[unfolded InvRecordCount_def, rule_format, of q])
      then have False
        using gvu u'(3) by auto
    }
    ultimately show False
      using pos_gii assms(1)[unfolded InvJustifiedGII_def justified_alt, rule_format, OF pos_gii]
      by auto
  qed
  done

text\<open>InvGlobVacantImpRecordsVacant is the one proved in the Abadi paper. We prove
InvGlobNonposImpRecordsNonpos, which implies this.\<close>
lemma invs_imp_InvGlobVacantImpRecordsVacant:
  assumes "InvJustifiedGII c"
    and   "InvRecordCount c"
    and   "InvRecordsNonneg c"
  shows   "InvGlobVacantImpRecordsVacant c"
proof -
  { fix p x
    assume "GlobVacantUpto c p x"
    then have "GlobNonposUpto c p x"
      unfolding nonpos_upto_def vacant_upto_def by simp
    note invs_imp_InvGlobNonposImpRecordsNonpos[OF assms, unfolded InvGlobNonposImpRecordsNonpos_def, rule_format, OF this]
    then have "RecordsVacantUpto c x"
      using assms(3)
      unfolding nonpos_upto_def vacant_upto_def InvRecordsNonneg_def
      by (simp add: order_class.order.antisym)
  }
  then show ?thesis
    unfolding InvGlobVacantImpRecordsVacant_def by simp
qed

lemma alw_InvGlobNonposImpRecordsNonpos: "spec s \<Longrightarrow> alw (holds InvGlobNonposImpRecordsNonpos) s"
  apply (frule alw_InvJustifiedGII)
  apply (frule alw_InvRecordCount)
  apply (drule alw_InvRecordsNonneg)
  apply (simp add: alw_iff_sdrop invs_imp_InvGlobNonposImpRecordsNonpos)
  done

lemma alw_InvGlobVacantImpRecordsVacant: "spec s \<Longrightarrow> alw (holds InvGlobVacantImpRecordsVacant) s"
  apply (frule alw_InvGlobNonposImpRecordsNonpos)
  apply (frule alw_InvJustifiedGII)
  apply (frule alw_InvRecordCount)
  apply (drule alw_InvRecordsNonneg)
  apply (simp add: alw_iff_sdrop invs_imp_InvGlobVacantImpRecordsVacant)
  done

subsubsection\<open>SafeGlobVacantUptoImpliesStickyNrec\<close>

text\<open>This is the main safety property proved in the Abadi paper.\<close>

lemma invs_imp_SafeGlobVacantUptoImpliesStickyNrec:
  "SafeRecordsMono s \<Longrightarrow> holds InvGlobVacantImpRecordsVacant s \<Longrightarrow> SafeGlobVacantUptoImpliesStickyNrec s"
  by (simp add: InvGlobVacantImpRecordsVacant_def SafeRecordsMono_def SafeGlobVacantUptoImpliesStickyNrec_def)

lemma alw_SafeGlobVacantUptoImpliesStickyNrec:
  "spec s \<Longrightarrow> alw SafeGlobVacantUptoImpliesStickyNrec s"
  by (meson alw_iff_sdrop invs_imp_SafeGlobVacantUptoImpliesStickyNrec alw_SafeRecordsMono alw_InvGlobVacantImpRecordsVacant)

subsubsection\<open>InvGlobNonposEqVacant\<close>

text\<open>The least pointstamps in glob are always positive, i.e. @{term nonpos_upto} and @{term vacant_upto} on glob
are equivalent.\<close>

definition InvGlobNonposEqVacant where
  "InvGlobNonposEqVacant c = (\<forall>q t. GlobVacantUpto c q t = GlobNonposUpto c q t)"

lemma invs_imp_InvGlobNonposEqVacant:
  assumes "InvRecordCount c"
    and   "InvJustifiedGII c"
    and   "InvRecordsNonneg c"
  shows   "InvGlobNonposEqVacant c"
proof -
  note safe = invs_imp_InvGlobNonposImpRecordsNonpos[OF assms(2,1,3), unfolded InvGlobNonposImpRecordsNonpos_def nonpos_upto_def, THEN spec2, THEN mp]
  note nonneg = assms(3)[unfolded InvRecordsNonneg_def, rule_format]
  note count = assms(1)[unfolded InvRecordCount_def, rule_format]
  { fix q t
    assume np: "GlobNonposUpto c q t"
    assume nv: "\<not> GlobVacantUpto c q t"
      \<comment> \<open>Obtain the least, negative pointstamp in glob\<close>
    obtain s where s: "s \<le> t" "zcount (c_glob c q) s < 0" "\<forall>s'<s. zcount (c_glob c q) s' = 0"
      apply atomize_elim
      using nv[unfolded vacant_upto_def]
      apply clarsimp
      apply (drule elem_order_zmset_exists_foundation)
      apply clarsimp
      subgoal for _ s
        apply (rule exI[of _ s])
        apply (meson order.ordering_axioms nonpos_upto_def np order_class.le_less ordering.trans zcount_ne_zero_iff)
        done
      done
        \<comment> \<open>No records @{term "s' \<le> s"} can exist, since that would violate InvGlobNonposImpRecordsNonpos\<close>
    have norec: "s' \<le> s \<Longrightarrow> zcount (records c) s' = 0" for s'
      by (metis (full_types) order.ordering_axioms nonneg nonpos_upto_def np order_class.antisym_conv ordering.trans s(1) safe)
        \<comment> \<open>Hence GII must be positive at @{term s}\<close>
    have gii: "zcount (GlobalIncomingInfoAt c q) s > 0"
      using count[of q] s(2) norec[of s, simplified]
      by (metis add.commute less_add_same_cancel1 zcount_union)
        \<comment> \<open>which means it must be justified by one of these three disjuncts\<close>
    then consider
      "supported_strong (GlobalIncomingInfoAt c q) s" |
      "\<exists>t'<s. 0 < zcount (records c) t'" |
      "zcount (GlobalIncomingInfoAt c q) s < zcount (records c) s"
      using assms(2)[unfolded InvJustifiedGII_def justified_alt, rule_format, OF gii]
      by atomize_elim auto
    then have False
    proof cases
      case 1 \<comment> \<open>@{term s} can't be @{term supported_strong}, since either glob or records would have to be positive at the support\<close>
      then show False
        using norec count s(3)
        unfolding supported_strong_def
        by (metis (full_types) add.commute add.left_neutral less_le preorder_class.less_irrefl zcount_union)
    next
      case 2 \<comment> \<open>no lesser capabilities exist\<close>
      then show ?thesis
        using norec s(2,3) order.order_iff_strict by auto
    next
      case 3 \<comment> \<open>no capabilities at @{term s} exist\<close>
      then show ?thesis
        unfolding norec[of s, simplified]
        using gii by auto
    qed
  }
  then show ?thesis
    unfolding InvGlobNonposEqVacant_def
    apply (intro allI)
    apply (rule iffI)
     apply (simp add: nonpos_upto_def vacant_upto_def)
    apply auto
    done
qed

lemma alw_InvGlobNonposEqVacant: "spec s \<Longrightarrow> alw (holds InvGlobNonposEqVacant) s"
  using
    alw_InvJustifiedGII
    alw_InvRecordCount
    alw_InvRecordsNonneg
    invs_imp_InvGlobNonposEqVacant
  by (metis alw_iff_sdrop holds.elims(2) holds.elims(3))

subsubsection\<open>InvInfoJustifiedWithII and InvInfoJustifiedWithGII\<close>

definition InvInfoJustifiedWithII where
  "InvInfoJustifiedWithII c = (\<forall>k p q. justified_with (c_caps c p) (InfoAt c k p q) (IncomingInfo c (k+1) p q))"

definition InvInfoJustifiedWithGII where
  "InvInfoJustifiedWithGII c = (\<forall>k p q. justified_with (records c) (InfoAt c k p q) (GlobalIncomingInfo c (k+1) p q))"

lemma init_config_implies_InvInfoJustifiedWithII: "init_config c \<Longrightarrow> InvInfoJustifiedWithII c"
  unfolding init_config_def InvInfoJustifiedWithII_def justified_with_def InfoAt_def
  by auto

text\<open>This proof relies heavily on the addition properties summarized in the lemma
@{thm "next_performop'_preserves_justified_with"}\<close>
lemma performop_preserves_InvInfoJustifiedWithII:
  assumes "InvInfoJustifiedWithII c0"
    and   "next_performop' c0 c1 p' \<Delta>neg \<Delta>mint_msg \<Delta>mint_self"
    and   "InvJustifiedII c0"
    and   "InvCapsNonneg c0"
  shows   "InvInfoJustifiedWithII c1"
  unfolding InvInfoJustifiedWithII_def
  apply (intro allI)
  subgoal for k p q
    apply (cases "p'=p")
    subgoal
      unfolding next_performop_complexD[OF assms(2)] next_performopD[OF assms(2)]
      apply (simp only: add_diff_eq if_P fun_upd_same)
      apply (subst (4) add.commute)
      apply (subst add.assoc[symmetric])
      apply (rule next_performop'_preserves_justified_with)
      using assms(1)[unfolded InvInfoJustifiedWithII_def] apply simp
      using assms(2) apply simp
      using assms(4)[unfolded InvCapsNonneg_def] apply simp
      using assms(3)[unfolded InvJustifiedII_def] apply simp
      done
    subgoal
      using assms(1)[unfolded InvInfoJustifiedWithII_def justified_with_def]
      by (auto simp: not_less justified_with_def next_performop_complexD[OF assms(2)] next_performopD[OF assms(2)])
    done
  done

lemma sendupd_preserves_InvInfoJustifiedWithII:
  assumes "InvInfoJustifiedWithII c0"
    and   "next_sendupd' c0 c1 p' tt"
    and   "InvTempJustified c0"
  shows   "InvInfoJustifiedWithII c1"
  unfolding InvInfoJustifiedWithII_def
proof (intro allI impI)
  fix k :: nat and p q
  note complex = next_sendupd_complexD[OF assms(2)]
  note change = next_sendupdD[OF assms(2)]
  consider
    "p' = p" "k < length (c_msg c0 p q)" |
    "p' = p" "k = length (c_msg c0 p q)" |
    "p' = p" "k > length (c_msg c0 p q)" |
    "p' \<noteq> p"
    by atomize_elim auto
  then show "justified_with (c_caps c1 p) (InfoAt c1 k p q) (IncomingInfo c1 (k+1) p q)"
  proof cases
    case 1
    then show ?thesis
      by (metis InvInfoJustifiedWithII_def Suc_eq_plus1 Suc_le_eq assms(1) change(6) complex(4,7) order_class.less_le)
  next
    case 2
    have temp0: "c_temp c0 p = InfoAt c1 k p q + c_temp c1 p"
      unfolding complex change
      using 2 by (auto simp: algebra_simps)
    have pi: "PositiveImplies (InfoAt c1 k p q) (c_temp c0 p)"
      unfolding PositiveImplies_def complex
      using 2(2) by (auto simp: InfoAt_def)
    have iitemp: "IncomingInfo c1 (k+1) p q = c_temp c1 p"
      unfolding IncomingInfo_def
      using 2 by (simp add: change)
    show ?thesis
      apply (rule PositiveImplies_justified_with)
      unfolding iitemp temp0[symmetric]
      unfolding change
      using assms(3) apply (simp add: InvTempJustified_def)
      using pi apply simp
      done
  next
    case 3
    then show ?thesis
      by (metis add_cancel_right_left complex(7) justified_with_leastI preorder_class.less_asym InfoAt_def zcount_union)
  next
    case 4
    then show ?thesis
      unfolding complex change
      using assms(1)[unfolded InvInfoJustifiedWithII_def, rule_format]
      apply simp
      done
  qed
qed

lemma recvupd_preserves_InvInfoJustifiedWithII:
  assumes "InvInfoJustifiedWithII c0"
    and   "next_recvupd' c0 c1 p q"
  shows   "InvInfoJustifiedWithII c1"
  using assms(1)
  unfolding
    InvInfoJustifiedWithII_def
    next_recvupd_complexD[OF assms(2)]
    next_recvupdD[OF assms(2)]
  by auto

lemma recvcap_preserves_InvInfoJustifiedWithII:
  assumes "InvInfoJustifiedWithII c0"
    and   "next_recvcap' c0 c1 p t"
  shows   "InvInfoJustifiedWithII c1"
  using assms(1)
  unfolding
    InvInfoJustifiedWithII_def
    next_recvcap_complexD[OF assms(2)]
    next_recvcapD[OF assms(2)]
  by simp

lemma invs_imp_InvInfoJustifiedWithGII:
  assumes "InvInfoJustifiedWithII c"
    and   "InvJustifiedII c"
    and   "InvCapsNonneg c"
  shows   "InvInfoJustifiedWithGII c"
  unfolding InvInfoJustifiedWithGII_def
  apply clarify
  subgoal for k p q
    unfolding GlobalIncomingInfo_def records_def
    apply (rule justified_with_add_records)
    subgoal
      apply (rule justified_with_sum[where x = p])
           apply simp
          apply simp
         apply simp
      using assms(1)[unfolded InvInfoJustifiedWithII_def, rule_format, of p k q]
        apply simp
      using assms(2)[unfolded InvJustifiedII_def] apply simp
      using assms(3)[unfolded InvCapsNonneg_def] apply simp
      done
    apply simp
    done
  done

lemma next'_preserves_InvInfoJustifiedWithII:
  assumes "InvInfoJustifiedWithII c0"
    and   "next' c0 c1"
    and   "InvCapsNonneg c0"
    and   "InvJustifiedII c0"
    and   "InvTempJustified c0"
  shows   "InvInfoJustifiedWithII c1"
  using assms unfolding next'_def
  apply (elim disjE exE)
      apply (drule (4) performop_preserves_InvInfoJustifiedWithII)
     apply (drule (3) sendupd_preserves_InvInfoJustifiedWithII)
    apply (drule (2) recvupd_preserves_InvInfoJustifiedWithII)
   apply (drule (2) recvcap_preserves_InvInfoJustifiedWithII)
  apply simp
  done

lemma alw_InvInfoJustifiedWithII: "spec s \<Longrightarrow> alw (holds InvInfoJustifiedWithII) s"
  apply (frule alw_InvCapsNonneg)
  apply (frule alw_InvJustifiedII)
  apply (frule alw_InvTempJustified)
  unfolding spec_def
  apply (elim conjE)
  apply (subst (asm) holds.simps)
  apply (drule init_config_implies_InvInfoJustifiedWithII)
  apply (coinduction arbitrary: s rule: alw.coinduct)
  apply (subst (asm) (1 2 3) alw_nxt)
  apply clarsimp
  using next'_preserves_InvInfoJustifiedWithII
  apply blast
  done

lemma alw_InvInfoJustifiedWithGII: "spec s \<Longrightarrow> alw (holds InvInfoJustifiedWithGII) s"
  by (metis alw_InvCapsNonneg alw_InvInfoJustifiedWithII alw_InvJustifiedII alw_iff_sdrop holds.elims(2,3) invs_imp_InvInfoJustifiedWithGII)


subsubsection\<open>SafeGlobMono and InvMsgInGlob\<close>

text\<open>The records in glob are monotonic. This implies the corollary InvMsgInGlob; No incoming message
carries a timestamp change that would cause glob to regress.\<close>

definition SafeGlobMono where
  "SafeGlobMono c0 c1 = (\<forall>p t. GlobVacantUpto c0 p t \<longrightarrow> GlobVacantUpto c1 p t)"

definition InvMsgInGlob where
  "InvMsgInGlob c = (\<forall>p q t. c_msg c p q \<noteq> [] \<longrightarrow> t \<in>#\<^sub>z hd (c_msg c p q) \<longrightarrow> (\<exists>t'\<le>t. 0 < zcount (c_glob c q) t'))"

lemma not_InvMsgInGlob_imp_not_SafeGlobMono:
  assumes "\<not> InvMsgInGlob c0"
    and   "InvGlobNonposEqVacant c0"
  shows   "\<exists>c1. next_recvupd c0 c1 \<and> \<not> SafeGlobMono c0 c1"
proof -
  note npeq0 = assms(2)[unfolded InvGlobNonposEqVacant_def, rule_format]
  from assms(1) obtain p q t c1 where t:
    "next_recvupd' c0 c1 p q"
    "t \<in>#\<^sub>z hd (c_msg c0 p q)"
    "GlobVacantUpto c0 q t"
    by (auto simp: InvMsgInGlob_def npeq0 nonpos_upto_def not_less dest!: ex_next_recvupd)
  have nvu: "\<not> GlobVacantUpto c1 q t"
    unfolding vacant_upto_def next_recvupdD(4)[OF t(1)]
    using t(2) t(3) vacant_upto_def by auto
  from t(3) nvu have "\<not> SafeGlobMono c0 c1"
    by (auto simp: SafeGlobMono_def)
  with t(1) show ?thesis
    by blast
qed

lemma GII_eq_GIA: "GlobalIncomingInfo c 1 p q = (if c_msg c p q = [] then GlobalIncomingInfoAt c q else GlobalIncomingInfoAt c q - hd (c_msg c p q))"
  unfolding GlobalIncomingInfo_def
  apply (cases "c_msg c p q = []")
   apply (simp add: IncomingInfo_def)
   apply (rule sum.cong[OF refl], simp)
  apply simp
  apply (subst diff_conv_add_uminus)
  apply (rule Sum_eq_pick_changed_elem)
     apply (auto simp: IncomingInfo_def drop_Suc sum_list_hd_tl algebra_simps)
  done

lemma recvupd_preserves_GlobVacantUpto:
  assumes "GlobVacantUpto c0 q t"
    and   "next_recvupd' c0 c1 p q"
    and   "InvInfoJustifiedWithGII c0"
    and   "InvGlobNonposEqVacant c1"
    and   "InvGlobVacantImpRecordsVacant c0"
    and   "InvRecordCount c0"
  shows   "GlobVacantUpto c1 q t"
proof (rule ccontr)
  note npeq1 = assms(4)[unfolded InvGlobNonposEqVacant_def, rule_format]
  note gvu0 = assms(1)[unfolded vacant_upto_def, rule_format]
  note nvu0 = assms(5)[unfolded InvGlobVacantImpRecordsVacant_def, rule_format, OF assms(1)]
  note recordcount = assms(6)[unfolded InvRecordCount_def zmultiset_eq_iff zcount_union, rule_format]
  note change = next_recvupdD[OF assms(2)]
  let ?\<kappa> = "hd (c_msg c0 p q)"
  from change(1) have ia\<kappa>: "?\<kappa> = InfoAt c0 0 p q"
    unfolding InfoAt_def by (simp add: hd_conv_nth)
  assume gvu1: "\<not> GlobVacantUpto c1 q t"
  obtain t' where t':
    "t' \<le> t"
    "0 < zcount (c_glob c1 q) t'"
    "zcount (c_glob c0 q) t' = 0"
    "\<forall>s<t'. zcount (c_glob c1 q) s \<le> 0"
    apply atomize_elim
    using gvu1
    unfolding npeq1 nonpos_upto_def
    apply (simp add: not_le)
    apply (elim exE conjE)
    apply (drule order_zmset_exists_foundation')
    apply (elim exE conjE)
    subgoal for s s'
      apply (rule exI[of _ s'])
      using gvu0 apply auto
      done
    done
  from t'(2,3) have count\<kappa>: "0 < zcount ?\<kappa> t'"
    by (auto simp: change(4))
  note assms(3)[unfolded InvInfoJustifiedWithGII_def justified_with_alt, rule_format, OF count\<kappa>[unfolded ia\<kappa>]]
  then consider
    "\<exists>s<t'. zcount (InfoAt c0 0 p q) s < 0 \<and> (\<forall>s'<s. zcount (InfoAt c0 0 p q) s' \<le> 0)" |
    "\<exists>s<t'. zcount (GlobalIncomingInfo c0 1 p q) s < 0 \<and> (\<forall>s'<s. zcount (InfoAt c0 0 p q) s' \<le> 0)"
    "\<nexists>s. s < t' \<and> zcount (InfoAt c0 0 p q) s < 0 \<and> (\<forall>s'<s. zcount (InfoAt c0 0 p q) s' \<le> 0)" |
    "\<exists>s<t'. 0 < zcount (records c0) s" |
    "zcount (InfoAt c0 0 p q + GlobalIncomingInfo c0 1 p q) t' < zcount (records c0) t'"
    by atomize_elim auto
  then show False
  proof cases
    case 1
    then obtain s where s: "s < t'" "zcount (InfoAt c0 0 p q) s < 0" "\<forall>s'<s. zcount (InfoAt c0 0 p q) s' \<le> 0"
      by blast
    then have globs: "zcount (c_glob c1 q) s < 0"
      using gvu0 ia\<kappa> t'(1) by (auto simp: change(4))
    have "zcount (c_glob c1 q) s \<le> 0"
      using globs by linarith
    then have "\<forall>s'\<le>s. zcount (c_glob c1 q) s' \<le> 0"
      using s(1) t'(4) by auto
    with globs show False
      by (auto simp: npeq1[unfolded nonpos_upto_def, symmetric] vacant_upto_def)
  next
    case 2
    then obtain s where s: "s < t'" "zcount (GlobalIncomingInfo c0 1 p q) s < 0" "\<forall>s'<s. zcount (InfoAt c0 0 p q) s' \<le> 0"
      by blast
    from 2(2) s(1,3) have "zcount (InfoAt c0 0 p q) s \<ge> 0"
      by force
    have rc: "zcount (records c0) s = 0"
      using order.strict_implies_order order.strict_trans2 nvu0 s(1) t'(1) vacant_upto_def by blast
    show False
      using assms(6) change(1,4) s(1,2) rc t'(4)
      unfolding GII_eq_GIA InvRecordCount_def fun_upd_same
      by clarsimp (metis add.commute add_mono_thms_linordered_field(1) not_le recordcount)
  next
    case 3
    with nvu0 t'(1) show False
      unfolding vacant_upto_def by auto
  next
    case 4
    then have "0 < zcount (c_glob c0 q) t'"
      using change(1) ia\<kappa> t'(3)
      unfolding GII_eq_GIA
      apply clarsimp
      apply (metis add.right_neutral preorder_class.less_irrefl recordcount)
      done
    then show False
      by (simp add: t'(3))
  qed
qed

lemma recvupd_imp_SafeGlobMono:
  assumes "next_recvupd' c0 c1 p q"
    and   "InvInfoJustifiedWithGII c0"
    and   "InvGlobNonposEqVacant c1"
    and   "InvGlobVacantImpRecordsVacant c0"
    and   "InvRecordCount c0"
  shows   "SafeGlobMono c0 c1"
  unfolding SafeGlobMono_def
  apply clarify
  subgoal for q' t
    apply (cases "q'=q")
    subgoal
      apply (rule recvupd_preserves_GlobVacantUpto)
      using assms apply simp_all
      done
    subgoal
      unfolding next_recvupdD[OF assms(1)]
      by simp
    done
  done

lemma next'_imp_SafeGlobMono:
  assumes "next' c0 c1"
    and   "InvInfoJustifiedWithGII c0"
    and   "InvGlobNonposEqVacant c1"
    and   "InvGlobVacantImpRecordsVacant c0"
    and   "InvRecordCount c0"
  shows   "SafeGlobMono c0 c1"
  using assms unfolding next'_def
  apply (elim disjE exE)
  subgoal
    by (auto simp: SafeGlobMono_def dest: next_performopD(7))
  subgoal
    by (auto simp: SafeGlobMono_def dest: next_sendupdD(5))
  subgoal
    by (auto intro: recvupd_imp_SafeGlobMono)
  subgoal
    by (auto simp: SafeGlobMono_def dest: next_recvcapD(4))
  subgoal
    by (simp add: SafeGlobMono_def)
  done

lemma invs_imp_InvMsgInGlob:
  fixes c0 :: "('p::finite, 'a) configuration"
  assumes "InvInfoJustifiedWithGII c0"
    and   "InvGlobNonposEqVacant c0"
    and   "InvGlobVacantImpRecordsVacant c0"
    and   "InvRecordCount c0"
    and   "InvJustifiedII c0"
    and   "InvCapsNonneg c0"
    and   "InvRecordsNonneg c0"
  shows   "InvMsgInGlob c0"
  using assms
  apply -
  apply (rule ccontr)
  apply (drule not_InvMsgInGlob_imp_not_SafeGlobMono[rotated, OF assms(2)])
  apply (elim exE conjE)
  apply (frule recvupd_imp_SafeGlobMono)
      apply simp
  subgoal
    apply (rule invs_imp_InvGlobNonposEqVacant)
      apply (drule (2) recvupd_preserves_InvRecordCount)
     apply (drule (1) recvupd_preserves_InvJustifiedII)
     apply (rule InvJustifiedII_implies_InvJustifiedGII)
      apply simp
     apply (drule (2) recvupd_preserves_InvCapsNonneg)
    apply (simp add: InvRecordsNonneg_def next_recvupd_complexD)
    done
    apply simp
   apply simp
  apply simp
  done

lemma alw_SafeGlobMono: "spec s \<Longrightarrow> alw (relates SafeGlobMono) s"
proof -
  assume spec: "spec s"
  { assume "alw next s"
    moreover assume "alw (holds InvGlobNonposEqVacant) s"
    moreover assume "alw (holds InvGlobVacantImpRecordsVacant) s"
    moreover assume "alw (holds InvInfoJustifiedWithGII) s"
    moreover assume "alw (holds InvRecordCount) s"
    ultimately have "alw (relates SafeGlobMono) s"
      apply (coinduction arbitrary: s)
      apply (clarsimp simp: relates_def intro!: next'_imp_SafeGlobMono)
      apply (rule conjI)
       apply (rule next'_imp_SafeGlobMono)
           apply auto [2]
         apply (subst (asm) alw_holds2)
         apply clarify
         apply (drule alwD)+
         apply simp
        apply auto
      done
  }
  with spec show ?thesis
    apply -
    apply (frule alw_InvGlobNonposEqVacant)
    apply (frule alw_InvGlobVacantImpRecordsVacant)
    apply (frule alw_InvInfoJustifiedWithGII)
    apply (frule alw_InvRecordCount)
    unfolding spec_def
    apply auto
    done
qed

lemma alw_InvMsgInGlob: "spec s \<Longrightarrow> alw (holds InvMsgInGlob) s"
  apply (frule alw_InvInfoJustifiedWithGII)
  apply (frule alw_InvGlobNonposEqVacant)
  apply (frule alw_InvGlobVacantImpRecordsVacant)
  apply (frule alw_InvRecordCount)
  apply (frule alw_InvJustifiedII)
  apply (frule alw_InvCapsNonneg)
  apply (drule alw_InvRecordsNonneg)
  apply (simp add: alw_iff_sdrop invs_imp_InvMsgInGlob)
  done

lemma SafeGlobMono_preserves_vacant:
  assumes "\<forall>t'\<le>t. zcount (c_glob c0 q) t' = 0"
    and   "(\<lambda>c0 c1. SafeGlobMono c0 c1)\<^sup>*\<^sup>* c0 c1"
  shows   "\<forall>t'\<le>t. zcount (c_glob c1 q) t' = 0"
  using assms(2,1)
  by (induct rule: rtranclp_induct)(auto simp: SafeGlobMono_def vacant_upto_def)

lemma rtranclp_all_imp_rel: "r\<^sup>*\<^sup>* x y \<Longrightarrow> \<forall>a b. r a b \<longrightarrow> r' a b \<Longrightarrow> r'\<^sup>*\<^sup>* x y"
  by (metis mono_rtranclp)

lemma rtranclp_rel_and_invar: "r\<^sup>*\<^sup>* x y \<Longrightarrow> Q x \<Longrightarrow> \<forall>a b. Q a \<and> r a b \<longrightarrow> P a b \<and> Q b \<Longrightarrow> (\<lambda>x y. P x y \<and> Q y)\<^sup>*\<^sup>* x y"
  apply (induct rule: rtranclp_induct)
   apply auto []
  apply (metis (no_types, lifting) rtranclp.simps)
  done

lemma rtranclp_invar_conclude_last: "(\<lambda>x y. P x y \<and> Q y)\<^sup>*\<^sup>* x y \<Longrightarrow> Q x \<Longrightarrow> Q y"
  using rtranclp.cases by fastforce

lemma InvCapsNonneg_imp_InvRecordsNonneg: "InvCapsNonneg c \<Longrightarrow> InvRecordsNonneg c"
  unfolding InvCapsNonneg_def InvRecordsNonneg_def records_def
  by (auto simp: zcount_sum intro!: sum_nonneg add_nonneg_nonneg)

lemma invs_imp_msg_in_glob:
  fixes c :: "('p::finite, 'a) configuration"
  assumes "M \<in> set (c_msg c p q)"
    and   "t \<in>#\<^sub>z M"
    and   "InvGlobNonposEqVacant c"
    and   "InvJustifiedII c"
    and   "InvInfoJustifiedWithII c"
    and   "InvGlobVacantImpRecordsVacant c"
    and   "InvRecordCount c"
    and   "InvCapsNonneg c"
    and   "InvMsgInGlob c"
  shows   "\<exists>t'\<le>t. 0 < zcount (c_glob c q) t'"
proof (rule ccontr)
  assume "\<not> (\<exists>t'\<le>t. 0 < zcount (c_glob c q) t')"
  then have vacant: "\<forall>t'\<le>t. zcount (c_glob c q) t' = 0"
    using assms(3)
    by (auto simp: InvGlobNonposEqVacant_def vacant_upto_def nonpos_upto_def)
  let ?c1 = "the (while_option (\<lambda>c. hd (c_msg c p q) \<noteq> M) (\<lambda>c. SOME c'. next_recvupd' c c' p q) c)"
  have r[simp]: "M \<in> set (c_msg c p q) \<Longrightarrow> c_msg (SOME c'. next_recvupd' c c' p q) p q = tl (c_msg c p q)" for c
    by (rule someI2_ex[OF ex_next_recvupd]) (auto simp: next_recvupd'_def)
  obtain c1 where while_some:
    "while_option (\<lambda>c. hd (c_msg c p q) \<noteq> M) (\<lambda>c. SOME c'. next_recvupd' c c' p q) c = Some c1"
    apply atomize_elim
    apply (rule measure_while_option_Some[where P="\<lambda>c. M \<in> set (c_msg c p q)"
          and f="\<lambda>c. Min {i. i < length (c_msg c p q) \<and> M = c_msg c p q ! i}"])
     apply clarsimp
     apply safe
      apply (metis list.exhaust_sel list.sel(2) set_ConsD)
     apply (subst Min_gr_iff)
       apply (auto simp: in_set_conv_nth nth_tl) [2]
     apply clarsimp
     apply (subst Min_less_iff)
       apply (auto simp: in_set_conv_nth nth_tl) []
      apply (clarsimp simp: in_set_conv_nth nth_tl)
      apply (metis (no_types, hide_lams) Suc_less_eq Suc_pred hd_conv_nth list.size(3) not_gr_zero not_less_zero)
     apply (clarsimp simp: in_set_conv_nth nth_tl)
    subgoal for s x
      by (rule exI[of _ "x-1"])
        (metis One_nat_def Suc_le_eq Suc_pred' diff_less diff_less_mono hd_conv_nth length_tl list.size(3) not_gr_zero nth_tl zero_less_Suc)
    apply (meson assms(1) in_set_conv_nth)
    done
  have c1: "(\<lambda>c0 c1. next_recvupd' c0 c1 p q)\<^sup>*\<^sup>* c c1" "c_msg c1 p q \<noteq> []" "hd (c_msg c1 p q) = M"
    subgoal
      apply (rule conjunct2)
      apply (rule while_option_rule[OF _ while_some, where P="\<lambda>d. M \<in> set (c_msg d p q) \<and> (\<lambda>c0 c1. next_recvupd' c0 c1 p q)\<^sup>*\<^sup>* c d"])
       apply (rule conjI)
        apply (metis list.sel(1) list.sel(3) list.set_cases r)
       apply (auto simp: assms(1) elim!: rtrancl_into_rtrancl[to_pred] intro: someI2_ex[OF ex_next_recvupd])
      done
    subgoal
      using while_option_rule[OF _ while_some, where P="\<lambda>c. M \<in> set (c_msg c p q)"]
      by (metis assms(1) empty_iff hd_Cons_tl list.set(1) r set_ConsD)
    subgoal
      using while_option_stop[OF while_some] by simp
    done
  have invs_trancl:
    "(\<lambda>c0 c1. SafeGlobMono c0 c1 \<and> InvJustifiedII c1 \<and> InvGlobNonposEqVacant c1 \<and> InvInfoJustifiedWithII c1 \<and> InvGlobVacantImpRecordsVacant c1 \<and> InvRecordCount c1 \<and> InvCapsNonneg c1)\<^sup>*\<^sup>* c c1"
    apply (rule rtranclp_rel_and_invar)
    using c1(1) apply simp
    using assms(3-8) apply simp
    apply clarsimp
    subgoal for a b
      apply (frule InvJustifiedII_implies_InvJustifiedGII)
       apply simp
      apply (frule recvupd_preserves_InvJustifiedII)
       apply simp
      apply (frule InvCapsNonneg_imp_InvRecordsNonneg)
      apply (frule next_preserves_InvRecordCount[of _ b])
       apply (auto simp: next'_def) []
      apply (frule recvupd_preserves_InvCapsNonneg[of _ b])
       apply simp
      apply (frule InvJustifiedII_implies_InvJustifiedGII[of b])
       apply simp
      apply (frule InvCapsNonneg_imp_InvRecordsNonneg[of b])
      apply (frule invs_imp_InvGlobNonposEqVacant[of b])
        apply simp_all [2]
      apply (frule recvupd_preserves_InvInfoJustifiedWithII[of _ b])
       apply simp
      apply (frule invs_imp_InvInfoJustifiedWithGII)
        apply simp_all [2]
      apply (frule invs_imp_InvInfoJustifiedWithGII[of b])
        apply simp_all [2]
      apply (intro conjI)
            apply (rule next'_imp_SafeGlobMono)
                apply (clarsimp simp: next'_def)
               apply simp_all [7]
        apply (rule invs_imp_InvGlobVacantImpRecordsVacant)
          apply simp_all
      done
    done
  then have trancl_mono: "(\<lambda>c0 c1. SafeGlobMono c0 c1)\<^sup>*\<^sup>* c c1"
    by (metis (no_types, lifting) rtranclp_all_imp_rel)
  then have vacant_c1: "\<forall>t'\<le>t. zcount (c_glob c1 q) t' = 0"
    by (rule SafeGlobMono_preserves_vacant[OF vacant])
  have InvMsgInGlob: "InvMsgInGlob c1"
    using rtranclp_invar_conclude_last[OF invs_trancl] assms
    apply (intro invs_imp_InvMsgInGlob)
    using invs_imp_InvInfoJustifiedWithGII InvCapsNonneg_imp_InvRecordsNonneg apply blast+
    done
  have "\<exists>t'\<le>t. 0 < zcount (c_glob c1 q) t'"
    using InvMsgInGlob[unfolded InvMsgInGlob_def] c1(2,3) assms(1,2)
    by auto
  then show False
    using vacant_c1 by auto
qed

lemma alw_msg_glob: "spec s \<Longrightarrow>
  alw (holds (\<lambda>c. \<forall>p q t. (\<exists>M \<in> set (c_msg c p q). t \<in>#\<^sub>z M) \<longrightarrow> (\<exists>t'\<le>t. 0 < zcount (c_glob c q) t'))) s"
  apply (frule alw_InvGlobNonposEqVacant)
  apply (frule alw_InvJustifiedII)
  apply (frule alw_InvInfoJustifiedWithII)
  apply (frule alw_InvGlobVacantImpRecordsVacant)
  apply (frule alw_InvRecordCount)
  apply (frule alw_InvCapsNonneg)
  apply (drule alw_InvMsgInGlob)
  apply (coinduction arbitrary: s)
  apply clarsimp
  apply (rule conjI)
   apply clarify
   apply (rule invs_imp_msg_in_glob)
           apply auto [2]
  using holds.elims(2) apply blast+
  done

end

(*<*)
end
(*>*)