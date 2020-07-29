section \<open> tock-Circus \<close>

theory utp_tockcircus
imports "UTP-Reactive-Designs.utp_rea_designs" "rcircus/Refusal_Tests"
begin recall_syntax

subsection \<open> Foundations \<close>

text \<open> We try and characterise a tock-CSP like model using the standard Circus pattern and adapting
  the CML model and bits of the refusal testing model. First we represent traces. \<close>

datatype ('t, 'e) teva = Tock "'t" | Evt 'e

type_synonym 'e tev = "('e set, 'e) teva"

text \<open> We don't need a tick event, because this is handled by the $wait$ flag. Nor do we need to
  separate refusals and tocks. A refusal in tock-CSP (as I understand) can occur either (1) just
  before a tock occurs, or (2) at the end of a trace. We gain the former by embedding refusals
  in a tock (as in CML). We gain the latter by including the $ref'$ variable as in Circus. We encode
  the healthiness condition that a tock can't occur in a refusal before a tock event using
  the type system. \<close>

alphabet ('s, 'e) tc_vars = "('e tev list, 's) rsp_vars" +
  ref :: "(unit, 'e) teva refusal"

text \<open> The $ref$ variable is not simply a set, but a set augmented with the @{term "\<^bold>\<bullet>"} that denotes
  stability. We need this because tick-tock traces can end without a refusal. Note that unlike
  in the trace this is a refusal over @{typ "'e tev"} so that we can refuse tocks at the end. \<close>

text \<open> The interpretation of $wait$ changes to there being both stable (quiescent) and unstable.
  Extra information is needed for refusals. What is the meaning pericondition? \<close>

(* FIXME: Nasty hack below *)

declare des_vars.splits [alpha_splits del]
declare rp_vars.splits [alpha_splits del]
declare des_vars.splits [alpha_splits del]
declare rsp_vars.splits [alpha_splits del]
declare rsp_vars.splits [alpha_splits]
declare rp_vars.splits [alpha_splits]
declare des_vars.splits [alpha_splits]

type_synonym ('s,'e) taction  = "('s, 'e) tc_vars hrel"

definition tocks :: "'e set \<Rightarrow> 'e tev list set" where
"tocks X = {t. \<forall> e \<in> set(t). \<exists> Y. e = Tock Y \<and> Y \<subseteq> X}"

lemma tocks_Nil [simp]: "[] \<in> tocks X"
  by (simp add: tocks_def)

lemma tocks_Cons: "\<lbrakk> Y \<subseteq> X; t \<in> tocks X \<rbrakk> \<Longrightarrow> Tock Y # t \<in> tocks X"
  by (simp add: tocks_def)

lemma tocks_append [simp]: "\<lbrakk> s \<in> tocks X; t \<in> tocks X \<rbrakk> \<Longrightarrow> s @ t \<in> tocks X"
  by (auto simp add: tocks_def)

lemma tocks_take [simp]: "s \<in> tocks X \<Longrightarrow> take n s \<in> tocks X"
  by (auto simp add: tocks_def, meson in_set_takeD)

lemma tocks_drop [simp]: "s \<in> tocks X \<Longrightarrow> drop n s \<in> tocks X"
  by (auto simp add: tocks_def, meson in_set_dropD)

definition "mk_tocks n = replicate n (Tock {})"

lemma mk_tocks: "mk_tocks n \<in> tocks X"
  by (simp add: mk_tocks_def tocks_def)

lemma length_mk_tocks [simp]: "length (mk_tocks n) = n"
  by (simp add: mk_tocks_def)

fun events :: "'e tev list \<Rightarrow> 'e tev list" where
"events [] = []" |
"events (Tock A # t) = events t" |
"events (Evt x # t) = (Evt x # events t)"

lemma events_append [simp]: "events (xs @ ys) = events(xs) @ events(ys)"
  apply (induct xs, simp_all)
  apply (rename_tac x xs)
  apply (case_tac x)
  apply (simp_all)
done

fun idleprefix :: "'e tev list \<Rightarrow> 'e tev list" where
"idleprefix [] = []" |
"idleprefix (Tock A # t) = (Tock A # idleprefix t)" |
"idleprefix (Evt x # t) = []"

subsection \<open> Reactive Relation Constructs \<close>

no_utp_lift lift_state_rel

definition tc_stable :: "'s upred \<Rightarrow> ('e tev list, 's) uexpr \<Rightarrow> ((unit, 'e) teva set, 's) uexpr \<Rightarrow> ('s, 'e) taction" ("\<E>'(_, _, _')") where
[upred_defs]: "\<E>(s,t,E) = U(\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> = $tr @ \<lceil>t\<rceil>\<^sub>S\<^sub>< \<and> (\<forall> e\<in>\<lceil>E\<rceil>\<^sub>S\<^sub><. \<guillemotleft>e\<guillemotright> \<notin>\<^sub>\<R> $ref\<acute>))"

definition tc_unstable :: "'s upred \<Rightarrow> ('e tev list, 's) uexpr \<Rightarrow> ('s, 'e) taction" ("\<U>'(_, _')") where
[upred_defs]: "\<U>(s,t) = U(\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> = $tr @ \<lceil>t\<rceil>\<^sub>S\<^sub>< \<and> $ref\<acute> = \<^bold>\<bullet>)"

definition tc_final :: "'s upred \<Rightarrow> ('e tev list, 's) uexpr \<Rightarrow> 's usubst \<Rightarrow> ('s, 'e) taction" ("\<F>'(_, _, _')") where
[upred_defs]: "\<F>(s,t,\<sigma>) = U(\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> = $tr @ \<lceil>t\<rceil>\<^sub>S\<^sub>< \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S)" 

definition tc_time ("\<T>'(_, _')") where 
[upred_defs]: "tc_time X A = U(\<exists> t \<in> tocks \<lceil>UNIV - X\<rceil>\<^sub>S\<^sub><. $tr\<acute> = $tr @ \<guillemotleft>t\<guillemotright> \<and> length(\<guillemotleft>t\<guillemotright>) \<in> \<lceil>A\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> = $st)"

utp_lift_notation tc_stable
utp_lift_notation tc_unstable
utp_lift_notation tc_final (2)
utp_lift_notation tc_time

lemma [closure]: "\<E>(s, t, E) is RR"
  by (rel_auto)

lemma [closure]: "\<U>(s, t) is RR"
  by (rel_auto)

lemma [closure]: "\<F>(s, t, \<sigma>) is RR"
  by (rel_auto)

lemma [closure]: "\<T>(X, A) is RR"
  by (rel_auto)

lemma [unrest]: "$st\<acute> \<sharp> \<E>(s, t, E)"
  by (rel_auto)

lemma [unrest]: "$st\<acute> \<sharp> \<U>(s, t)"
  by (rel_auto)

text \<open> Unstable observations are subsumed by stable ones \<close>

lemma instability_subsumed: "\<E>(s, t, E) \<sqsubseteq> \<U>(s, t)"
  by (rel_auto)

lemma [rpred]: "\<F>(s\<^sub>1, t\<^sub>1, \<sigma>\<^sub>1) ;; \<F>(s\<^sub>2, t\<^sub>2, \<sigma>\<^sub>2) = \<F>(s\<^sub>1 \<and> \<sigma>\<^sub>1 \<dagger> s\<^sub>2, t\<^sub>1 @ \<sigma>\<^sub>1 \<dagger> t\<^sub>2, \<sigma>\<^sub>2 \<circ>\<^sub>s \<sigma>\<^sub>1)"
  by (rel_auto)

lemma [rpred]: "\<F>(s\<^sub>1, t\<^sub>1, \<sigma>) ;; \<E>(s\<^sub>2, t\<^sub>2, E) = \<E>(s\<^sub>1 \<and> \<sigma> \<dagger> s\<^sub>2, t\<^sub>1 @ \<sigma> \<dagger> t\<^sub>2, \<sigma> \<dagger> E)"
  by (rel_auto)

lemma [rpred]: "\<F>(s\<^sub>1, t\<^sub>1, \<sigma>) ;; \<U>(s\<^sub>2, t\<^sub>2) = \<U>(s\<^sub>1 \<and> \<sigma> \<dagger> s\<^sub>2, t\<^sub>1 @ \<sigma> \<dagger> t\<^sub>2)"
  by (rel_auto)

lemma split_time_dom:
  fixes l :: nat
  assumes "m\<^sub>1 + m\<^sub>2 \<le> l" "l \<le> m\<^sub>1 + m\<^sub>2 + (n\<^sub>1 + n\<^sub>2)"
  shows "(\<exists> n. n \<le> l \<and> m\<^sub>1 \<le> n \<and> m\<^sub>2 + n \<le> l \<and> n \<le> m\<^sub>1+n\<^sub>1 \<and> l \<le> m\<^sub>2+n\<^sub>2+n)"
  using assms
  by presburger

lemma [rpred]: "\<T>(X, {0}) ;; \<E>(s, t, E) = \<E>(s, t, E)"
  by (rel_simp)

lemma [rpred]: "\<T>(X, {0}) ;; \<U>(s, t) = \<U>(s, t)"
  by (rel_simp)

lemma [rpred]: "\<T>(X, {0}) ;; \<F>(s, t, \<sigma>) = \<F>(s, t, \<sigma>)"
  by (rel_auto)

lemma time_single_single [rpred]: "\<T>(X, {m}) ;; \<T>(X, {n}) = \<T>(X, {m+n})"
  apply rel_auto
  apply (rename_tac tr st x)
  apply (rule_tac x="tr @ take (\<lbrakk>m\<rbrakk>\<^sub>e st) x" in exI)
  apply (auto)
  apply (rule_tac x="drop (\<lbrakk>m\<rbrakk>\<^sub>e st) x" in bexI)
   apply (auto)
  done

lemma time_single_lessthan [rpred]: "\<T>(X, {m}) ;; \<T>(X, {0..<n}) = \<T>(X, {m..<m+n})"
  apply rel_auto
  apply (rename_tac tr st x)
  apply (rule_tac x="tr @ take (\<lbrakk>m\<rbrakk>\<^sub>e st) x" in exI)
  apply (auto)
  apply (rule_tac x="drop (\<lbrakk>m\<rbrakk>\<^sub>e st) x" in bexI)
   apply (auto)
  done

lemma time_single_atMost [rpred]: "\<T>(X, {m}) ;; \<T>(X, {0..n}) = \<T>(X, {m..m+n})"
  apply rel_auto
  apply (rename_tac tr st x)
  apply (rule_tac x="tr @ take (\<lbrakk>m\<rbrakk>\<^sub>e st) x" in exI)
  apply (auto)
  apply (rule_tac x="drop (\<lbrakk>m\<rbrakk>\<^sub>e st) x" in bexI)
   apply (auto)
  done

lemma time_single_atLeast [rpred]: "\<T>(X, {m}) ;; \<T>(X, {n..}) = \<T>(X, {m+n..})"
  apply rel_auto
  apply (rename_tac tr st x)
  apply (rule_tac x="tr @ take (\<lbrakk>m\<rbrakk>\<^sub>e st) x" in exI)
  apply (auto)
  apply (rule_tac x="drop (\<lbrakk>m\<rbrakk>\<^sub>e st) x" in bexI)
   apply (auto)
  done

lemma [rpred]: "\<T>(X, {m\<^sub>1..m\<^sub>1+n\<^sub>1}) ;; \<T>(X, {m\<^sub>2..m\<^sub>2+n\<^sub>2}) = \<T>(X, {m\<^sub>1 + m\<^sub>2..m\<^sub>1 + m\<^sub>2+(n\<^sub>1 + n\<^sub>2)})"
proof (rel_auto)
  fix tr st t

  assume a: "t \<in> tocks (UNIV - \<lbrakk>X\<rbrakk>\<^sub>e st)" "\<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e st + \<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e st \<le> length t" "length t \<le> \<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e st + \<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e st + (\<lbrakk>n\<^sub>1\<rbrakk>\<^sub>e st + \<lbrakk>n\<^sub>2\<rbrakk>\<^sub>e st)"
  then obtain n where n: "n \<le> length t" "\<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e st \<le> n" "\<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e st + n \<le> length t" "n \<le> \<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e st+\<lbrakk>n\<^sub>1\<rbrakk>\<^sub>e st" "length t \<le> \<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e st+\<lbrakk>n\<^sub>2\<rbrakk>\<^sub>e st+n"
    using split_time_dom by blast

  with a show "\<exists>tr' st'.
          (\<exists>x\<in>tocks (UNIV - \<lbrakk>X\<rbrakk>\<^sub>e st). tr' = tr @ x \<and> \<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e st \<le> length x \<and> length x \<le> \<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e st + \<lbrakk>n\<^sub>1\<rbrakk>\<^sub>e st \<and> st' = st) \<and>
          (\<exists>xa\<in>tocks (UNIV - \<lbrakk>X\<rbrakk>\<^sub>e st'). tr @ t = tr' @ xa \<and> \<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e st' \<le> length xa \<and> length xa \<le> \<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e st' + \<lbrakk>n\<^sub>2\<rbrakk>\<^sub>e st' \<and> st = st')"
    apply (rule_tac x="tr @ take n t" in exI)
    apply (rule_tac x="st" in exI)
    apply (auto)
    apply (rule_tac x="drop n t" in bexI)
     apply (auto)
    done
qed

subsection \<open> Basic Constructs \<close>

definition Div :: "('s,'e) taction" where
[rdes_def]: "Div = \<^bold>R(true\<^sub>r \<turnstile> \<U>(true, []) \<diamondop> false)"

text \<open> This is the same as Circus $Skip$, except that it includes a quiescent state. \<close>

definition Skip :: "('s,'e) taction" where
[rdes_def]: "Skip = \<^bold>R(true\<^sub>r \<turnstile> \<U>(true, []) \<diamondop> \<F>(true, [], id\<^sub>s))"

definition AssignsT :: "'s usubst \<Rightarrow> ('s,'e) taction" ("\<langle>_\<rangle>\<^sub>T") where
[upred_defs]: "AssignsT \<sigma> = \<^bold>R(true \<turnstile> \<U>(true, []) \<diamondop> \<F>(true, [], \<sigma>))" 

definition Stop :: "('s,'e) taction" where
[rdes_def]: "Stop = \<^bold>R(true\<^sub>r \<turnstile> \<T>({}, {0..}) ;; \<E>(true, [], {Tock ()}) \<diamondop> false)"

definition Stop\<^sub>U :: "('s,'e) taction" where
[rdes_def]: "Stop\<^sub>U = \<^bold>R(true\<^sub>r \<turnstile> \<E>(true, [], {}) \<diamondop> false)"

utp_const R2

term "\<E>(true, [], {Tock ()})"

term "(\<Sqinter> X \<bullet> \<U>(true, [Tock \<guillemotleft>X\<guillemotright>]))"

term tocks

term "\<E>(true, [], {Tock ()})"
term "\<E>(\<guillemotleft>t\<guillemotright> \<in> tocks (UNIV - {\<guillemotleft>a\<guillemotright>}), \<guillemotleft>t\<guillemotright>, {Tock (), Evt \<guillemotleft>a\<guillemotright>})"

term "tocks (UNIV - {a::'e})"

term "(\<Sqinter> t \<bullet> \<E>(\<guillemotleft>t \<in> tocks (UNIV - {a})\<guillemotright>, \<guillemotleft>t\<guillemotright>, {}))"

text \<open> SDF: Check the following definition against the tick-tock paper. It only allows prefixing
  of non-tock events for now. \<close>

definition DoT :: "'e \<Rightarrow> ('s, 'e) taction" ("do\<^sub>T'(_')") where
[rdes_def]: "DoT a =
  \<^bold>R(true\<^sub>r 
  \<turnstile> \<T>({\<guillemotleft>a\<guillemotright>}, {0..}) ;; \<E>(true, [], {Tock (), Evt \<guillemotleft>a\<guillemotright>})
  \<diamondop> \<T>({\<guillemotleft>a\<guillemotright>}, {0..}) ;; \<F>(true, [Evt \<guillemotleft>a\<guillemotright>], id\<^sub>s))"

lemma "((\<Sqinter> t \<bullet> \<E>(\<guillemotleft>t\<guillemotright> \<in> tocks UNIV \<and> length(\<guillemotleft>t\<guillemotright>) < n, \<guillemotleft>t\<guillemotright>, {Tock ()})) 
       \<or> (\<Sqinter> t \<bullet> \<U>(\<guillemotleft>t\<guillemotright> \<in> tocks UNIV \<and> length(\<guillemotleft>t\<guillemotright>) = n, \<guillemotleft>t\<guillemotright>))) is RR"
  by (simp add: closure)

lemma "(\<Sqinter> t \<bullet> \<F>(\<guillemotleft>t\<guillemotright> \<in> tocks UNIV \<and> length(\<guillemotleft>t\<guillemotright>) = n, \<guillemotleft>t\<guillemotright>, id\<^sub>s)) is RR"
  by (simp add: closure)


definition Wait :: "(nat, 's) uexpr \<Rightarrow> ('s,'e) taction" where
[rdes_def]: "Wait n = 
  \<^bold>R(true\<^sub>r 
    \<turnstile> ((\<T>({}, {0..<n}) ;; \<E>(true, [], {Tock ()})) 
       \<or> (\<T>({}, {n}) ;; \<U>(true, [])))
    \<diamondop> \<T>({}, {n}))"


lemma [closure]: "U(R2(&tt \<in> tocks UNIV \<and> length(&tt) = \<lceil>n\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> = $st)) is RR"
  by (rel_auto)


lemma [closure]: "U($tr\<acute> = $tr \<and> $st\<acute> = $st) is RR"
  apply (rel_auto)
  using minus_zero_eq by blast

lemma [closure]: "U(R1(&tt \<in> tocks UNIV) \<and> Tock () \<notin>\<^sub>\<R> $ref\<acute>) is RR"
  by (rel_auto)

lemma "Div ;; Skip = Div"
  by (rdes_simp)

lemma "Skip ;; Skip = Skip"
  by (rdes_eq)

lemma "Skip ;; Stop = Stop"
  by (rdes_eq)

lemma "Stop \<sqsubseteq> Div"
  by (rdes_refine)

utp_const lift_state_pre

lemma Wait_0: "Wait 0 = Skip"
  by (rdes_eq)

lemma Wait_Wait: "Wait m ;; Wait n = Wait(m + n)"
  apply (rdes_eq_split)
    apply (rel_auto)
   apply (simp_all add: rpred closure seqr_assoc[THEN sym])
  apply (rel_auto)
  done

text \<open> This is a pleasing result although @{const Wait} raises instability, this is swallowed up 
  by the sequential composition. \<close>

lemma Wait_Stop: "Wait m ;; Stop = Stop"
  by (rdes_eq_split, simp_all add: rpred closure seqr_assoc[THEN sym], rel_auto)

definition extChoice :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction \<Rightarrow> ('s, 'e) taction" where
"extChoice P Q =
  \<^bold>R(true\<^sub>r 
  \<turnstile> [$tr \<mapsto>\<^sub>s [], $tr\<acute> \<mapsto>\<^sub>s idleprefix(&tt)] \<dagger> (peri\<^sub>R(P) \<and> peri\<^sub>R(Q)) \<diamondop> false)"


text \<open> Pedro Comment: Renaming should be a relation rather than a function. \<close>

end