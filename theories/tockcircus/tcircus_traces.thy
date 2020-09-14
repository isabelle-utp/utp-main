section \<open> Timed Traces \<close>

theory tcircus_traces
  imports "UTP-Reactive-Designs.utp_rea_designs" "../rcircus/Refusal_Tests"
begin recall_syntax

subsection \<open> Events and Traces \<close>

instantiation list :: (type) monoid_mult
begin
definition [simp]: "one_list = []"
definition [simp]: "times_list = (@)"
instance by (intro_classes; simp)
end

lemma power_replicate: "[x]^n = replicate n x"
  by (induct n; simp)

text \<open> We try and characterise a tock-CSP like model using the standard Circus pattern and adapting
  the CML model and bits of the refusal testing model. First we represent traces. \<close>

datatype 'e tev = 
  Tock "'e set" \<comment> \<open> Passage of time, which we term and ``idle'' event \<close>
  | Evt 'e      \<comment> \<open> Other, ``active'' events \<close>

type_synonym 'e ttrace = "'e tev list"

subsection \<open> Idle Traces \<close>

definition tocks :: "'e set \<Rightarrow> 'e tev list set" where
"tocks X = {t. \<forall> e \<in> set(t). \<exists> Y. e = Tock Y \<and> Y \<subseteq> X}"

lemma tocks_Nil [simp]: "[] \<in> tocks X"
  by (simp add: tocks_def)

lemma tocks_Tock: "t \<in> tocks X \<Longrightarrow> set t \<subseteq> range Tock"
  by (auto simp add: tocks_def)

lemma tocks_Cons [intro]: "\<lbrakk> Y \<subseteq> X; t \<in> tocks X \<rbrakk> \<Longrightarrow> Tock Y # t \<in> tocks X"
  by (simp add: tocks_def)

lemma tocks_inter [intro!]: "\<lbrakk> t \<in> tocks X; t \<in> tocks Y \<rbrakk> \<Longrightarrow> t \<in> tocks (X \<inter> Y)"
  by (auto simp add: tocks_def, metis tev.inject(1))

lemma tocks_Evt [simp]: "Evt e # t \<in> tocks X = False"
  by (simp add: tocks_def)

lemma tocks_subset: "\<lbrakk> A \<subseteq> B; t \<in> tocks A\<rbrakk> \<Longrightarrow> t \<in> tocks B"
  by (auto simp add: tocks_def)

lemma tocks_append [simp]: "s @ t \<in> tocks X \<longleftrightarrow> (s \<in> tocks X \<and> t \<in> tocks X)"
  by (auto simp add: tocks_def)

lemma tocks_take [simp]: "s \<in> tocks X \<Longrightarrow> take n s \<in> tocks X"
  by (auto simp add: tocks_def, meson in_set_takeD)

lemma tocks_drop [simp]: "s \<in> tocks X \<Longrightarrow> drop n s \<in> tocks X"
  by (auto simp add: tocks_def, meson in_set_dropD)

lemma tocks_inter1 [dest]: "t \<in> tocks (X \<inter> Y) \<Longrightarrow> t \<in> tocks(X)"
  by (auto simp add: tocks_def)

lemma tocks_inter2 [dest]: "t \<in> tocks (X \<inter> Y) \<Longrightarrow> t \<in> tocks(Y)"
  by (auto simp add: tocks_def)

definition "mk_tocks n = replicate n (Tock {})"

lemma mk_tocks: "mk_tocks n \<in> tocks X"
  by (simp add: mk_tocks_def tocks_def)

lemma length_mk_tocks [simp]: "length (mk_tocks n) = n"
  by (simp add: mk_tocks_def)

subsubsection \<open> Tocks Order \<close>

text \<open> This order states that two traces have the same length, and agree on the order of events 
  and tocks, but each tock can refuse fewer events. \<close>

definition tock_ord :: "'e tev list \<Rightarrow> 'e tev list \<Rightarrow> bool" (infix "\<subseteq>\<^sub>t" 50) where
"(t\<^sub>1 \<subseteq>\<^sub>t t\<^sub>2) = (length t\<^sub>1 = length t\<^sub>2 \<and> (\<forall> i<length t\<^sub>1. t\<^sub>1!i = t\<^sub>2!i \<or> (\<exists> X Y. X \<subseteq> Y \<and> t\<^sub>1!i = Tock X \<and> t\<^sub>2!i = Tock Y)))"

lemma tock_ord_refl: "x \<subseteq>\<^sub>t x"
  by (simp add: tock_ord_def)

lemma tock_ord_trans: "\<lbrakk> x \<subseteq>\<^sub>t y; y \<subseteq>\<^sub>t z \<rbrakk> \<Longrightarrow> x \<subseteq>\<^sub>t z"
  by (auto simp add: tock_ord_def, smt dual_order.trans tev.inject(1))

lemma tock_ord_antisym: "\<lbrakk> x \<subseteq>\<^sub>t y; y \<subseteq>\<^sub>t x \<rbrakk> \<Longrightarrow> x = y"
  by (auto simp add: tock_ord_def, metis nth_equalityI subset_antisym tev.inject(1))

lemma tock_ord_least [simp]: "t \<subseteq>\<^sub>t [] \<longleftrightarrow> t = []"
  by (auto simp add: tock_ord_def)

lemma tock_ord_Nil [simp]: "[] \<subseteq>\<^sub>t t \<longleftrightarrow> t = []"
  by (auto simp add: tock_ord_def)

lemma tock_ord_append: "\<lbrakk> x\<^sub>1 \<subseteq>\<^sub>t y\<^sub>1; x\<^sub>2 \<subseteq>\<^sub>t y\<^sub>2 \<rbrakk> \<Longrightarrow> x\<^sub>1 @ x\<^sub>2 \<subseteq>\<^sub>t y\<^sub>1 @ y\<^sub>2"
  apply (auto simp add: tock_ord_def)
  by (smt diff_add_cancel_left' nat_add_left_cancel_less not_less nth_append)

lemma tock_ord_decompose:
  assumes  "x \<subseteq>\<^sub>t y @ z" 
  shows "take (length y) x \<subseteq>\<^sub>t y" "drop (length y) x \<subseteq>\<^sub>t z"
  using assms
  by (auto simp add: tock_ord_def)
     (metis add_leE not_less nth_append, metis nat_add_left_cancel_less nth_append_length_plus)

lemma tocks_order_power:
  assumes "t \<in> tocks A"
  shows "t \<subseteq>\<^sub>t [Tock A]^length t"
proof -
  from assms have "\<forall>i<length t. t ! i = Tock A \<or> (\<exists>X. X \<subseteq> A \<and> t ! i = Tock X)"
    by (simp add: tocks_def, meson in_set_conv_nth)
  thus ?thesis
    by (auto simp add: tock_ord_def power_replicate)
qed

lemma tock_power_in_tocks: "[Tock A]^n \<in> tocks A"
  by (simp add: tocks_def power_replicate)

lemma tocks_ord_closed:
  "\<lbrakk> t\<^sub>1 \<in> tocks A; t\<^sub>2 \<subseteq>\<^sub>t t\<^sub>1 \<rbrakk> \<Longrightarrow> t\<^sub>2 \<in> tocks A"
  by (auto simp add: tocks_def tock_ord_def in_set_conv_nth)
     (metis (no_types, hide_lams) nth_mem subset_trans tev.inject(1))

lemma tock_ord_Evt: "x \<subseteq>\<^sub>t Evt e # y \<Longrightarrow> (\<exists> t. x = Evt e # t \<and> t \<subseteq>\<^sub>t y)"
  apply (simp add: tock_ord_def)
  apply (rule_tac x="tl x" in exI)
  apply (auto)
  apply (metis hd_Cons_tl length_0_conv nat.simps(3) nth_Cons_0 tev.distinct(1) zero_less_Suc)
  apply (metis Nitpick.size_list_simp(2) Suc_less_eq nat.simps(3) nth_Cons_Suc nth_tl)
  done

lemma tock_ord_EvtE [elim!]: "\<lbrakk> x \<subseteq>\<^sub>t Evt e # y; \<And> t. \<lbrakk> x = Evt e # t; t \<subseteq>\<^sub>t y \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis tock_ord_Evt)

lemma tock_ord_Evt_hd_eq [simp]: "Evt e # x \<subseteq>\<^sub>t Evt f # y \<longleftrightarrow> (e = f \<and> x \<subseteq>\<^sub>t y)"
  by (auto simp add: tock_ord_def)
     (smt One_nat_def add.commute diff_add_cancel_left' length_Cons less_Suc0 list.size(4) nat_add_left_cancel_less not_less nth_Cons')

subsubsection \<open> Other Functions \<close>

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

text \<open> This function is from CML. It extracts the prefix of a trace that consists of tocks only,
  that is before an active event has occurred. \<close>

fun idleprefix :: "'e tev list \<Rightarrow> 'e tev list" where
"idleprefix [] = []" |
"idleprefix (Tock A # t) = (Tock A # idleprefix t)" |
"idleprefix (Evt x # t) = []"

lemma idleprefix_tocks [simp]: "idleprefix t \<in> tocks UNIV"
  by (induct t, simp_all, metis idleprefix.elims list.sel(3) subset_UNIV tocks_Cons tocks_Nil)

text \<open> The dual function extracts the events following an active event. \<close>

fun activesuffix :: "'e tev list \<Rightarrow> 'e tev list" where
"activesuffix [] = []" |
"activesuffix (Tock A # t) = activesuffix t" |
"activesuffix (Evt x # t) = (Evt x # t)"

text \<open> If an active suffix has elements, then the first element must be an event. \<close>

lemma hd_activesuffix:
  "activesuffix t \<noteq> [] \<Longrightarrow> hd(activesuffix t) \<in> range(Evt)"
  apply (induct t, simp_all)
  apply (rename_tac a t)
  apply (case_tac a)
   apply (simp_all)
  done

text \<open> A trace can always be decomposed into an idle prefix and an active suffix. \<close>

lemma idle_active_decomp:
  "idleprefix t @ activesuffix t = t"
  apply (induct t, simp_all)
  apply (rename_tac a t)
  apply (case_tac a)
   apply (simp_all)
  done

lemma idleprefix_concat_Evt [simp]: "idleprefix (t @ Evt e # t') = idleprefix t"
  by ((induct t; simp), metis idleprefix.simps(2) idleprefix.simps(3) tev.exhaust)

lemma idleprefix_prefix: "idleprefix(t) \<le> t"
  by (metis Prefix_Order.prefixI idle_active_decomp)

lemma tocks_idleprefix_fp [simp]:
  "t \<in> tocks A \<Longrightarrow> idleprefix(t) = t"
  by (metis hd_Cons_tl hd_activesuffix idle_active_decomp rangeE self_append_conv tocks_Evt tocks_append)

lemma tocks_iff_idleprefix_fp: "t \<in> tocks UNIV \<longleftrightarrow> idleprefix t = t"
  by (metis idleprefix_tocks tocks_idleprefix_fp)

lemma idleprefix_idem [simp]: "idleprefix (idleprefix t) = idleprefix t"
  using idleprefix_tocks tocks_idleprefix_fp by blast

text \<open> If we have two equal traces with idle prefixes, @{term x} and @{term y}, followed by active 
  events @{term a} and @{term b}, and then suffixes @{term as} and @{term bs}, then we can identify
  the prefixes, active events, and suffixes. \<close>

lemma tock_prefix_eq:
  assumes "x @ (Evt a # as) = y @ (Evt b # bs)" "x \<in> tocks X" "y \<in> tocks Y"
  shows "x = y \<and> a = b \<and> as = bs"
proof (safe)
  show 1:"x = y"
  proof (rule ccontr)
    assume neq: "x \<noteq> y"
    from assms(1) have "\<forall> i. (x @ (Evt a # as))!i = (y @ (Evt b # bs))!i"
      by simp
    show False
    proof (cases "length x" "length y" rule: linorder_cases)
      case less thus ?thesis
        by (metis assms(1) assms(3) less nth_append nth_append_length nth_mem rangeE subsetD tev.distinct(1) tocks_Tock)
    next
      case equal
      then show ?thesis
        by (metis append_eq_append_conv assms(1) neq)
    next
      case greater thus ?thesis
        by (metis assms(1) assms(2) nth_append nth_append_length nth_mem rangeE subsetD tev.distinct(1) tocks_Tock)
    qed
  qed
  show "a = b" 
    by (metis "1" assms(1) nth_append_length tev.inject(2))
  show "as = bs"
    by (metis "1" assms(1) list.inject same_append_eq)
qed

text \<open> Generalised variant of the above \<close>

lemma tock_prefix_eq':
  assumes "x @ (Evt a # as) = y @ z" "x \<in> tocks X" "y \<in> tocks Y" "hd(z) \<in> range(Evt)"
  shows "x = y \<and> z = Evt a # as"
proof -
  obtain b bs where "z = Evt b # bs"
    by (metis append.right_neutral assms(1) assms(3) assms(4) hd_Cons_tl image_iff tocks_Evt tocks_append)
  thus ?thesis
    by (metis assms(1) assms(2) assms(3) tock_prefix_eq)
qed


end