(*<*)
theory Infinite_Sequences
imports
  CIMP_pred
begin

(*>*)
section\<open> Infinite Sequences \label{sec:infinite_sequences}\<close>

text\<open>

Infinite sequences and some operations on them.

We use the customary function-based representation.

\<close>

type_synonym 'a seq = "nat \<Rightarrow> 'a"
type_synonym 'a seq_pred = "'a seq \<Rightarrow> bool"

definition suffix :: "'a seq \<Rightarrow> nat \<Rightarrow> 'a seq" (infixl "|\<^sub>s" 60) where
  "\<sigma> |\<^sub>s i \<equiv> \<lambda>j. \<sigma> (j + i)"

primrec stake :: "nat \<Rightarrow> 'a seq \<Rightarrow> 'a list" where
  "stake 0 \<sigma> = []"
| "stake (Suc n) \<sigma> = \<sigma> 0 # stake n (\<sigma> |\<^sub>s 1)"

primrec shift :: "'a list \<Rightarrow> 'a seq \<Rightarrow> 'a seq" (infixr \<open>@-\<close> 65) where
  "shift [] \<sigma> = \<sigma>"
| "shift (x # xs) \<sigma> = (\<lambda>i. case i of 0 \<Rightarrow> x | Suc i \<Rightarrow> shift xs \<sigma> i)"

(* FIXME misleading: this is \<sigma>(i, i+j). Use a bundle for this notation. FIXME move *)
abbreviation interval_syn ("_'(_ \<rightarrow> _')" [69, 0, 0] 70) where (* FIXME priorities *)
  "\<sigma>(i \<rightarrow> j) \<equiv> stake j (\<sigma> |\<^sub>s i)"

lemma suffix_eval: "(\<sigma> |\<^sub>s i) j = \<sigma> (j + i)"
unfolding suffix_def by simp

lemma suffix_plus: "\<sigma> |\<^sub>s n |\<^sub>s m = \<sigma> |\<^sub>s (m + n)"
unfolding suffix_def by (simp add: add.assoc)

lemma suffix_commute: "((\<sigma> |\<^sub>s n) |\<^sub>s m) = ((\<sigma> |\<^sub>s m) |\<^sub>s n)"
by (simp add: suffix_plus add.commute)

lemma suffix_plus_com: "\<sigma> |\<^sub>s m |\<^sub>s n = \<sigma> |\<^sub>s (m + n)"
proof -
  have "\<sigma> |\<^sub>s n |\<^sub>s m = \<sigma> |\<^sub>s (m + n)" by (rule suffix_plus)
  then show "\<sigma> |\<^sub>s m |\<^sub>s n = \<sigma> |\<^sub>s (m + n)" by (simp add: suffix_commute)
qed

lemma suffix_zero: "\<sigma> |\<^sub>s 0 = \<sigma>"
unfolding suffix_def by simp

lemma comp_suffix: "f \<circ> \<sigma> |\<^sub>s i = (f \<circ> \<sigma>) |\<^sub>s i"
unfolding suffix_def comp_def by simp

lemmas suffix_simps[simp] =
  comp_suffix
  suffix_eval
  suffix_plus_com
  suffix_zero

lemma length_stake[simp]: "length (stake n s) = n"
by (induct n arbitrary: s) auto

lemma shift_simps[simp]:
   "(xs @- \<sigma>) 0 = (if xs = [] then \<sigma> 0 else hd xs)"
   "(xs @- \<sigma>) |\<^sub>s Suc 0 = (if xs = [] then \<sigma> |\<^sub>s Suc 0 else tl xs @- \<sigma>)"
by (induct xs) auto

lemma stake_nil[simp]:
  "stake i \<sigma> = [] \<longleftrightarrow> i = 0"
by (cases i; clarsimp)

lemma stake_shift:
  "stake i (w @- \<sigma>) = take i w @ stake (i - length w) \<sigma>"
by (induct i arbitrary: w) (auto simp: neq_Nil_conv)

lemma shift_snth_less[simp]:
  assumes "i < length xs"
  shows "(xs @- \<sigma>) i = xs ! i"
using assms
proof(induct i arbitrary: xs)
  case (Suc i xs) then show ?case by (cases xs) simp_all
qed (simp add: hd_conv_nth nth_tl)

lemma shift_snth_ge[simp]:
  assumes "i \<ge> length xs"
  shows "(xs @- \<sigma>) i = \<sigma> (i - length xs)"
using assms
proof(induct i arbitrary: xs)
  case (Suc i xs) then show ?case by (cases xs) simp_all
qed simp

lemma shift_snth:
  "(xs @- \<sigma>) i = (if i < length xs then xs ! i else \<sigma> (i - length xs))"
by simp

lemma suffix_shift:
  "(xs @- \<sigma>) |\<^sub>s i = drop i xs @- (\<sigma> |\<^sub>s i - length xs)"
proof(induct i arbitrary: xs)
  case (Suc i xs) then show ?case by (cases xs) simp_all
qed simp

lemma stake_nth[simp]:
  assumes "i < j"
  shows "stake j s ! i = s i"
using assms by (induct j arbitrary: s i) (simp_all add: nth_Cons')

lemma stake_suffix_id:
  "stake i \<sigma> @- (\<sigma> |\<^sub>s i) = \<sigma>"
by (induct i) (simp_all add: fun_eq_iff shift_snth split: nat.splits)

lemma id_stake_snth_suffix:
  "\<sigma> = (stake i \<sigma> @ [\<sigma> i]) @- (\<sigma> |\<^sub>s Suc i)"
using stake_suffix_id
apply (metis Suc_diff_le append_Nil2 diff_is_0_eq length_stake lessI nat.simps(3) nat_le_linear shift_snth stake_nil stake_shift take_Suc_conv_app_nth)
done

lemma stake_add[simp]:
  "stake i \<sigma> @ stake j (\<sigma> |\<^sub>s i) = stake (i + j) \<sigma>"
apply (induct i arbitrary: \<sigma>)
 apply simp
apply auto
apply (metis One_nat_def plus_1_eq_Suc suffix_plus_com)
done

lemma stake_append: "stake n (u @- s) = take (min (length u) n) u @ stake (n - length u) s"
proof (induct n arbitrary: u)
  case (Suc n) then show ?case
    apply clarsimp
    apply (cases u)
    apply auto
    done
qed auto

lemma stake_shift_stake_shift:
  "stake i \<sigma> @- stake j (\<sigma> |\<^sub>s i) @- \<beta> = stake (i + j) \<sigma> @- \<beta>"
apply (induct i arbitrary: \<sigma>)
 apply simp
apply auto
apply (metis One_nat_def plus_1_eq_Suc suffix_plus_com)
done

lemma stake_suffix_drop:
  "stake i (\<sigma> |\<^sub>s j) = drop j (stake (i + j) \<sigma>)"
by (metis append_eq_conv_conj length_stake semiring_normalization_rules(24) stake_add)

lemma stake_suffix:
  assumes "i \<le> j"
  shows "stake j \<sigma> @- u |\<^sub>s i = \<sigma>(i \<rightarrow> j - i) @- u"
by (simp add: assms stake_suffix_drop suffix_shift)


subsection\<open>Decomposing safety and liveness \label{sec:infinite_sequences-safety-liveness}\<close>

text\<open>

Famously properties on infinite sequences can be decomposed into
@{emph \<open>safety\<close>} and @{emph \<open>liveness\<close>}
properties @{cite "AlpernSchneider:1985" and "Schneider:1987"}. See
@{cite [cite_macro=citet] "Kindler:1994"} for an overview.

\<close>

definition safety :: "'a seq_pred \<Rightarrow> bool" where
  "safety P \<longleftrightarrow> (\<forall>\<sigma>. \<not>P \<sigma> \<longrightarrow> (\<exists>i. \<forall>\<beta>. \<not>P (stake i \<sigma> @- \<beta>)))"

lemma safety_def2: \<comment> \<open>Contraposition gives the customary prefix-closure definition\<close>
  "safety P \<longleftrightarrow> (\<forall>\<sigma>. (\<forall>i. \<exists>\<beta>. P (stake i \<sigma> @- \<beta>)) \<longrightarrow> P \<sigma>)"
unfolding safety_def by blast

definition liveness :: "'a seq_pred \<Rightarrow> bool" where
  "liveness P \<longleftrightarrow> (\<forall>\<alpha>. \<exists>\<sigma>. P (\<alpha> @- \<sigma>))"

lemmas safetyI = iffD2[OF safety_def, rule_format]
lemmas safetyI2 = iffD2[OF safety_def2, rule_format]
lemmas livenessI = iffD2[OF liveness_def, rule_format]

lemma safety_False:
  shows "safety (\<lambda>\<sigma>. False)"
by (rule safetyI) simp

lemma safety_True:
  shows "safety (\<lambda>\<sigma>. True)"
by (rule safetyI) simp

lemma safety_state_prop:
  shows "safety (\<lambda>\<sigma>. P (\<sigma> 0))"
by (rule safetyI) auto

lemma safety_invariant:
  shows "safety (\<lambda>\<sigma>. \<forall>i. P (\<sigma> i))"
apply (rule safetyI)
apply clarsimp
apply (metis length_stake lessI shift_snth_less stake_nth)
done

lemma safety_transition_relation:
  shows "safety (\<lambda>\<sigma>. \<forall>i. (\<sigma> i, \<sigma> (i + 1)) \<in> R)"
apply (rule safetyI)
apply clarsimp
apply (metis (no_types, hide_lams) Suc_eq_plus1 add.left_neutral add_Suc_right add_diff_cancel_left' le_add1 list.sel(1) list.simps(3) shift_simps(1) stake.simps(2) stake_suffix suffix_def)
done

lemma safety_conj:
  assumes "safety P"
  assumes "safety Q"
  shows "safety (P \<^bold>\<and> Q)"
using assms unfolding safety_def by blast

lemma safety_always_eventually[simplified]:
  assumes "safety P"
  assumes "\<forall>i. \<exists>j\<ge>i. \<exists>\<beta>. P (\<sigma>(0 \<rightarrow> j) @- \<beta>)"
  shows "P \<sigma>"
using assms unfolding safety_def2
apply -
apply (drule_tac x=\<sigma> in spec)
apply clarsimp
apply (drule_tac x=i in spec)
apply clarsimp
apply (rule_tac x="(stake j \<sigma> @- \<beta>) |\<^sub>s i" in exI)
apply (simp add: stake_shift_stake_shift stake_suffix)
done

lemma safety_disj:
  assumes "safety P"
  assumes "safety Q"
  shows "safety (P \<^bold>\<or> Q)"
unfolding safety_def2 using assms
by (metis safety_always_eventually add_diff_cancel_right' diff_le_self le_add_same_cancel2)

text\<open>

The decomposition is given by a form of closure.

\<close>

definition M\<^sub>p :: "'a seq_pred \<Rightarrow> 'a seq_pred" where
  "M\<^sub>p P = (\<lambda>\<sigma>. \<forall>i. \<exists>\<beta>. P (stake i \<sigma> @- \<beta>))"

definition Safe :: "'a seq_pred \<Rightarrow> 'a seq_pred" where
  "Safe P = (P \<^bold>\<or> M\<^sub>p P)"

definition Live :: "'a seq_pred \<Rightarrow> 'a seq_pred" where
  "Live P = (P \<^bold>\<or> \<^bold>\<not>M\<^sub>p P)"

lemma decomp:
  "P = (Safe P \<^bold>\<and> Live P)"
unfolding Safe_def Live_def by blast

lemma safe:
  "safety (Safe P)"
unfolding Safe_def safety_def M\<^sub>p_def
apply clarsimp
apply (simp add: stake_shift)
apply (rule_tac x=i in exI)
apply clarsimp
apply (rule_tac x=i in exI)
apply clarsimp
done

lemma live:
  "liveness (Live P)"
proof(rule livenessI)
  fix \<alpha>
  have "(\<exists>\<beta>. P (\<alpha> @- \<beta>)) \<or> \<not>(\<exists>\<beta>. P (\<alpha> @- \<beta>))" by blast
  also have "?this \<longleftrightarrow> (\<exists>\<beta>. P (\<alpha> @- \<beta>) \<or> (\<forall>\<gamma>. \<not>P (\<alpha> @- \<gamma>)))" by blast
  also have "\<dots> \<longleftrightarrow> (\<exists>\<beta>. P (\<alpha> @- \<beta>) \<or> (\<exists>i. i = length \<alpha> \<and> (\<forall>\<gamma>. \<not>P (stake i (\<alpha> @- \<beta>) @- \<gamma>))))" by (simp add: stake_shift)
  also have "\<dots> \<longrightarrow> (\<exists>\<beta>. P (\<alpha> @- \<beta>) \<or> (\<exists>i. (\<forall>\<gamma>. \<not>P (stake i (\<alpha> @- \<beta>) @- \<gamma>))))" by blast
  finally have "\<exists>\<beta>. P (\<alpha> @- \<beta>) \<or> (\<exists>i. \<forall>\<gamma>. \<not> P (stake i (\<alpha> @- \<beta>) @- \<gamma>))" .
  then show "\<exists>\<sigma>. Live P (\<alpha> @- \<sigma>)" unfolding Live_def M\<^sub>p_def by simp
qed

text\<open>

@{cite "Sistla:1994"} proceeds to give a topological analysis of fairness. An \<^emph>\<open>absolute\<close>
liveness property is a liveness property whose complement is stable.

\<close>

definition absolute_liveness :: "'a seq_pred \<Rightarrow> bool" where \<comment> \<open> closed under prepending any finite sequence \<close>
  "absolute_liveness P \<longleftrightarrow> (\<exists>\<sigma>. P \<sigma>) \<and> (\<forall>\<sigma> \<alpha>. P \<sigma> \<longrightarrow> P (\<alpha> @- \<sigma>))"

definition stable :: "'a seq_pred \<Rightarrow> bool" where \<comment> \<open> closed under suffixes \<close>
  "stable P \<longleftrightarrow> (\<exists>\<sigma>. P \<sigma>) \<and> (\<forall>\<sigma> i. P \<sigma> \<longrightarrow> P (\<sigma> |\<^sub>s i))"

lemma absolute_liveness_liveness:
  assumes "absolute_liveness P"
  shows "liveness P"
using assms unfolding absolute_liveness_def liveness_def by blast

lemma stable_absolute_liveness:
  assumes "P \<sigma>"
  assumes "\<not>P \<sigma>'" \<comment>\<open> extra hypothesis \<close>
  shows "stable P \<longleftrightarrow> absolute_liveness (\<^bold>\<not> P)"
using assms unfolding stable_def absolute_liveness_def
apply auto
 apply (metis cancel_comm_monoid_add_class.diff_cancel drop_eq_Nil order_refl shift.simps(1) suffix_shift suffix_zero)
apply (metis stake_suffix_id)
done

(*
text\<open>

Fairness ala Sistla. Unmotivated.

FIXME safety properties are insensitive to fairness.
FIXME typically we prove \<open>sys \<longrightarrow> safety\<close>. The result below doesn't appear strong enough.
FIXME observe fairness is a special liveness property.

\<close>
*)

definition fairness :: "'a seq_pred \<Rightarrow> bool" where
  "fairness P \<longleftrightarrow> stable P \<and> absolute_liveness P"

lemma fairness_safety:
  assumes "safety P"
  assumes "fairness F"
  shows "(\<forall>\<sigma>. F \<sigma> \<longrightarrow> P \<sigma>) \<longleftrightarrow> (\<forall>\<sigma>. P \<sigma>)"
apply rule
using assms
apply clarsimp
unfolding safety_def fairness_def stable_def absolute_liveness_def
apply clarsimp
apply blast+
done

(*<*)

end
(*>*)
