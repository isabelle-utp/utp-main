(*  Title:       Verification components with Kleene Algebras
    Author:      Jonathan Julián Huerta y Munive, 2020
    Maintainer:  Jonathan Julián Huerta y Munive <jonjulian23@gmail.com>
*)

section \<open> Verification components with KAT  \<close>

text \<open> We use Kleene algebras with tests to derive rules for verification condition generation and 
refinement laws. \<close>

theory HS_VC_KAT
  imports KAT_and_DRA.PHL_KAT

begin


subsection \<open> Hoare logic in KAT \<close> 

text \<open> Here we derive the rules of Hoare Logic. \<close>

notation t ("\<tt>\<tt>")

hide_const t

no_notation if_then_else ("if _ then _ else _ fi" [64,64,64] 63)
        and HOL.If ("(if (_)/ then (_)/ else (_))" [0, 0, 10] 10)
        and while ("while _ do _ od" [64,64] 63)

context kat (* mostly by Victor Gomes, Georg Struth *)
begin
 
\<comment> \<open> Definitions of Hoare Triple \<close>

definition Hoare :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("H") where
  "H p x q \<longleftrightarrow> \<tt>\<tt> p \<cdot> x \<le> x \<cdot> \<tt>\<tt> q" 

lemma H_consl: "\<tt>\<tt> p \<le> \<tt>\<tt> p' \<Longrightarrow> H p' x q \<Longrightarrow> H p x q"
  using Hoare_def phl_cons1 by blast

lemma H_consr: "\<tt>\<tt> q' \<le> \<tt>\<tt> q \<Longrightarrow> H p x q' \<Longrightarrow> H p x q"
  using Hoare_def phl_cons2 by blast         

lemma H_cons: "\<tt>\<tt> p \<le> \<tt>\<tt> p' \<Longrightarrow> \<tt>\<tt> q' \<le> \<tt>\<tt> q \<Longrightarrow> H p' x q' \<Longrightarrow> H p x q"
  by (simp add: H_consl H_consr)

\<comment> \<open> Skip \<close>

lemma H_skip:  "H p 1 p"
  by (simp add: Hoare_def)

\<comment> \<open> Abort \<close>

lemma H_abort: "H p 0 q"
  by (simp add: Hoare_def)

\<comment> \<open> Sequential composition \<close>

lemma H_seq: "H p x r \<Longrightarrow> H r y q \<Longrightarrow> H p (x \<cdot> y) q"
  by (simp add: Hoare_def phl_seq)

\<comment> \<open> Nondeterministic choice \<close>

lemma H_choice: "H p x q \<Longrightarrow> H p y q \<Longrightarrow> H p (x + y) q"
  using local.distrib_left local.join.sup.mono by (auto simp: Hoare_def)

\<comment> \<open> Conditional statement \<close>

definition kat_cond :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("if _ then _ else _" [64,64,64] 63) where
  "if p then x else y = (\<tt>\<tt> p \<cdot> x + n p \<cdot> y)"

lemma H_var: "H p x q \<longleftrightarrow> \<tt>\<tt> p \<cdot> x \<cdot> n q = 0"
  by (metis Hoare_def n_kat_3 t_n_closed)

lemma H_cond_iff: "H p (if r then x else y) q \<longleftrightarrow> H (\<tt>\<tt> p \<cdot> \<tt>\<tt> r) x q \<and> H (\<tt>\<tt> p \<cdot> n r) y q"
proof -
  have "H p (if r then x else y) q \<longleftrightarrow> \<tt>\<tt> p \<cdot> (\<tt>\<tt> r \<cdot> x + n r \<cdot> y) \<cdot> n q = 0"
    by (simp add: H_var kat_cond_def)
  also have "... \<longleftrightarrow> \<tt>\<tt> p \<cdot> \<tt>\<tt> r \<cdot> x \<cdot> n q + \<tt>\<tt> p \<cdot> n r \<cdot> y \<cdot> n q = 0"
    by (simp add: distrib_left mult_assoc)
  also have "... \<longleftrightarrow> \<tt>\<tt> p \<cdot> \<tt>\<tt> r \<cdot> x \<cdot> n q = 0 \<and> \<tt>\<tt> p \<cdot> n r \<cdot> y \<cdot> n q = 0"
    by (metis add_0_left no_trivial_inverse)
  finally show ?thesis
    by (metis H_var test_mult)
qed

lemma H_cond: "H (\<tt>\<tt> p \<cdot> \<tt>\<tt> r) x q \<Longrightarrow> H (\<tt>\<tt> p \<cdot> n r) y q \<Longrightarrow> H p (if r then x else y) q"
  by (simp add: H_cond_iff)

\<comment> \<open> While loop \<close>

definition kat_while :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("while _ do _" [64,64] 63) where
  "while b do x = (\<tt>\<tt> b \<cdot> x)\<^sup>\<star> \<cdot> n b"

definition kat_while_inv :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("while _ inv _ do _" [64,64,64] 63) where
  "while p inv i do x = while p do x"

lemma H_exp1: "H (\<tt>\<tt> p \<cdot> \<tt>\<tt> r) x q \<Longrightarrow> H p (\<tt>\<tt> r \<cdot> x) q"
  using Hoare_def n_de_morgan_var2 phl.ht_at_phl_export1 by auto

lemma H_while: "H (\<tt>\<tt> p \<cdot> \<tt>\<tt> r) x p \<Longrightarrow> H p (while r do x) (\<tt>\<tt> p \<cdot> n r)"
proof -
  assume a1: "H (\<tt>\<tt> p \<cdot> \<tt>\<tt> r) x p"
  have "\<tt>\<tt> (\<tt>\<tt> p \<cdot> n r) = n r \<cdot> \<tt>\<tt> p \<cdot> n r"
    using n_preserve test_mult by presburger
  then show ?thesis
    using a1 Hoare_def H_exp1 conway.phl.it_simr phl_export2 kat_while_def by auto
qed

lemma H_while_inv: "\<tt>\<tt> p \<le> \<tt>\<tt> i \<Longrightarrow> \<tt>\<tt> i \<cdot> n r \<le> \<tt>\<tt> q \<Longrightarrow> H (\<tt>\<tt> i \<cdot> \<tt>\<tt> r) x i \<Longrightarrow> H p (while r inv i do x) q"
  by (metis H_cons H_while test_mult kat_while_inv_def)

\<comment> \<open> Finite iteration \<close>

lemma H_star: "H i x i \<Longrightarrow> H i (x\<^sup>\<star>) i"
  unfolding Hoare_def using star_sim2 by blast

lemma H_star_inv: 
  assumes "\<tt>\<tt> p \<le> \<tt>\<tt> i" and "H i x i" and "(\<tt>\<tt> i) \<le> (\<tt>\<tt> q)"
  shows "H p (x\<^sup>\<star>) q"
proof-
  have "H i (x\<^sup>\<star>) i"
    using assms(2) H_star by blast
  hence "H p (x\<^sup>\<star>) i"
    unfolding Hoare_def using assms(1) phl_cons1 by blast
  thus ?thesis 
    unfolding Hoare_def using assms(3) phl_cons2 by blast
qed

definition kat_loop_inv :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("loop _ inv _ " [64,64] 63)
  where "loop x inv i = x\<^sup>\<star>"

lemma H_loop: "H p x p \<Longrightarrow> H p (loop x inv i) p"
  unfolding kat_loop_inv_def by (rule H_star)

lemma H_loop_inv: "\<tt>\<tt> p \<le> \<tt>\<tt> i \<Longrightarrow> H i x i \<Longrightarrow> \<tt>\<tt> i \<le> \<tt>\<tt> q \<Longrightarrow> H p (loop x inv i) q"
  unfolding kat_loop_inv_def using H_star_inv by blast

\<comment> \<open> Invariants \<close>

lemma H_inv: "\<tt>\<tt> p \<le> \<tt>\<tt> i \<Longrightarrow> \<tt>\<tt> i \<le> \<tt>\<tt> q \<Longrightarrow> H i x i \<Longrightarrow> H p x q"
  by (rule_tac p'=i and q'=i in H_cons)

lemma H_inv_plus: "\<tt>\<tt> i = i \<Longrightarrow> \<tt>\<tt> j = j \<Longrightarrow> H i x i \<Longrightarrow>  H j x j \<Longrightarrow>  H (i + j) x (i + j)"
  unfolding Hoare_def using combine_common_factor
  by (smt add_commute add.left_commute distrib_left join.sup.absorb_iff1 t_add_closed)

lemma H_inv_mult: "\<tt>\<tt> i = i \<Longrightarrow> \<tt>\<tt> j = j \<Longrightarrow> H i x i \<Longrightarrow>  H j x j \<Longrightarrow>  H (i \<cdot> j) x (i \<cdot> j)"
  unfolding Hoare_def by (smt n_kat_2 n_mult_comm t_mult_closure mult_assoc)

end


subsection \<open> refinement KAT \<close> 

text \<open> Here we derive the laws of the refinement calculus. \<close>

class rkat = kat +
  fixes Ref :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes spec_def:  "x \<le> Ref p q \<longleftrightarrow> H p x q"

begin (* mostly by Victor Gomes, Georg Struth *)

lemma R1: "H p (Ref p q) q"
  using spec_def by blast

lemma R2: "H p x q \<Longrightarrow> x \<le> Ref p q"
  by (simp add: spec_def)

lemma R_cons: "\<tt>\<tt> p \<le> \<tt>\<tt> p' \<Longrightarrow> \<tt>\<tt> q' \<le> \<tt>\<tt> q \<Longrightarrow> Ref p' q' \<le> Ref p q"
proof -
  assume h1: "\<tt>\<tt> p \<le> \<tt>\<tt> p'" and h2: "\<tt>\<tt> q' \<le> \<tt>\<tt> q"
  have "H p' (Ref p' q') q'"
    by (simp add: R1)
  hence "H p (Ref p' q') q"
    using h1 h2 H_consl H_consr by blast
  thus ?thesis
    by (rule R2)
qed

\<comment> \<open> Skip \<close>

lemma R_skip: "1 \<le> Ref p p"
proof -
  have "H p 1 p"
    by (simp add: H_skip)
  thus ?thesis
    by (rule R2)
qed

\<comment> \<open> Abort \<close>

lemma R_zero_one: "x \<le> Ref 0 1"
proof -
  have "H 0 x 1"
    by (simp add: Hoare_def)
  thus ?thesis
    by (rule R2)
qed

lemma R_one_zero: "Ref 1 0 = 0"
proof -
  have "H 1 (Ref 1 0) 0"
    by (simp add: R1)
  thus ?thesis
    by (simp add: Hoare_def join.le_bot)
qed

lemma R_abort: "0 \<le> Ref p q"
  using bot_least by force

\<comment> \<open> Sequential composition \<close>

lemma R_seq: "(Ref p r) \<cdot> (Ref r q) \<le> Ref p q"
proof -
  have "H p (Ref p r) r" and "H r (Ref r q) q"
    by (simp add: R1)+
  hence "H p ((Ref p r) \<cdot> (Ref r q)) q"
    by (rule H_seq)
  thus ?thesis
    by (rule R2)
qed

\<comment> \<open> Nondeterministic choice \<close>

lemma R_choice: "(Ref p q) + (Ref p q) \<le> Ref p q"
  unfolding spec_def by (rule H_choice) (rule R1)+

\<comment> \<open> Conditional statement \<close>

lemma R_cond: "if v then (Ref (\<tt>\<tt> v \<cdot> \<tt>\<tt> p) q) else (Ref (n v \<cdot> \<tt>\<tt> p) q) \<le> Ref p q"
proof - 
  have "H (\<tt>\<tt> v \<cdot> \<tt>\<tt> p) (Ref (\<tt>\<tt> v \<cdot> \<tt>\<tt> p) q) q" and "H (n v \<cdot> \<tt>\<tt> p) (Ref (n v \<cdot> \<tt>\<tt> p) q) q"
    by (simp add: R1)+
  hence "H p (if v then (Ref (\<tt>\<tt> v \<cdot> \<tt>\<tt> p) q) else (Ref (n v \<cdot> \<tt>\<tt> p) q)) q"
    by (simp add: H_cond n_mult_comm)
 thus ?thesis
    by (rule R2)
qed

\<comment> \<open> While loop \<close>

lemma R_while: "while q do (Ref (\<tt>\<tt> p \<cdot> \<tt>\<tt> q) p) \<le> Ref p (\<tt>\<tt> p \<cdot> n q)"
proof -
  have "H (\<tt>\<tt> p \<cdot> \<tt>\<tt> q) (Ref (\<tt>\<tt> p \<cdot> \<tt>\<tt> q) p)  p" 
    by (simp_all add: R1)
  hence "H p (while q do (Ref (\<tt>\<tt> p \<cdot> \<tt>\<tt> q) p)) (\<tt>\<tt> p \<cdot> n q)"
    by (simp add: H_while)
  thus ?thesis
    by (rule R2)
qed

\<comment> \<open> Finite iteration \<close>

lemma R_star: "(Ref i i)\<^sup>\<star> \<le> Ref i i"
proof -
  have "H i (Ref i i) i"
    using R1 by blast
  hence "H i ((Ref i i)\<^sup>\<star>) i"
    using H_star by blast
  thus "Ref i i\<^sup>\<star> \<le> Ref i i"
    by (rule R2)
qed

lemma R_loop: "loop (Ref p p) inv i \<le> Ref p p"
  unfolding kat_loop_inv_def by (rule R_star)

\<comment> \<open> Invariants \<close>

lemma R_inv: "\<tt>\<tt> p \<le> \<tt>\<tt> i \<Longrightarrow> \<tt>\<tt> i \<le> \<tt>\<tt> q \<Longrightarrow> Ref i i \<le> Ref p q"
  using R_cons by force

end

end
