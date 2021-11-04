(*  Title:       Verification components with MKAs
    Author:      Jonathan Julián Huerta y Munive, 2020
    Maintainer:  Jonathan Julián Huerta y Munive <jonjulian23@gmail.com>
*)

section \<open> Verification components with MKA \<close>

text \<open> We use the forward box operator of antidomain Kleene algebras to derive rules for weakest 
liberal preconditions (wlps) of regular programs. \<close>

theory HS_VC_MKA
  imports "KAD.Modal_Kleene_Algebra"

begin


subsection \<open> Verification in AKA \<close>

text \<open>Here we derive verification components with weakest liberal preconditions based on 
antidomain Kleene algebra \<close>

no_notation Range_Semiring.antirange_semiring_class.ars_r ("r")
        and HOL.If ("(if (_)/ then (_)/ else (_))" [0, 0, 10] 10)

notation zero_class.zero ("0")

context antidomain_kleene_algebra
begin

\<comment> \<open> Skip \<close>

lemma "|1] x = d x"
  using fbox_one .

\<comment> \<open> Abort \<close>

lemma "|0] q = 1"
  using fbox_zero .

\<comment> \<open> Sequential composition \<close>

lemma "|x \<cdot> y] q = |x] |y] q"
  using fbox_mult .

declare fbox_mult [simp]

\<comment> \<open> Nondeterministic choice \<close>

lemma "|x + y] q = |x] q \<cdot> |y] q"
  using fbox_add2 .

lemma le_fbox_choice_iff: "d p \<le> |x + y]q \<longleftrightarrow> (d p \<le> |x]q) \<and> (d p \<le> |y]q)"
  by (metis local.a_closure' local.ads_d_def local.dnsz.dom_glb_eq local.fbox_add2 local.fbox_def)

\<comment> \<open> Conditional statement \<close> (* by Victor Gomes, Georg Struth *)

definition aka_cond :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("if _ then _ else _" [64,64,64] 63) 
  where "if p then x else y = d p \<cdot> x + ad p \<cdot> y"

lemma fbox_export1: "ad p + |x] q = |d p \<cdot> x] q"
  using a_d_add_closure addual.ars_r_def fbox_def fbox_mult by auto

lemma fbox_cond [simp]: "|if p then x else y] q = (ad p + |x] q) \<cdot> (d p + |y] q)"
  using fbox_export1 local.ans_d_def local.fbox_mult 
  unfolding aka_cond_def ads_d_def fbox_def by auto

lemma fbox_cond2: "|if p then x else y] q = (d p \<cdot> |x] q) + (ad p \<cdot> |y] q)" (is "?lhs = ?d1 + ?d2")
proof -
  have obs: "?lhs = d p \<cdot> ?lhs + ad p \<cdot> ?lhs"
    by (metis (no_types, lifting) local.a_closure' local.a_de_morgan fbox_def ans_d_def
        ads_d_def local.am2 local.am5_lem local.dka.dsg3 local.dka.dsr5) 
  have "d p \<cdot> ?lhs = d p \<cdot> |x] q \<cdot> (d p + d ( |y] q))"
    using fbox_cond local.a_d_add_closure local.ads_d_def 
      local.ds.ddual.mult_assoc local.fbox_def by auto
  also have "... = d p \<cdot> |x] q"
    by (metis local.ads_d_def local.am2 local.dka.dns5 local.ds.ddual.mult_assoc local.fbox_def)
  finally have "d p \<cdot> ?lhs = d p \<cdot> |x] q" .
  moreover have "ad p \<cdot> ?lhs = ad p \<cdot> |y] q"
    by (metis add_commute fbox_cond local.a_closure' local.a_mult_add ads_d_def ans_d_def
        local.dnsz.dns5 local.ds.ddual.mult_assoc local.fbox_def)
  ultimately show ?thesis
    using obs by simp
qed

\<comment> \<open> While loop \<close> (* by Victor Gomes, Georg Struth *)

definition aka_whilei :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("while _ do _ inv _" [64,64,64] 63) where
  "while t do x inv i  = (d t \<cdot> x)\<^sup>\<star> \<cdot> ad t"

lemma fbox_frame: "d p \<cdot> x \<le> x \<cdot> d p \<Longrightarrow> d q \<le> |x] r \<Longrightarrow> d p \<cdot> d q \<le> |x] (d p \<cdot> d r)"    
  using dual.mult_isol_var fbox_add1 fbox_demodalisation3 fbox_simp by auto

lemma fbox_shunt: "d p \<cdot> d q \<le> |x] t \<longleftrightarrow> d p \<le> ad q + |x] t"
  by (metis a_6 a_antitone' a_loc add_commute addual.ars_r_def am_d_def da_shunt2 fbox_def)

lemma fbox_export2: "|x] p \<le> |x \<cdot> ad q] (d p \<cdot> ad q)"
proof -
  {fix t
   have "d t \<cdot> x \<le> x \<cdot> d p \<Longrightarrow> d t \<cdot> x \<cdot> ad q \<le> x \<cdot> ad q \<cdot> d p \<cdot> ad q"
     by (metis (full_types) a_comm_var a_mult_idem ads_d_def am2 ds.ddual.mult_assoc phl_export2)
   hence "d t \<le> |x] p \<Longrightarrow> d t \<le> |x \<cdot> ad q] (d p \<cdot> ad q)"
     by (metis a_closure' addual.ars_r_def ans_d_def dka.dsg3 ds.ddual.mult_assoc fbox_def fbox_demodalisation3)}
  thus ?thesis
    by (metis a_closure' addual.ars_r_def ans_d_def fbox_def order_refl)
qed

lemma fbox_while: "d p \<cdot> d t \<le> |x] p \<Longrightarrow> d p \<le> |(d t \<cdot> x)\<^sup>\<star> \<cdot> ad t] (d p \<cdot> ad t)"
proof -
  assume "d p \<cdot> d t \<le> |x] p"
  hence "d p \<le> |d t \<cdot> x] p"
    by (simp add: fbox_export1 fbox_shunt)
  hence "d p \<le> |(d t \<cdot> x)\<^sup>\<star>] p"
    by (simp add: fbox_star_induct_var)
  thus ?thesis
    using order_trans fbox_export2 by presburger
qed

lemma fbox_whilei: 
  assumes "d p \<le> d i" and "d i \<cdot> ad t \<le> d q" and "d i \<cdot> d t \<le> |x] i"
  shows "d p \<le> |while t do x inv i] q"
proof-
  have "d i \<le> |(d t \<cdot> x)\<^sup>\<star> \<cdot> ad t] (d i \<cdot> ad t)"
    using fbox_while assms by blast
  also have "... \<le> |(d t \<cdot> x)\<^sup>\<star> \<cdot> ad t] q"
    by (metis assms(2) local.dka.dom_iso local.dka.domain_invol local.fbox_iso)
  finally show ?thesis
    unfolding aka_whilei_def 
    using assms(1) local.dual_order.trans by blast 
qed

lemma fbox_seq_var: "p \<le> |x] p' \<Longrightarrow> p' \<le> |y] q \<Longrightarrow>  p \<le> |x \<cdot> y] q"
proof -
  assume h1: "p \<le> |x] p'" and h2: "p' \<le> |y] q"
  hence "|x] p' \<le> |x] |y] q"
    by (metis ads_d_def fbox_antitone_var fbox_dom fbox_iso)
  thus ?thesis
    by (metis dual_order.trans fbox_mult h1)
qed

lemma fbox_whilei_break: 
  "d p \<le> |y] i \<Longrightarrow> d i \<cdot> ad t \<le> d q \<Longrightarrow> d i \<cdot> d t \<le> |x] i \<Longrightarrow> d p \<le> |y \<cdot> (while t do x inv i)] q"
  apply (rule fbox_seq_var[OF _ fbox_whilei]) 
  using fbox_simp by auto

\<comment> \<open> Finite iteration \<close>

definition aka_loopi :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("loop _ inv _ " [64,64] 63)
  where "loop x inv i = x\<^sup>\<star>"

lemma "d p \<le> |x] p \<Longrightarrow> d p \<le> |x\<^sup>\<star>] p"
  using fbox_star_induct_var .

lemma fbox_loopi: "p \<le> d i \<Longrightarrow> d i \<le> |x] i \<Longrightarrow> d i \<le> d q \<Longrightarrow> p \<le> |loop x inv i] q"
  unfolding aka_loopi_def by (meson dual_order.trans fbox_iso fbox_star_induct_var)

lemma fbox_loopi_break: 
  "p \<le> |y] d i \<Longrightarrow> d i \<le> |x] i \<Longrightarrow> d i \<le> d q \<Longrightarrow> p \<le> |y \<cdot> (loop x inv i)] q"
  by (rule fbox_seq_var, force) (rule fbox_loopi, auto) 

\<comment> \<open> Invariants \<close>

lemma "p \<le> i \<Longrightarrow> i \<le> |x]i \<Longrightarrow> i \<le> q \<Longrightarrow> p \<le> |x]q"
  by (metis local.ads_d_def local.dpdz.dom_iso local.dual_order.trans local.fbox_iso)

lemma "p \<le> d i \<Longrightarrow> d i \<le> |x]i \<Longrightarrow> i \<le> d q \<Longrightarrow> p \<le> |x]q"
  by (metis local.a_4 local.a_antitone' local.a_subid_aux2 ads_d_def local.antisym fbox_def
      local.dka.dsg1 local.dual.mult_isol_var local.dual_order.trans local.order.refl)

lemma "(i \<le> |x] i) \<or> (j \<le> |x] j) \<Longrightarrow> (i + j) \<le> |x] (i + j)"
  (*nitpick*)
  oops

lemma "d i \<le> |x] i \<Longrightarrow> d j \<le> |x] j \<Longrightarrow> (d i + d j) \<le> |x] (d i + d j)"
  by (metis (no_types, lifting) dual_order.trans fbox_simp fbox_subdist join.le_supE join.le_supI)

lemma plus_inv: "i \<le> |x] i \<Longrightarrow> j \<le> |x] j \<Longrightarrow> (i + j) \<le> |x] (i + j)"
  by (metis ads_d_def dka.dsr5 fbox_simp fbox_subdist join.sup_mono order_trans)

lemma mult_inv: "d i \<le> |x] i \<Longrightarrow> d j \<le> |x] j \<Longrightarrow> (d i \<cdot> d j) \<le> |x] (d i \<cdot> d j)"
  using fbox_demodalisation3 fbox_frame fbox_simp by auto

end

end