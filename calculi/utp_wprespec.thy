section \<open> Weakest Prespecification \<close>

theory utp_wprespec
  imports "UTP.utp"
begin

definition wprespec :: "('b, 'c) urel \<Rightarrow> ('a, 'c) urel \<Rightarrow> ('a, 'b) urel" (infixr "\\" 70) where
[upred_defs]: "wprespec K Y = (\<not> ((\<not> Y) ;; K\<^sup>-))"

theorem wprespec: "R \<sqsubseteq> P ;; Q \<longleftrightarrow> Q \\ R \<sqsubseteq> P"
  by (rel_auto)

lemma wprespec1: "R \<sqsubseteq> (Q \\ R) ;; Q"
  by (simp add: wprespec)

lemma wprespec2: "Q \\ (P ;; Q) \<sqsubseteq> P"
  by (meson eq_iff wprespec)

lemma wprespec3: "Q \\ R \<sqsubseteq> II \<longleftrightarrow> R \<sqsubseteq> Q"
  by (metis seqr_left_unit wprespec)

lemma wprespec4: "Q \\ Q \<sqsubseteq> II"
  by (simp add: wprespec3)

lemma wprespec5: "II \\ P = P"
  by (metis eq_iff seqr_right_unit wprespec1 wprespec2)

lemma wprespec6: "Q \\ (R \<and> S) = ((Q \\ R) \<and> (Q \\ S))"
  by (meson eq_iff utp_pred_laws.inf.bounded_iff wprespec)
  
lemma wprespec6a: "Q \\ (\<And> n\<in>A \<bullet> R(n)) = (\<And> n\<in>A \<bullet> Q \\ R(n))"
  by (rel_auto)

lemma wprespec7: "(P \<or> Q) \\ R = ((P \\ R) \<and> (Q \\ R))"
  by (rel_auto)

lemma wprespec7a: "(\<Sqinter> i\<in>A \<bullet> P(i)) \\ R = (\<And> i\<in>A \<bullet> P(i) \\ R)"
  by (rel_auto)

lemma wprespec8: "(P ;; Q) \\ R = P \\ Q \\ R"
  by (simp add: seqr_assoc wprespec_def)

theorem wprespec9: "Q \\ R = \<Sqinter> {Y. R \<sqsubseteq> Y ;; Q}" (is "?lhs = ?rhs")
proof (rule antisym)
  show "?lhs \<sqsubseteq> ?rhs"
    by (metis Sup_least mem_Collect_eq wprespec)
  show "?rhs \<sqsubseteq> ?lhs"
    by (simp add: Sup_upper wprespec1)
qed

theorem wprespec10: "\<lbrakk>Q \\ R\<rbrakk>\<^sub>e (s\<^sub>0, s) = (\<forall> s'. \<lbrakk>Q\<rbrakk>\<^sub>e (s, s') \<longrightarrow> \<lbrakk>R\<rbrakk>\<^sub>e (s\<^sub>0, s'))"
  by (rel_auto)

lemma wprespec12: "Q\<^sup>- = ((\<not>Q) \\ (\<not>II))"
  by (rel_auto)

lemma wprespec13: "- (Q \\ R) = (-R \\ -Q) \\ -II"
  by (rel_auto)

lemma wprespec17: "\<langle>\<sigma>\<rangle>\<^sub>a \\ R = R ;; (\<langle>\<sigma>\<rangle>\<^sub>a \\ II)"
  by (rel_auto)

lemma wprespec17a: "\<langle>\<sigma>\<rangle>\<^sub>a \\ II = \<langle>\<sigma>\<rangle>\<^sub>a\<^sup>-"
  by (rel_auto)

theorem wlp_as_wprespec: "P wlp b = \<lfloor>P \\ b\<^sup>>\<rfloor>\<^sub>>"
  by (rel_auto)

end