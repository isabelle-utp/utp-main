section \<open> Abstract Separation Logic \<close>

theory utp_mem_aseplog
  imports utp_mem_prelim
begin

subsection \<open> Operators \<close>

definition empty_heap :: "('h :: pam, 's) spred" ("emp") where 
[upred_defs]: "emp = (&hp =\<^sub>u 0)"

definition sep_conj :: "('h :: sep_alg, 's) spred \<Rightarrow> ('h, 's) spred \<Rightarrow> ('h, 's) spred" (infixr "\<^bold>*" 35) where
[upred_defs]: "(P \<^bold>* Q) = (\<^bold>\<exists> (h\<^sub>0, h\<^sub>1) \<bullet> \<guillemotleft>h\<^sub>0 ## h\<^sub>1\<guillemotright> \<and> &hp =\<^sub>u \<guillemotleft>h\<^sub>0 + h\<^sub>1\<guillemotright> \<and> P\<lbrakk>\<guillemotleft>h\<^sub>0\<guillemotright>/&hp\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>h\<^sub>1\<guillemotright>/&hp\<rbrakk>)"

definition sep_impl :: "('h :: sep_alg, 's) spred \<Rightarrow> ('h, 's) spred \<Rightarrow> ('h, 's) spred" (infixr "-\<^bold>*" 25) where
[upred_defs]: "(P -\<^bold>* Q) = (\<^bold>\<forall> h\<^sub>0 \<bullet> \<guillemotleft>h\<^sub>0\<guillemotright> ##\<^sub>u &hp \<and> P\<lbrakk>\<guillemotleft>h\<^sub>0\<guillemotright>/&hp\<rbrakk> \<Rightarrow> Q\<lbrakk>(&hp + \<guillemotleft>h\<^sub>0\<guillemotright>)/&hp\<rbrakk>)"

subsection \<open> Algebraic Properties \<close>

lemma sep_conj_unit: 
  "(emp \<^bold>* P) = P" "(P \<^bold>* emp) = P"
  by (rel_auto)+

lemma sep_conj_false [simp] :
  "(false \<^bold>* P) = false" "(P \<^bold>* false) = false"
  by (rel_simp)+

lemma sep_conj_comm: "(P \<^bold>* Q) = (Q \<^bold>* P)"
  using compat_comm plus_pcomm by (rel_blast)

lemma sep_conj_assoc: "((P \<^bold>* Q) \<^bold>* R) = (P \<^bold>* (Q \<^bold>* R))"
  by (rel_auto, (metis compat_property plus_passoc)+)

lemma sep_conj_or_distl: "((P \<or> Q) \<^bold>* R) = ((P \<^bold>* R) \<or> (Q \<^bold>* R))"
  by (rel_auto)

lemma sep_conj_and_subdistl: "((P \<^bold>* R) \<and> (Q \<^bold>* R)) \<sqsubseteq> ((P \<and> Q) \<^bold>* R)"
  by (rel_auto)

lemma sep_conj_iso: "P \<sqsubseteq> Q \<Longrightarrow> (P \<^bold>* R) \<sqsubseteq> (Q \<^bold>* R)"
  by (rel_auto)

subsection \<open> Locality and Abstract Frame Rule \<close>

definition local_wrt where
[upred_defs]: "local_wrt p S = (\<forall> q. (S wp\<^sub>D (p \<^bold>* q) \<sqsubseteq> (p \<^bold>* (S wp\<^sub>D q))))"

lemma local_wrt_seq_closed:
  assumes "C is \<^bold>N" "D is \<^bold>N" "local_wrt r C" "local_wrt r D"
  shows "local_wrt r (C ;; D)"
proof -
  obtain c\<^sub>1 C\<^sub>2 where C: "C = c\<^sub>1 \<turnstile>\<^sub>n C\<^sub>2"
    by (metis assms(1) ndesign_form)
  obtain d\<^sub>1 D\<^sub>2 where D: "D = d\<^sub>1 \<turnstile>\<^sub>n D\<^sub>2"
    by (metis assms(2) ndesign_form)
  with assms(3-4) show ?thesis
    apply (simp add: C D local_wrt_def wp)
    apply (auto)
    apply (metis wlp_conj)
    apply (metis utp_pred_laws.inf.absorb_iff2 utp_pred_laws.le_infE wlp_conj)
    apply (metis utp_pred_laws.inf.absorb_iff2 utp_pred_laws.inf_assoc wlp_conj)
    done
qed

lemma frame_rule_aux:
  "\<lbrakk> c is \<^bold>N; local_wrt r c; {p} c {q}\<^sub>D \<rbrakk> \<Longrightarrow> {p \<^bold>* r} c {q \<^bold>* r}\<^sub>D"
  apply (simp add: wp_hoare_d_link)
  apply (simp add: local_wrt_def)
  apply (metis (no_types, lifting) dual_order.trans sep_conj_comm sep_conj_iso)
  done

end