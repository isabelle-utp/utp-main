subsection \<open> Design Hoare Logic \<close>

theory utp_des_hoare
  imports utp_des_prog
begin

definition HoareD :: "'s upred \<Rightarrow> 's hrel_des \<Rightarrow> 's upred \<Rightarrow> bool" ("{_}_{_}\<^sub>D") where
[upred_defs, ndes_simp]: "HoareD p S q = ((p \<turnstile>\<^sub>n \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> S)"

lemma assigns_hoare_d [hoare_safe]: "`p \<Rightarrow> \<sigma> \<dagger> q` \<Longrightarrow> {p}\<langle>\<sigma>\<rangle>\<^sub>D{q}\<^sub>D"
  by rel_auto

lemma skip_hoare_d: "{p}II\<^sub>D{p}\<^sub>D"
  by (rel_auto)

lemma assigns_backward_hoare_d: 
  "{\<sigma> \<dagger> p}\<langle>\<sigma>\<rangle>\<^sub>D{p}\<^sub>D"
  by rel_auto

lemma seq_hoare_d: 
  assumes "C is \<^bold>N" "D is \<^bold>N" "{p}C{q}\<^sub>D" "{q}D{r}\<^sub>D"
  shows "{p}C ;; D{r}\<^sub>D"
proof -
  obtain c\<^sub>1 C\<^sub>2 where C: "C = c\<^sub>1 \<turnstile>\<^sub>n C\<^sub>2"
    by (metis assms(1) ndesign_form)
  obtain d\<^sub>1 D\<^sub>2 where D: "D = d\<^sub>1 \<turnstile>\<^sub>n D\<^sub>2"
    by (metis assms(2) ndesign_form)
  from assms(3-4) show ?thesis
    apply (simp add: C D)
    apply (ndes_simp)
    apply (simp add: ndesign_refinement)
    apply (rel_blast)
    done
qed

end