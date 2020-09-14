section \<open> Idle and Active Relations \<close>

theory tcircus_idle
  imports tcircus_rel
begin

definition filter_idle :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction" ("idle'(_')") where
[upred_defs]: "filter_idle P = U(R1(P \<and> &tt \<in> tocks UNIV))"

definition filter_time :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction" ("time'(_')") where
[upred_defs]: "filter_time P = U(R1(\<exists> $st\<acute> \<bullet> \<exists> $pat\<acute> \<bullet> \<exists> $ref\<acute> \<bullet> P\<lbrakk>idleprefix(&tt)/&tt\<rbrakk>))"

definition filter_active :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction" ("active'(_')") where 
[upred_defs]: "filter_active(P) = U(R1(\<exists> t e t'. P \<and> \<guillemotleft>t\<guillemotright> \<in> tocks UNIV \<and> &tt = \<guillemotleft>t @ (Evt e # t')\<guillemotright>))"

utp_const filter_idle filter_active

lemma idle_TRR [closure]: assumes "P is TRR" shows "idle(P) is TRR"
proof -
  have "TRR(idle(TRR(P))) = idle(TRR(P))" by rel_blast
  thus "idle(P) is TRR" by (metis Healthy_def assms)
qed

lemma active_TRR [closure]: assumes "P is TRR" shows "active(P) is TRR"
proof -
  have "TRR(active(TRR(P))) = active(TRR(P))" by rel_blast
  thus "active(P) is TRR" by (metis Healthy_def assms)
qed

lemma time_TRR [closure]: assumes "P is TRR" shows "time(P) is TRR"
proof -
  have "TRR(time(TRR(P))) = time(TRR(P))" by rel_blast
  thus "time(P) is TRR" by (metis Healthy_def assms)
qed

lemma 
  assumes "P is TRR"
  shows "(P \<and> time(P)) is TIP"
  apply (simp add: Healthy_def)
  apply (trr_auto cls: assms)
  oops

lemma active_disj [rpred]: "active(P \<or> Q) = (active(P) \<or> active(Q))"
  by rel_auto

lemma idle_conj [rpred]: "idle(P \<and> Q) = (idle(P) \<and> idle(Q))"
  by (rel_auto)

lemma idle_disj [rpred]: "idle(P \<or> Q) = (idle(P) \<or> idle(Q))"
  by (rel_auto)

lemma idle_idem [rpred]: "idle(idle(P)) = idle(P)"
  by rel_auto

lemma idle_true': "idle(true) = U(R1(&tt \<in> tocks UNIV))"
  by rel_auto

lemma active_idem [rpred]: "active(active(P)) = active(P)"
  by rel_auto

lemma TRR_idle_or_active [rpred]:
  assumes "P is TRR"
  shows "(idle(P) \<or> active(P)) = P"
  by (trr_auto cls: assms)
     (metis hd_Cons_tl hd_activesuffix idle_active_decomp idleprefix_tocks rangeE tocks_Nil tocks_append)
 
lemma refine_eval_dest: "P \<sqsubseteq> Q \<Longrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>e s \<Longrightarrow> \<lbrakk>P\<rbrakk>\<^sub>e s"
  by (rel_auto)

lemma Healthy_after: "\<lbrakk> \<And> i. P i is H \<rbrakk> \<Longrightarrow> H \<circ> P = P"
  by (metis (mono_tags, lifting) Healthy_if fun.map_cong fun.map_id0 id_apply image_iff)
    
lemma idle_skip [rpred]: "idle(II\<^sub>t) = II\<^sub>t"
  by (rel_auto)

lemma idle_false [rpred]: "idle(false) = false"
  by (rel_auto)

lemma time_disj [rpred]: "time(P \<or> Q) = (time(P) \<or> time(Q))"
  by (rel_auto)

lemma TIP_has_time [rpred]:
  assumes "P is TRR" "P is TIP"
  shows "(P \<and> time(P)) = P"
  apply (trr_auto cls: assms)
  apply (drule refine_eval_dest[OF TIP_prop[OF assms(1) assms(2)]])
  apply (rel_blast)
  done

lemma TIP_time_active [rpred]:
  assumes "P is TRR" "P is TIP"
  shows "(active(P) \<and> time(P)) = active(P)"
  apply (trr_auto cls: assms)
  apply (drule refine_eval_dest[OF TIP_prop[OF assms(1) assms(2)]])
  apply (rel_blast)
  done

lemma TRF_time [closure]:
  "P is TRR \<Longrightarrow> time(P) is TRF"
  by (rule TRF_intro, simp add: closure unrest, simp_all add: filter_time_def unrest)

end