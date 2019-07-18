theory formal_assurance
  imports refinement
begin

text \<open> Cyber-Physical State Space: controlled, monitored, and internal variables \<close>

alphabet ('c, 'm, 's) cpst =
  ctrl  :: 'c
  mon   :: 'm
  state :: 's

type_synonym ('c, 'm, 's) cpsprog = "('c, 'm, 's) cpst hrel"

text \<open> A cyber-physical system model consists of a state invariant over the controlled variables,
  and a body over the entire state \<close>

type_synonym ('c, 'm, 's) cps = "('c, 'm, 's) cpst machine"
  
locale valid_cps = machine M for M :: "('c, 'm, 's) cps" (structure) +
  \<comment> \<open> The invariant does not refer to monitored variables \<close>
  assumes invs_nmon: "mon \<sharp> Invs"
  \<comment> \<open> The actions do not change the monitored variables \<close>
  and body_mon_unch: "($mon\<acute> =\<^sub>u $mon) \<sqsubseteq> Body"
begin

  text \<open> Any predicate on monitored variables is invariant \<close>

  lemma env_assm_inv:
    assumes "ctrl \<sharp> A" "state \<sharp> A"
    shows "\<lbrace>A\<rbrace>Body\<lbrace>A\<rbrace>\<^sub>u"
  proof -
    from assms have "\<lbrace>A\<rbrace>($mon\<acute> =\<^sub>u $mon \<and> Body)\<lbrace>A\<rbrace>\<^sub>u"
      by (rel_blast)
    thus ?thesis
      by (simp add: body_mon_unch utp_pred_laws.inf.absorb2)
  qed

  lemma env_assm_inv':
    assumes "ctrl \<sharp> A" "state \<sharp> A"
    shows "`A \<Rightarrow> Body wlp A`"
    using assms(1) assms(2) env_assm_inv wlp_hoare_link by auto

  lemma env_assm_inv'':
    "`(\<exists> &ctrl \<bullet> \<exists> &state \<bullet> A) \<Rightarrow> Body wlp (\<exists> &ctrl \<bullet> \<exists> &state \<bullet> A)`"
    by (rule env_assm_inv', simp_all add: unrest)
end

text \<open> Demonstration that the unchanging monitored variable property can be demonstrated using wp. \<close>

lemma mon_unch_prop: 
  fixes P :: "('c, 'm, 's) cpsprog"
  shows "($mon\<acute> =\<^sub>u $mon) \<sqsubseteq> P \<longleftrightarrow> (\<forall> r. `P wp r \<Rightarrow> (\<exists> &ctrl \<bullet> \<exists> &state \<bullet> r)`)"
proof -
  have "($mon\<acute> =\<^sub>u $mon) \<sqsubseteq> P \<longleftrightarrow> ctrl := * ;; state := * \<sqsubseteq> P"
    by rel_auto
  also have "... = (\<forall>r. `P wp r \<Rightarrow> (\<^bold>\<exists> v \<bullet> (\<^bold>\<exists> v \<bullet> r\<lbrakk>\<guillemotleft>v\<guillemotright>/&state\<rbrakk>)\<lbrakk>\<guillemotleft>v\<guillemotright>/&ctrl\<rbrakk>)`)"
    by (subst wp_refine_iff[THEN sym], simp add: wp)
  also have "... = (\<forall> r. `P wp r \<Rightarrow> (\<exists> &ctrl \<bullet> \<exists> &state \<bullet> r)`)"
    by (rel_simp')
  finally show ?thesis .
qed


type_synonym ('s\<^sub>1, 's\<^sub>2) cinv = "('s\<^sub>1, 's\<^sub>2) urel"

text \<open> Formal Assurance Case Signature \<close>

datatype reqtype = nxt | glob | fin

record ('c, 'm, 's) reqbody = 
  pre   :: "('c, 'm, 's) cpst upred"
  post  :: "('c, 'm, 's) cpst upred"

type_synonym ('c, 'm, 's) req = "reqtype \<times> ('c, 'm, 's) reqbody"

text \<open> The body of the CPS satisfies the safety or liveness requirement \<close>

fun req_sat :: "_ \<times> ('c, 'm, 's) cps \<Rightarrow> ('c, 'm, 's) req \<Rightarrow> bool" ("_ \<TTurnstile> _" [100, 101] 100) where
"(A, M) \<TTurnstile> (nxt, rb)  = `(A \<and> invs M \<and> pre rb) \<Rightarrow> (body M) wlp (post rb)`" |
"(A, M) \<TTurnstile> (glob, rb) = (\<exists> I. \<lbrace>I\<rbrace>body M\<lbrace>I\<rbrace>\<^sub>u \<and> `A \<and> pre rb \<and> invs M \<Rightarrow> I` \<and> `A \<and> I \<and> invs M \<Rightarrow> post rb`)" |
"(A, M) \<TTurnstile> (fin, rb) = `(A \<and> invs M \<and> pre rb) \<Rightarrow> (body M)\<^sup>\<star> wp (post rb)`"

lemma global_satisfaction:
  assumes "valid_cps M" "(A, M) \<TTurnstile> (glob, rb)" "ctrl \<sharp> A" "state \<sharp> A"
  shows "\<lbrace>A \<and> pre rb \<and> invs M\<rbrace>(body M)\<^sup>\<star>\<lbrace>post rb\<rbrace>\<^sub>u"
proof -
  obtain I where I:"\<lbrace>I\<rbrace>body M\<lbrace>I\<rbrace>\<^sub>u" "`A \<and> pre rb \<and> invs M \<Rightarrow> I`" "`A \<and> I \<and> invs M \<Rightarrow> post rb`"
    by (meson assms req_sat.simps(2))
  from I(3) have post: "`I \<Rightarrow> A \<and> invs M \<Rightarrow> post rb`"
    by (rel_auto)
 
  have "\<lbrace>A \<and> pre rb \<and> invs M\<rbrace>(body M)\<^sup>\<star>\<lbrace>A \<and> invs M \<Rightarrow> post rb\<rbrace>\<^sub>u"
    using I(1) I(2) hoare_r_conseq iter_hoare_r post by blast
  moreover have "\<lbrace>invs M\<rbrace>(body M)\<^sup>\<star>\<lbrace>invs M\<rbrace>\<^sub>u"
    using assms(1) iter_hoare_r machine.body_invs' valid_cps.axioms(1) by blast
  moreover have "\<lbrace>A\<rbrace>(body M)\<^sup>\<star>\<lbrace>A\<rbrace>\<^sub>u"
    by (simp add: assms(1) assms(3) assms(4) iter_hoare_r valid_cps.env_assm_inv)
  ultimately show ?thesis
    by (simp add: wlp_hoare_link, rel_auto)
qed

text \<open> A formal assurance case consists of assumptions, guarantees, and a model \<close>

record ('c, 'm, 's) fac =
  assm  :: "('c, 'm, 's) cpst upred"
  guar  :: "('c, 'm, 's) req set"

record ('c, 'm, 's) fmac = "('c, 'm, 's) fac" +
  model :: "('c, 'm, 's) cps"

definition fac_sem where "fac_sem AC = (mon := * ;; ?[assm AC] ;; body (model AC))\<^sup>\<star>"

locale valid_fac =
  fixes AC :: "('c, 'm, 's) fmac"
  assumes valid_cps: "valid_cps (model AC)"
  \<comment> \<open> The assumption refers only to monitored variables \<close>
  and "ctrl \<sharp> assm AC" "state \<sharp> assm AC"
  \<comment> \<open> All requirements are satisfied by the model \<close>
  and reqs_satisfied: "\<And> R. R \<in> guar AC \<Longrightarrow> (assm AC, model AC) \<TTurnstile> R"
begin

  lemma assm_invar_body: "\<lbrace>assm AC\<rbrace>body (model AC)\<lbrace>assm AC\<rbrace>\<^sub>u"
    using valid_cps.env_assm_inv valid_fac_axioms valid_fac_def by blast

end

text \<open> Lift safety requirements using a functional retrieve relation\<close>

definition lift_sreqs :: 
  "('c\<^sub>1, 'm\<^sub>1, 's\<^sub>1) fmac \<Rightarrow> 
   (('c\<^sub>2, 'm\<^sub>2, 's\<^sub>2) cpst \<Rightarrow> ('c\<^sub>1, 'm\<^sub>1, 's\<^sub>1) cpst) \<Rightarrow> 
   reqtype \<leftrightarrow> ('c\<^sub>2, 'm\<^sub>2, 's\<^sub>2) reqbody" where
"lift_sreqs AC \<sigma> \<equiv> {(t, \<lparr> pre = \<sigma> \<dagger> (assm AC \<and> pre b), post = \<sigma> \<dagger> post b \<rparr>) | t b. t \<in> {nxt, glob} \<and> (t, b) \<in> guar AC}"

text \<open> Extend an existing FAC with a new model and additional requirements; we assume that a 
  data refinement will be exhibited between the abstract and concrete models \<close>

definition fac_extend :: 
  "('c\<^sub>1, 'm\<^sub>1, 's\<^sub>1) fmac \<Rightarrow> (('c\<^sub>2, 'm\<^sub>2, 's\<^sub>2) cpst, ('c\<^sub>1, 'm\<^sub>1, 's\<^sub>1) cpst) psubst \<Rightarrow>
   ('c\<^sub>2, 'm\<^sub>2, 's\<^sub>2) fmac \<Rightarrow> ('c\<^sub>2, 'm\<^sub>2, 's\<^sub>2) fmac" where
  "fac_extend AC\<^sub>1 \<sigma> AC\<^sub>2 = \<lparr> assm = assm AC\<^sub>2, guar = lift_sreqs AC\<^sub>1 \<sigma> \<union> guar AC\<^sub>2, model = model AC\<^sub>2 \<rparr>"

text \<open> Theorem to prove the validity of the above; requires a data refinement argument \<close>

lemma fac_extend_intro:
  assumes 
    \<comment> \<open> Valid models \<close>
    "valid_cps (model AC\<^sub>1)" "valid_cps (model AC\<^sub>2)"
    \<comment> \<open> Original assurance case is valid \<close>
    "valid_fac AC\<^sub>1"
    \<comment> \<open> Weaken the assumption \<close>
    "`(\<sigma> \<dagger> assm AC\<^sub>1) \<Rightarrow> assm AC\<^sub>2`"
    \<comment> \<open> Demonstrate a backward functional refinement \<close>
    "func_refinement (func_refine (model AC\<^sub>1) (model AC\<^sub>2) \<sigma>) \<sigma>"
    \<comment> \<open> Prove all additional requirements \<close>
    "\<And> R. R \<in> guar AC\<^sub>2 \<Longrightarrow> ((assm AC\<^sub>2, model AC\<^sub>2) \<TTurnstile> R)"
    \<comment> \<open> New assumption refers only to monitored variables \<close>    
    "ctrl \<sharp> assm AC\<^sub>2" "state \<sharp> assm AC\<^sub>2"
  shows "valid_fac (fac_extend AC\<^sub>1 \<sigma> AC\<^sub>2)"
proof (rule valid_fac.intro)
  interpret func_refinement "func_refine (model AC\<^sub>1) (model AC\<^sub>2) \<sigma>" \<sigma>
    by (simp add: assms)
  show "valid_cps (model (fac_extend AC\<^sub>1 \<sigma> AC\<^sub>2))"
    by (simp add: fac_extend_def assms)
  show "\<And>R. R \<in> guar (fac_extend AC\<^sub>1 \<sigma> AC\<^sub>2) \<Longrightarrow> (assm (fac_extend AC\<^sub>1 \<sigma> AC\<^sub>2), model (fac_extend AC\<^sub>1 \<sigma> AC\<^sub>2)) \<TTurnstile> R"
  proof (clarsimp simp add: fac_extend_def, erule disjE)
    fix rt rb
    assume "(rt, rb) \<in> guar AC\<^sub>2"
    thus "(assm AC\<^sub>2, model AC\<^sub>2) \<TTurnstile> (rt, rb)"
      by (simp add: assms)
  next
    fix rt rb
    assume a: "(rt, rb) \<in> lift_sreqs AC\<^sub>1 \<sigma>"
    hence rt: "rt = nxt \<or> rt = glob"
      by (auto simp add: lift_sreqs_def)
    from a obtain Pre Post where rb: "(rt, \<lparr> pre = Pre, post = Post \<rparr>) \<in> guar AC\<^sub>1" "rb = \<lparr> pre = \<sigma> \<dagger> (assm AC\<^sub>1 \<and> Pre), post = \<sigma> \<dagger> Post \<rparr>"
      by (auto simp add: lift_sreqs_def, (metis (full_types) old.unit.exhaust reqbody.surjective)+)
    have osat: "(assm AC\<^sub>1, model AC\<^sub>1) \<TTurnstile> (rt, \<lparr> pre = Pre, post = Post \<rparr>)"
      by (simp add: assms(3) rb(1) valid_fac.reqs_satisfied)
    show "(assm AC\<^sub>2, model AC\<^sub>2) \<TTurnstile> (rt, rb)"
    proof (cases "rt = nxt")
      case True
      have "`assm AC\<^sub>1 \<Rightarrow> Invs\<^bsub>model AC\<^sub>1\<^esub> \<and> Pre \<Rightarrow> Body\<^bsub>model AC\<^sub>1\<^esub> wlp Post`"
        by (metis True assms(3) hoare_gcmd rb(1) req_sat.simps(1) reqbody.select_convs(1) reqbody.select_convs(2) valid_fac.reqs_satisfied wlp_gcmd wlp_hoare_link)
      hence "`Invs\<^bsub>model AC\<^sub>1\<^esub> \<and> (Pre \<and> assm AC\<^sub>1) \<Rightarrow> Body\<^bsub>model AC\<^sub>1\<^esub> wlp Post`"
        by (rel_auto)
      hence "`Invs\<^bsub>model AC\<^sub>2\<^esub> \<and> (\<sigma> \<dagger> (Pre \<and> assm AC\<^sub>1)) \<Rightarrow> Body\<^bsub>model AC\<^sub>2\<^esub> wlp (\<sigma> \<dagger> Post)`"
        using refinement_preserves_safety_wlp_func
        by (simp add: func_refine_def)
      with rb True show ?thesis
        by (auto, metis hoare_r_weaken_pre(2) utp_pred_laws.inf.commute wlp_hoare_link)
    next
      case False
      with rt have glob:"rt = glob"
        by auto
      with osat obtain I where I:"\<lbrace>I\<rbrace> Body\<^bsub>model AC\<^sub>1\<^esub> \<lbrace>I\<rbrace>\<^sub>u" "`assm AC\<^sub>1 \<and> Pre \<and> Invs\<^bsub>model AC\<^sub>1\<^esub> \<Rightarrow> I`" "`assm AC\<^sub>1 \<and> I \<and> Invs\<^bsub>model AC\<^sub>1\<^esub> \<Rightarrow> Post`"
        by (auto)
      hence 1:"\<lbrace>Invs\<^bsub>model AC\<^sub>2\<^esub> \<and> (\<sigma> \<dagger> (I \<and> assm AC\<^sub>1))\<rbrace>Body\<^bsub>model AC\<^sub>2\<^esub>\<lbrace>(\<sigma> \<dagger> I)\<rbrace>\<^sub>u"
        by (metis func_refine_def hoare_r_weaken_pre(1) refinement.refinement.select_convs(1) refinement.refinement.select_convs(2) refinement_preserves_safety_func utp_pred_laws.inf_commute)
      have 2: "\<lbrace>Invs\<^bsub>model AC\<^sub>2\<^esub> \<and> (\<sigma> \<dagger> assm AC\<^sub>1)\<rbrace>Body\<^bsub>model AC\<^sub>2\<^esub>\<lbrace>\<sigma> \<dagger> assm AC\<^sub>1\<rbrace>\<^sub>u"
      proof -
        have "\<lbrace>Invs\<^bsub>model AC\<^sub>1\<^esub> \<and> assm AC\<^sub>1\<rbrace>Body\<^bsub>model AC\<^sub>1\<^esub>\<lbrace>assm AC\<^sub>1\<rbrace>\<^sub>u"
          by (simp add: assms(3) hoare_r_weaken_pre(2) valid_fac.assm_invar_body) 
        thus ?thesis
          using refinement_preserves_safety_func by (simp add: func_refine_def)
      qed
      have 3: "\<lbrace>Invs\<^bsub>model AC\<^sub>2\<^esub>\<rbrace>Body\<^bsub>model AC\<^sub>2\<^esub>\<lbrace>Invs\<^bsub>model AC\<^sub>2\<^esub>\<rbrace>\<^sub>u"
        by (simp add: assms(2) machine.body_invs' valid_cps.axioms(1))
      from 1 2 3 have 4:"\<lbrace>Invs\<^bsub>model AC\<^sub>2\<^esub> \<and> (\<sigma> \<dagger> (I \<and> assm AC\<^sub>1))\<rbrace>Body\<^bsub>model AC\<^sub>2\<^esub>\<lbrace>Invs\<^bsub>model AC\<^sub>2\<^esub> \<and> (\<sigma> \<dagger> (I \<and> assm AC\<^sub>1))\<rbrace>\<^sub>u"
        by (smt hoare_r_conj hoare_r_weaken_pre(2) subst_conj utp_pred_laws.conj_assoc utp_pred_laws.inf_commute)
      have 5: "`assm AC\<^sub>2 \<and> pre rb \<and> Invs\<^bsub>model AC\<^sub>2\<^esub> \<Rightarrow> Invs\<^bsub>model AC\<^sub>2\<^esub> \<and> \<sigma> \<dagger> (I \<and> assm AC\<^sub>1)`"
      proof -
        from I(2) have "`\<sigma> \<dagger> (assm AC\<^sub>1 \<and> Pre \<and> Invs\<^bsub>model AC\<^sub>1\<^esub>) \<Rightarrow> \<sigma> \<dagger> I`"
          by (rel_auto)
        moreover have "`Invs\<^bsub>model AC\<^sub>2\<^esub> \<Rightarrow> \<sigma> \<dagger> Invs\<^bsub>model AC\<^sub>1\<^esub>`"
          by (metis func_invs func_refine_def refinement.refinement.select_convs(1) refinement.refinement.select_convs(2))
        ultimately show ?thesis
          by (simp add: rb usubst, rel_simp)
      qed
      from I(3) have 6: "`assm AC\<^sub>2 \<and> (Invs\<^bsub>model AC\<^sub>2\<^esub> \<and> \<sigma> \<dagger> (I \<and> assm AC\<^sub>1)) \<and> Invs\<^bsub>model AC\<^sub>2\<^esub> \<Rightarrow> post rb`"
      proof -
        from I(3) have "`\<sigma> \<dagger> (assm AC\<^sub>1 \<and> I \<and> Invs\<^bsub>model AC\<^sub>1\<^esub>) \<Rightarrow> \<sigma> \<dagger> Post`"
          by (rel_auto)
        moreover have "`Invs\<^bsub>model AC\<^sub>2\<^esub> \<Rightarrow> \<sigma> \<dagger> Invs\<^bsub>model AC\<^sub>1\<^esub>`"
          by (metis func_invs func_refine_def refinement.refinement.select_convs(1) refinement.refinement.select_convs(2))
        ultimately show ?thesis
          by (simp add: rb usubst, rel_auto)
      qed
      from glob I(2-3) 4 5 6 show ?thesis
        by (auto)
    qed
  qed
  show "ctrl \<sharp> assm (fac_extend AC\<^sub>1 \<sigma> AC\<^sub>2)"
    by (simp add: fac_extend_def assms)
  show "state \<sharp> assm (fac_extend AC\<^sub>1 \<sigma> AC\<^sub>2)"
    by (simp add: fac_extend_def assms)
qed

end