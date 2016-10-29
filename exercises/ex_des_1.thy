theory ex_des_1
imports "../utp/utp_designs"
begin

record my_state =
  st_s :: "int set"
  st_q :: "int list"

consts s :: "int set \<Longrightarrow> '\<alpha>"
consts q :: "int list \<Longrightarrow> '\<alpha>"

definition s_mystate :: "int set \<Longrightarrow> my_state" where
[upred_defs]: "s_mystate = VAR st_s"
definition q_mystate :: "int list \<Longrightarrow> my_state" where
[upred_defs]: "q_mystate = VAR st_q"

adhoc_overloading
  s s_mystate and
  q q_mystate

lemma uvar_s [simp]: "vwb_lens s"
  by (unfold_locales, auto simp add: s_mystate_def)

lemma uvar_q [simp]: "vwb_lens q"
  by (unfold_locales, auto simp add: q_mystate_def)

lemma my_state_indeps [simp]: "s \<bowtie> q" "q \<bowtie> s"
  by (simp_all add: lens_indep_def s_mystate_def q_mystate_def)

abbreviation Inv_A :: "my_state upred" where
"Inv_A \<equiv> finite\<^sub>u(&s)"

definition Init_A :: "my_state hrelation_d" where
"Init_A = (true \<turnstile>\<^sub>n ($s\<acute> =\<^sub>u {}\<^sub>u))"

abbreviation "pre_Add_A(x) \<equiv> Inv_A \<and> \<guillemotleft>x\<guillemotright> \<notin>\<^sub>u &s"

definition Add_A :: "int \<Rightarrow> my_state hrelation_d" where
"Add_A(x) = (pre_Add_A(x) \<turnstile>\<^sub>n ($s\<acute> =\<^sub>u $s \<union>\<^sub>u {\<guillemotleft>x\<guillemotright>}\<^sub>u))"

abbreviation "pre_Del_A(x) \<equiv> Inv_A \<and> \<guillemotleft>x\<guillemotright> \<in>\<^sub>u &s"

definition Del_A :: "int \<Rightarrow> my_state hrelation_d" where
"Del_A(x) = (pre_Del_A(x) \<turnstile>\<^sub>n ($s\<acute> =\<^sub>u $s - {\<guillemotleft>x\<guillemotright>}\<^sub>u))"

abbreviation Inv_C :: "my_state upred" where
"Inv_C \<equiv> distinct\<^sub>u(&q)"

definition Init_C :: "my_state hrelation_d" where
"Init_C = (true \<turnstile>\<^sub>n ($q\<acute> =\<^sub>u \<langle>\<rangle>))"

abbreviation "pre_Add_C(x) \<equiv> Inv_C \<and> \<guillemotleft>x\<guillemotright> \<notin>\<^sub>u ran\<^sub>u(&q)"

definition Add_C :: "int \<Rightarrow> my_state hrelation_d" where
"Add_C(x) = (pre_Add_C(x) \<turnstile>\<^sub>n ($q\<acute> =\<^sub>u $q ^\<^sub>u \<langle>\<guillemotleft>x\<guillemotright>\<rangle>))"

abbreviation "pre_Del_C(x) \<equiv> Inv_C \<and> \<guillemotleft>x\<guillemotright> \<in>\<^sub>u ran\<^sub>u(&q)"

definition Del_C :: "int \<Rightarrow> my_state hrelation_d" where
"Del_C(x) = (pre_Del_C(x) \<turnstile>\<^sub>n ($q\<acute> =\<^sub>u $q \<restriction>\<^sub>u (- {\<guillemotleft>x\<guillemotright>}\<^sub>u)))"

definition Abs :: "my_state upred" where
"Abs = (distinct\<^sub>u(&q) \<and> &s =\<^sub>u ran\<^sub>u(&q))"

lemma Del_Del: "(Del_A(x) ;; Del_A(x)) = \<bottom>\<^sub>D"
proof -
  have "($s\<acute> =\<^sub>u $s - {\<guillemotleft>x\<guillemotright>}\<^sub>u) wp (finite\<^sub>u(s) \<and> \<guillemotleft>x\<guillemotright> \<in>\<^sub>u s) = false"
    by (rel_tac, meson my_state.select_convs(1))
  thus ?thesis
    by (simp add: Del_A_def ndesign_composition_wp ndesign_false_pre)
qed

lemma "x \<noteq> y \<Longrightarrow> ($s\<acute> =\<^sub>u $s \<union>\<^sub>u {\<guillemotleft>x\<guillemotright>}\<^sub>u) wp (finite\<^sub>u(s) \<and> \<guillemotleft>y\<guillemotright> \<notin>\<^sub>u s) = (finite\<^sub>u(s) \<and> \<guillemotleft>y\<guillemotright> \<notin>\<^sub>u s)"
  by (rel_tac, (meson my_state.select_convs(1))+)

lemma Add_commute: 
  assumes "x \<noteq> y"
  shows "(Add_A(x) ;; Add_A(y)) = (Add_A(y) ;; Add_A(x))"
proof -
  from assms have 1[simplified]: "($s\<acute> =\<^sub>u $s \<union>\<^sub>u {\<guillemotleft>x\<guillemotright>}\<^sub>u) wp (finite\<^sub>u(s) \<and> \<guillemotleft>y\<guillemotright> \<notin>\<^sub>u s) = (finite\<^sub>u(s) \<and> \<guillemotleft>y\<guillemotright> \<notin>\<^sub>u s)"
    by (rel_tac, (meson my_state.select_convs(1))+)
  from assms have 2[simplified]: "($s\<acute> =\<^sub>u $s \<union>\<^sub>u {\<guillemotleft>y\<guillemotright>}\<^sub>u) wp (finite\<^sub>u(s) \<and> \<guillemotleft>x\<guillemotright> \<notin>\<^sub>u s) = (finite\<^sub>u(s) \<and> \<guillemotleft>x\<guillemotright> \<notin>\<^sub>u s)"
    by (rel_tac, (meson my_state.select_convs(1))+)
  from assms have 3: "($s\<acute> =\<^sub>u $s \<union>\<^sub>u {\<guillemotleft>y\<guillemotright>}\<^sub>u ;; $s\<acute> =\<^sub>u $s \<union>\<^sub>u {\<guillemotleft>x\<guillemotright>}\<^sub>u) = ($s\<acute> =\<^sub>u $s \<union>\<^sub>u {\<guillemotleft>x\<guillemotright>}\<^sub>u ;; $s\<acute> =\<^sub>u $s \<union>\<^sub>u {\<guillemotleft>y\<guillemotright>}\<^sub>u)"
    by (rel_tac, (metis insert_commute my_state.select_convs(1))+)
  show ?thesis
    by (simp add: Add_A_def ndesign_composition_wp 1 2 3 utp_pred.inf.commute)
qed
 

lemma Add_Del:
  "((Inv_A \<and> \<guillemotleft>x\<guillemotright> \<notin>\<^sub>u &s) \<turnstile>\<^sub>n ($s\<acute> =\<^sub>u $s)) \<sqsubseteq> (Add_A(x) ;; Del_A(x))" (is "?P \<sqsubseteq> ?Q")
proof -
  have 1:"($s\<acute> =\<^sub>u $s \<union>\<^sub>u {\<guillemotleft>x\<guillemotright>}\<^sub>u) wp (finite\<^sub>u(s) \<and> \<guillemotleft>x\<guillemotright> \<in>\<^sub>u s) = finite\<^sub>u(s)"
    by (rel_tac, meson my_state.select_convs(1))
  have 2:"((finite\<^sub>u(s) \<and> \<guillemotleft>x\<guillemotright> \<notin>\<^sub>u s) \<and> finite\<^sub>u(s)) = (finite\<^sub>u(s) \<and> \<guillemotleft>x\<guillemotright> \<notin>\<^sub>u s)"
    by (pred_tac)
  from 1 2 have 3:"?Q = (finite\<^sub>u(s) \<and> \<guillemotleft>x\<guillemotright> \<notin>\<^sub>u s) \<turnstile>\<^sub>n ($s\<acute> =\<^sub>u $s \<union>\<^sub>u {\<guillemotleft>x\<guillemotright>}\<^sub>u ;; $s\<acute> =\<^sub>u $s - {\<guillemotleft>x\<guillemotright>}\<^sub>u)"
    by (simp add: Add_A_def Del_A_def ndesign_composition_wp)
  show "?P \<sqsubseteq> ?Q"
    apply (simp add: 3)
    apply (rule ndesign_refine_intro)
    apply (simp_all add:alpha)
    apply (rel_tac)
  done
qed

lemma r1: "`\<forall> $\<Sigma>\<^sub>D:s\<acute> \<bullet> ($ok \<and> Init_A) \<Rightarrow> (\<exists> $\<Sigma>\<^sub>D:q\<acute> \<bullet> Init_C \<and> \<lceil>\<lceil>Abs\<rceil>\<^sub>>\<rceil>\<^sub>D)`"
  apply (simp add: Init_A_def Init_C_def Abs_def alpha)
  apply (rel_tac)
done

lemma r2: "`\<forall> s \<bullet> \<forall> q \<bullet> pre_Add_A(x) \<and> Abs \<Rightarrow> pre_Add_C(x)`"
  apply (simp add: Abs_def)
  apply (rel_tac)
done

lemma r3: "`($ok \<and> \<lceil>pre_Add_C(x) \<and> Abs\<rceil>\<^sub>D\<^sub>< \<and> Add_C(x)) \<Rightarrow> (\<exists> $\<Sigma>\<^sub>D:s\<acute> \<bullet> (Add_A(x) \<and> \<lceil>Abs\<rceil>\<^sub>D\<^sub>>))`"
  by (simp add: Add_C_def Add_A_def Abs_def, rel_tac)

lemma r4: "`\<forall> s \<bullet> \<forall> q \<bullet> pre_Del_A(x) \<and> Abs \<Rightarrow> pre_Del_C(x)`"
  apply (simp add: Abs_def)
  apply (rel_tac)
done

lemma r5: "`($ok \<and> \<lceil>pre_Del_C(x) \<and> Abs\<rceil>\<^sub>D\<^sub>< \<and> Del_C(x)) \<Rightarrow> (\<exists> $\<Sigma>\<^sub>D:s\<acute> \<bullet> (Del_A(x) \<and> \<lceil>Abs\<rceil>\<^sub>D\<^sub>>))`"
  apply (simp add: Del_C_def Del_A_def Abs_def alpha) 
  apply (simp add: upred_defs urel_defs)
  apply (transfer)
  apply (simp add: lens_comp_def)
  apply (clarsimp)
  apply (safe)
oops  

end