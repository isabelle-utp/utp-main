section {* UTP designs data refinement example *}

theory utp_designs_ref_ex
imports "../theories/utp_designs"
begin

text {* This theory is currently incomplete *}

alphabet my_state =
  s :: "int set"
  q :: "int list"

abbreviation Inv_A :: "my_state upred" where
"Inv_A \<equiv> finite\<^sub>u(&s)"

definition Init_A :: "my_state hrel_des" where
[upred_defs]: "Init_A = (true \<turnstile>\<^sub>n ($s\<acute> =\<^sub>u {}\<^sub>u))"

abbreviation "pre_Add_A(x) \<equiv> Inv_A \<and> \<guillemotleft>x\<guillemotright> \<notin>\<^sub>u &s"

definition Add_A :: "int \<Rightarrow> my_state hrel_des" where
[upred_defs]: "Add_A(x) = (pre_Add_A(x) \<turnstile>\<^sub>n ($s\<acute> =\<^sub>u $s \<union>\<^sub>u {\<guillemotleft>x\<guillemotright>}\<^sub>u))"

abbreviation "pre_Del_A(x) \<equiv> Inv_A \<and> \<guillemotleft>x\<guillemotright> \<in>\<^sub>u &s"

definition Del_A :: "int \<Rightarrow> my_state hrel_des" where
[upred_defs]: "Del_A(x) = (pre_Del_A(x) \<turnstile>\<^sub>n ($s\<acute> =\<^sub>u $s - {\<guillemotleft>x\<guillemotright>}\<^sub>u))"

abbreviation Inv_C :: "my_state upred" where
"Inv_C \<equiv> distinct\<^sub>u(&q)"

definition Init_C :: "my_state hrel_des" where
[upred_defs]: "Init_C = (true \<turnstile>\<^sub>n ($q\<acute> =\<^sub>u \<langle>\<rangle>))"

abbreviation "pre_Add_C(x) \<equiv> Inv_C \<and> \<guillemotleft>x\<guillemotright> \<notin>\<^sub>u ran\<^sub>u(&q)"

definition Add_C :: "int \<Rightarrow> my_state hrel_des" where
[upred_defs]: "Add_C(x) = (pre_Add_C(x) \<turnstile>\<^sub>n ($q\<acute> =\<^sub>u $q ^\<^sub>u \<langle>\<guillemotleft>x\<guillemotright>\<rangle>))"

abbreviation "pre_Del_C(x) \<equiv> Inv_C \<and> \<guillemotleft>x\<guillemotright> \<in>\<^sub>u ran\<^sub>u(&q)"

definition Del_C :: "int \<Rightarrow> my_state hrel_des" where
[upred_defs]: "Del_C(x) = (pre_Del_C(x) \<turnstile>\<^sub>n ($q\<acute> =\<^sub>u $q \<restriction>\<^sub>u (- {\<guillemotleft>x\<guillemotright>}\<^sub>u)))"

definition Abs :: "my_state upred" where
[upred_defs]: "Abs = (distinct\<^sub>u(&q) \<and> &s =\<^sub>u ran\<^sub>u(&q))"

lemma Del_Del: "(Del_A(x) ;; Del_A(x)) = \<bottom>\<^sub>D"
  by (rel_auto)

lemma Add_commute:
  assumes "x \<noteq> y"
  shows "(Add_A(x) ;; Add_A(y)) = (Add_A(y) ;; Add_A(x))"
  using assms by (rel_auto)

end