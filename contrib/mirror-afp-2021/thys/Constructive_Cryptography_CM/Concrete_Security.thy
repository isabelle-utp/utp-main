theory Concrete_Security 
imports 
  Observe_Failure
  Construction_Utility
begin

section \<open>Concrete security definition\<close>

locale constructive_security_aux_obsf =
  fixes real_resource :: "('a + 'e, 'b + 'f) resource"
    and ideal_resource :: "('c + 'e, 'd + 'f) resource"
    and sim :: "('a, 'b, 'c, 'd) converter"
    and \<I>_real :: "('a, 'b) \<I>"
    and \<I>_ideal :: "('c, 'd) \<I>"
    and \<I>_common :: "('e, 'f) \<I>"
    and adv :: real
  assumes WT_real [WT_intro]: "\<I>_real \<oplus>\<^sub>\<I> \<I>_common \<turnstile>res real_resource \<surd>"
    and WT_ideal [WT_intro]: "\<I>_ideal \<oplus>\<^sub>\<I> \<I>_common \<turnstile>res ideal_resource \<surd>"
    and WT_sim [WT_intro]: "\<I>_real, \<I>_ideal \<turnstile>\<^sub>C sim \<surd>"
    and pfinite_sim [pfinite_intro]: "pfinite_converter \<I>_real \<I>_ideal sim"
    and adv_nonneg: "0 \<le> adv"

locale constructive_security_sim_obsf =
  fixes real_resource :: "('a + 'e, 'b + 'f) resource"
    and ideal_resource :: "('c + 'e, 'd + 'f) resource"
    and sim :: "('a, 'b, 'c, 'd) converter"
    and \<I>_real :: "('a, 'b) \<I>"
    and \<I>_common :: "('e, 'f) \<I>"
    and \<A> :: "('a + 'e, 'b + 'f) distinguisher_obsf"
    and adv :: real
  assumes adv: "\<lbrakk> exception_\<I> (\<I>_real \<oplus>\<^sub>\<I> \<I>_common) \<turnstile>g \<A> \<surd> \<rbrakk>
      \<Longrightarrow> advantage \<A> (obsf_resource (sim |\<^sub>= 1\<^sub>C \<rhd> ideal_resource)) (obsf_resource (real_resource)) \<le> adv"

locale constructive_security_obsf = constructive_security_aux_obsf real_resource ideal_resource sim \<I>_real \<I>_ideal \<I>_common adv
  + constructive_security_sim_obsf real_resource ideal_resource sim \<I>_real \<I>_common \<A> adv
  for real_resource :: "('a + 'e, 'b + 'f) resource"
    and ideal_resource :: "('c + 'e, 'd + 'f) resource"
    and sim :: "('a, 'b, 'c, 'd) converter"
    and \<I>_real :: "('a, 'b) \<I>"
    and \<I>_ideal :: "('c, 'd) \<I>"
    and \<I>_common :: "('e, 'f) \<I>"
    and \<A> :: "('a + 'e, 'b + 'f) distinguisher_obsf"
    and adv :: real
begin

lemma constructive_security_aux_obsf: "constructive_security_aux_obsf real_resource ideal_resource sim \<I>_real \<I>_ideal \<I>_common adv" ..
lemma constructive_security_sim_obsf: "constructive_security_sim_obsf real_resource ideal_resource sim \<I>_real \<I>_common \<A> adv" ..

end

context constructive_security_aux_obsf begin

lemma constructive_security_obsf_refl:
  "constructive_security_obsf real_resource ideal_resource sim \<I>_real \<I>_ideal \<I>_common \<A>
    (advantage \<A> (obsf_resource (sim |\<^sub>= 1\<^sub>C \<rhd> ideal_resource)) (obsf_resource (real_resource)))"
  by unfold_locales(simp_all add: advantage_def WT_intro pfinite_intro)

end

lemma constructive_security_obsf_absorb_cong:
  assumes sec: "constructive_security_obsf real_resource ideal_resource sim \<I>_real \<I>_ideal \<I>_common (absorb \<A> cnv) adv"
    and [WT_intro]: "exception_\<I> \<I>, exception_\<I> (\<I>_real \<oplus>\<^sub>\<I> \<I>_common) \<turnstile>\<^sub>C cnv \<surd>" "exception_\<I> \<I>, exception_\<I> (\<I>_real \<oplus>\<^sub>\<I> \<I>_common) \<turnstile>\<^sub>C cnv' \<surd>" "exception_\<I> \<I> \<turnstile>g \<A> \<surd>"
    and cong: "exception_\<I> \<I>, exception_\<I> (\<I>_real \<oplus>\<^sub>\<I> \<I>_common) \<turnstile>\<^sub>C cnv \<sim> cnv'"
  shows "constructive_security_obsf real_resource ideal_resource sim \<I>_real \<I>_ideal \<I>_common (absorb \<A> cnv') adv"
proof -
  interpret constructive_security_obsf real_resource ideal_resource sim \<I>_real \<I>_ideal \<I>_common "absorb \<A> cnv" adv by fact
  show ?thesis
  proof
    have "connect_obsf \<A> (cnv' \<rhd> obsf_resource (sim |\<^sub>= 1\<^sub>C \<rhd> ideal_resource)) = connect_obsf \<A> (cnv \<rhd> obsf_resource (sim |\<^sub>= 1\<^sub>C \<rhd> ideal_resource))"
      "connect_obsf \<A> (cnv' \<rhd> obsf_resource real_resource) = connect_obsf \<A> (cnv \<rhd> obsf_resource real_resource)"
      by(rule connect_eq_resource_cong eq_\<I>_attach_on' WT_intro cong[symmetric] order_refl)+
    then have "advantage (absorb \<A> cnv') (obsf_resource (sim |\<^sub>= 1\<^sub>C \<rhd> ideal_resource)) (obsf_resource real_resource) =
          advantage (absorb \<A> cnv) (obsf_resource (sim |\<^sub>= 1\<^sub>C \<rhd> ideal_resource)) (obsf_resource real_resource)"
      unfolding advantage_def distinguish_attach[symmetric] by simp
    also have "\<dots> \<le> adv" by(rule adv)(rule WT_intro)+
    finally show "advantage (absorb \<A> cnv') (obsf_resource (sim |\<^sub>= 1\<^sub>C \<rhd> ideal_resource)) (obsf_resource real_resource) \<le> adv" .
  qed
qed

lemma constructive_security_obsf_sim_cong:
  assumes sec: "constructive_security_obsf real_resource ideal_resource sim \<I>_real \<I>_ideal \<I>_common \<A> adv"
    and cong: "\<I>_real, \<I>_ideal \<turnstile>\<^sub>C sim \<sim> sim'"
    and pfinite [pfinite_intro]: "pfinite_converter \<I>_real \<I>_ideal sim'" (* This could probably be derived from cong and sec.pfinite_sim *)
  shows "constructive_security_obsf real_resource ideal_resource sim' \<I>_real \<I>_ideal \<I>_common \<A> adv"
proof
  interpret constructive_security_obsf real_resource ideal_resource sim \<I>_real \<I>_ideal \<I>_common \<A> adv by fact
  show "\<I>_real \<oplus>\<^sub>\<I> \<I>_common \<turnstile>res real_resource \<surd>" "\<I>_ideal \<oplus>\<^sub>\<I> \<I>_common \<turnstile>res ideal_resource \<surd>" by(rule WT_intro)+
  from cong show [WT_intro]: "\<I>_real, \<I>_ideal \<turnstile>\<^sub>C sim' \<surd>" by(rule eq_\<I>_converterD_WT1)(rule WT_intro)
  show "pfinite_converter \<I>_real \<I>_ideal sim'" by fact
  show "0 \<le> adv" by(rule adv_nonneg)

  assume WT [WT_intro]: "exception_\<I> (\<I>_real \<oplus>\<^sub>\<I> \<I>_common) \<turnstile>g \<A> \<surd>"
  have "connect_obsf \<A> (obsf_resource (sim' |\<^sub>= 1\<^sub>C \<rhd> ideal_resource)) = connect_obsf \<A> (obsf_resource (sim |\<^sub>= 1\<^sub>C \<rhd> ideal_resource))"
    by(rule connect_eq_resource_cong WT_intro obsf_resource_eq_\<I>_cong eq_\<I>_attach_on' parallel_converter2_eq_\<I>_cong cong[symmetric] eq_\<I>_converter_reflI | simp)+
  with adv[OF WT]
  show "advantage \<A> (obsf_resource (sim' |\<^sub>= 1\<^sub>C \<rhd> ideal_resource)) (obsf_resource real_resource) \<le> adv"
    unfolding advantage_def by simp
qed

lemma constructive_security_obsfI_core_rest [locale_witness]:
  assumes "constructive_security_aux_obsf real_resource ideal_resource sim \<I>_real \<I>_ideal (\<I>_common_core \<oplus>\<^sub>\<I> \<I>_common_rest) adv"
    and adv: "\<lbrakk> exception_\<I> (\<I>_real \<oplus>\<^sub>\<I> (\<I>_common_core \<oplus>\<^sub>\<I> \<I>_common_rest)) \<turnstile>g \<A> \<surd> \<rbrakk>
      \<Longrightarrow> advantage \<A> (obsf_resource (sim |\<^sub>= (1\<^sub>C |\<^sub>= 1\<^sub>C) \<rhd> ideal_resource)) (obsf_resource (real_resource)) \<le> adv"
  shows "constructive_security_obsf real_resource ideal_resource sim \<I>_real \<I>_ideal (\<I>_common_core \<oplus>\<^sub>\<I> \<I>_common_rest) \<A> adv"
proof -
  interpret constructive_security_aux_obsf real_resource ideal_resource sim \<I>_real \<I>_ideal "\<I>_common_core \<oplus>\<^sub>\<I> \<I>_common_rest" by fact
  show ?thesis
  proof
    assume A [WT_intro]: "exception_\<I> (\<I>_real \<oplus>\<^sub>\<I> (\<I>_common_core \<oplus>\<^sub>\<I> \<I>_common_rest)) \<turnstile>g \<A> \<surd>"
    hence outs: "outs_gpv (exception_\<I> (\<I>_real \<oplus>\<^sub>\<I> (\<I>_common_core \<oplus>\<^sub>\<I> \<I>_common_rest))) \<A> \<subseteq> outs_\<I> (\<I>_real \<oplus>\<^sub>\<I> (\<I>_common_core \<oplus>\<^sub>\<I> \<I>_common_rest))"
      unfolding WT_gpv_iff_outs_gpv by simp
    have "connect_obsf \<A> (obsf_resource (sim |\<^sub>= 1\<^sub>C \<rhd> ideal_resource)) = connect_obsf \<A> (obsf_resource (sim |\<^sub>= 1\<^sub>C |\<^sub>= 1\<^sub>C \<rhd> ideal_resource))"
      by(rule connect_cong_trace trace_eq_obsf_resourceI eq_resource_on_imp_trace_eq eq_\<I>_attach_on')+
        (rule WT_intro parallel_converter2_eq_\<I>_cong eq_\<I>_converter_reflI parallel_converter2_id_id[symmetric] order_refl outs)+
    then show "advantage \<A> (obsf_resource (sim |\<^sub>= 1\<^sub>C \<rhd> ideal_resource)) (obsf_resource real_resource) \<le> adv" 
      using adv[OF A] by(simp add: advantage_def)
  qed
qed

subsection \<open>Composition theorems\<close>

theorem constructive_security_obsf_composability:
  fixes real
  assumes "constructive_security_obsf middle ideal sim_inner \<I>_middle \<I>_inner \<I>_common (absorb \<A> (obsf_converter (sim_outer |\<^sub>= 1\<^sub>C))) adv1"
  assumes "constructive_security_obsf real middle sim_outer \<I>_real \<I>_middle \<I>_common \<A> adv2"
  shows "constructive_security_obsf real ideal (sim_outer \<odot> sim_inner) \<I>_real \<I>_inner \<I>_common \<A> (adv1 + adv2)"
proof
  let ?\<A> = "absorb \<A> (obsf_converter (sim_outer |\<^sub>= 1\<^sub>C))"
  interpret inner: constructive_security_obsf middle ideal sim_inner \<I>_middle \<I>_inner \<I>_common ?\<A> adv1 by fact
  interpret outer: constructive_security_obsf real middle sim_outer \<I>_real \<I>_middle \<I>_common \<A> adv2 by fact

  show "\<I>_real \<oplus>\<^sub>\<I> \<I>_common \<turnstile>res real \<surd>"
    and "\<I>_inner \<oplus>\<^sub>\<I> \<I>_common \<turnstile>res ideal \<surd>"
    and "\<I>_real, \<I>_inner \<turnstile>\<^sub>C sim_outer \<odot> sim_inner \<surd>"  by(rule WT_intro)+
  show "pfinite_converter \<I>_real \<I>_inner (sim_outer \<odot> sim_inner)" by(rule pfinite_intro WT_intro)+
  show "0 \<le> adv1 + adv2" using inner.adv_nonneg outer.adv_nonneg by simp

  assume WT_adv[WT_intro]: "exception_\<I> (\<I>_real \<oplus>\<^sub>\<I> \<I>_common) \<turnstile>g \<A> \<surd>"
  have eq1: "connect_obsf (absorb \<A> (obsf_converter (sim_outer |\<^sub>= 1\<^sub>C))) (obsf_resource (sim_inner |\<^sub>= 1\<^sub>C \<rhd> ideal)) = 
      connect_obsf \<A> (obsf_resource (sim_outer \<odot> sim_inner |\<^sub>= 1\<^sub>C \<rhd> ideal))"
    unfolding distinguish_attach[symmetric]
    apply(rule connect_eq_resource_cong)
      apply(rule WT_intro)
     apply(simp del: outs_plus_\<I> add: parallel_converter2_comp1_out attach_compose)
     apply(rule obsf_attach)
       apply(rule pfinite_intro WT_intro)+
    done
  have eq2: "connect_obsf (absorb \<A> (obsf_converter (sim_outer |\<^sub>= 1\<^sub>C))) (obsf_resource middle) =
      connect_obsf \<A> (obsf_resource (sim_outer |\<^sub>= 1\<^sub>C \<rhd> middle))"
    unfolding distinguish_attach[symmetric]
    apply(rule connect_eq_resource_cong)
      apply(rule WT_intro)
     apply(simp del: outs_plus_\<I> add: parallel_converter2_comp1_out attach_compose)
     apply(rule obsf_attach)
       apply(rule pfinite_intro WT_intro)+
    done

  have "advantage ?\<A> (obsf_resource (sim_inner |\<^sub>= 1\<^sub>C \<rhd> ideal)) (obsf_resource middle) \<le> adv1"
    by(rule inner.adv)(rule WT_intro)+
  moreover have "advantage \<A> (obsf_resource (sim_outer |\<^sub>= 1\<^sub>C \<rhd> middle)) (obsf_resource real) \<le> adv2"
    by(rule outer.adv)(rule WT_intro)+
  ultimately
  show "advantage \<A> (obsf_resource (sim_outer \<odot> sim_inner |\<^sub>= 1\<^sub>C \<rhd> ideal)) (obsf_resource real) \<le> adv1 + adv2"
    by(auto simp add: advantage_def eq1 eq2 abs_diff_triangle_ineq2)
qed

theorem constructive_security_obsf_lifting:
  assumes sec: "constructive_security_aux_obsf real_resource ideal_resource sim \<I>_real \<I>_ideal \<I>_common adv"
    and sec2: "exception_\<I> (\<I>_real' \<oplus>\<^sub>\<I> \<I>_common') \<turnstile>g \<A> \<surd> 
    \<Longrightarrow> constructive_security_sim_obsf real_resource ideal_resource sim \<I>_real \<I>_common (absorb \<A> (obsf_converter (w_adv_real |\<^sub>= w_usr))) adv"
    (is "_ \<Longrightarrow> constructive_security_sim_obsf _ _ _ _ _ ?\<A> _")
  assumes WT_usr [WT_intro]: "\<I>_common', \<I>_common \<turnstile>\<^sub>C w_usr \<surd>"
    and pfinite [pfinite_intro]: "pfinite_converter \<I>_common' \<I>_common w_usr"
    and WT_adv_real [WT_intro]: "\<I>_real', \<I>_real \<turnstile>\<^sub>C w_adv_real \<surd>"
    and WT_w_adv_ideal [WT_intro]: "\<I>_ideal', \<I>_ideal \<turnstile>\<^sub>C w_adv_ideal \<surd>"
    and WT_adv_ideal_inv [WT_intro]: "\<I>_ideal, \<I>_ideal' \<turnstile>\<^sub>C w_adv_ideal_inv \<surd>"
    and ideal_inverse: "\<I>_ideal, \<I>_ideal \<turnstile>\<^sub>C w_adv_ideal_inv \<odot> w_adv_ideal \<sim> 1\<^sub>C"
    and pfinite_real [pfinite_intro]: "pfinite_converter \<I>_real' \<I>_real w_adv_real"
    and pfinite_ideal [pfinite_intro]: "pfinite_converter \<I>_ideal \<I>_ideal' w_adv_ideal_inv"
  shows "constructive_security_obsf (w_adv_real |\<^sub>= w_usr \<rhd> real_resource) (w_adv_ideal |\<^sub>= w_usr \<rhd> ideal_resource) (w_adv_real \<odot> sim \<odot> w_adv_ideal_inv) \<I>_real' \<I>_ideal' \<I>_common' \<A> adv"
    (is "constructive_security_obsf ?real ?ideal ?sim ?\<I>_real ?\<I>_ideal _ _ _")
proof
  interpret constructive_security_aux_obsf real_resource ideal_resource sim \<I>_real \<I>_ideal \<I>_common by fact
  show "\<I>_real' \<oplus>\<^sub>\<I> \<I>_common' \<turnstile>res ?real \<surd>"
    and "\<I>_ideal' \<oplus>\<^sub>\<I> \<I>_common' \<turnstile>res ?ideal \<surd>"
    and "\<I>_real', \<I>_ideal' \<turnstile>\<^sub>C ?sim \<surd>" by(rule WT_intro)+
  show "pfinite_converter \<I>_real' \<I>_ideal' ?sim" by(rule pfinite_intro WT_intro)+
  show "0 \<le> adv" by(rule adv_nonneg)

  assume WT_adv [WT_intro]: "exception_\<I> (\<I>_real' \<oplus>\<^sub>\<I> \<I>_common') \<turnstile>g \<A> \<surd>"
  then interpret constructive_security_sim_obsf real_resource ideal_resource sim \<I>_real \<I>_common ?\<A> adv by(rule sec2)

  have *: "advantage ?\<A> (obsf_resource (sim |\<^sub>= 1\<^sub>C \<rhd> ideal_resource)) (obsf_resource real_resource) \<le> adv"
    by(rule adv)(rule WT_intro)+

  have ideal: "connect_obsf ?\<A> (obsf_resource (sim |\<^sub>= 1\<^sub>C \<rhd> ideal_resource)) =
    connect_obsf \<A> (obsf_resource (?sim |\<^sub>= 1\<^sub>C \<rhd> ?ideal))"
    unfolding distinguish_attach[symmetric]
    apply(rule connect_eq_resource_cong)
      apply(rule WT_intro)
     apply(simp del: outs_plus_\<I>)
     apply(rule eq_resource_on_trans[OF obsf_attach])
        apply(rule pfinite_intro WT_intro)+
     apply(rule obsf_resource_eq_\<I>_cong)
     apply(fold attach_compose)
     apply(unfold comp_converter_parallel2)
     apply(rule eq_\<I>_attach_on')
       apply(rule WT_intro)
      apply(rule parallel_converter2_eq_\<I>_cong)
       apply(unfold comp_converter_assoc)
       apply(rule eq_\<I>_comp_cong)
        apply(rule eq_\<I>_converter_reflI; rule WT_intro)
       apply(rule eq_\<I>_converter_trans[rotated])
        apply(rule eq_\<I>_comp_cong)
         apply(rule eq_\<I>_converter_reflI; rule WT_intro)
        apply(rule ideal_inverse[symmetric])
       apply(unfold comp_converter_id_right comp_converter_id_left)
       apply(rule eq_\<I>_converter_reflI; rule WT_intro)+
     apply simp
    apply(rule WT_intro)+
    done
  have real: "connect_obsf ?\<A> (obsf_resource real_resource) = connect_obsf \<A> (obsf_resource ?real)"
    unfolding distinguish_attach[symmetric]
    apply(rule connect_eq_resource_cong)
      apply(rule WT_intro)
     apply(simp del: outs_plus_\<I>)
     apply(rule obsf_attach)
       apply(rule pfinite_intro WT_intro)+
    done
  show "advantage \<A> (obsf_resource ((?sim |\<^sub>= 1\<^sub>C) \<rhd> ?ideal)) (obsf_resource ?real) \<le> adv" using *
    unfolding advantage_def ideal[symmetric] real[symmetric] .
qed

corollary constructive_security_obsf_lifting_:
  assumes sec: "constructive_security_obsf real_resource ideal_resource sim \<I>_real \<I>_ideal \<I>_common (absorb \<A> (obsf_converter (w_adv_real |\<^sub>= w_usr))) adv"
  assumes WT_usr [WT_intro]: "\<I>_common', \<I>_common \<turnstile>\<^sub>C w_usr \<surd>"
    and pfinite [pfinite_intro]: "pfinite_converter \<I>_common' \<I>_common w_usr"
    and WT_adv_real [WT_intro]: "\<I>_real', \<I>_real \<turnstile>\<^sub>C w_adv_real \<surd>"
    and WT_w_adv_ideal [WT_intro]: "\<I>_ideal', \<I>_ideal \<turnstile>\<^sub>C w_adv_ideal \<surd>"
    and WT_adv_ideal_inv [WT_intro]: "\<I>_ideal, \<I>_ideal' \<turnstile>\<^sub>C w_adv_ideal_inv \<surd>"
    and ideal_inverse: "\<I>_ideal, \<I>_ideal \<turnstile>\<^sub>C w_adv_ideal_inv \<odot> w_adv_ideal \<sim> 1\<^sub>C"
    and pfinite_real [pfinite_intro]: "pfinite_converter \<I>_real' \<I>_real w_adv_real"
    and pfinite_ideal [pfinite_intro]: "pfinite_converter \<I>_ideal \<I>_ideal' w_adv_ideal_inv"
  shows "constructive_security_obsf (w_adv_real |\<^sub>= w_usr \<rhd> real_resource) (w_adv_ideal |\<^sub>= w_usr \<rhd> ideal_resource) (w_adv_real \<odot> sim \<odot> w_adv_ideal_inv) \<I>_real' \<I>_ideal' \<I>_common' \<A> adv"
proof -
  interpret constructive_security_obsf real_resource ideal_resource sim \<I>_real \<I>_ideal \<I>_common "absorb \<A> (obsf_converter (w_adv_real |\<^sub>= w_usr))" adv by fact
  from constructive_security_aux_obsf constructive_security_sim_obsf assms(2-)
  show ?thesis by(rule constructive_security_obsf_lifting)
qed

theorem constructive_security_obsf_lifting_usr:
  assumes sec: "constructive_security_aux_obsf real_resource ideal_resource sim \<I>_real \<I>_ideal \<I>_common adv"
    and sec2: "exception_\<I> (\<I>_real \<oplus>\<^sub>\<I> \<I>_common') \<turnstile>g \<A> \<surd> 
    \<Longrightarrow> constructive_security_sim_obsf real_resource ideal_resource sim \<I>_real \<I>_common (absorb \<A> (obsf_converter (1\<^sub>C |\<^sub>= conv))) adv"
    and WT_conv [WT_intro]: "\<I>_common', \<I>_common \<turnstile>\<^sub>C conv \<surd>"
    and pfinite [pfinite_intro]: "pfinite_converter \<I>_common' \<I>_common conv"
  shows "constructive_security_obsf (1\<^sub>C |\<^sub>= conv \<rhd> real_resource) (1\<^sub>C |\<^sub>= conv \<rhd> ideal_resource) sim \<I>_real \<I>_ideal \<I>_common' \<A> adv"
  by(rule constructive_security_obsf_lifting[OF sec sec2, where ?w_adv_ideal="1\<^sub>C" and ?w_adv_ideal_inv="1\<^sub>C", simplified comp_converter_id_left comp_converter_id_right])
    (rule WT_intro pfinite_intro id_converter_eq_self order_refl | assumption)+

theorem constructive_security_obsf_lifting2:
  assumes sec: "constructive_security_aux_obsf real_resource ideal_resource sim (\<I>_real1 \<oplus>\<^sub>\<I> \<I>_real2) (\<I>_ideal1 \<oplus>\<^sub>\<I> \<I>_ideal2) \<I>_common adv"
    and sec2: "exception_\<I> ((\<I>_real1 \<oplus>\<^sub>\<I> \<I>_real2) \<oplus>\<^sub>\<I> \<I>_common') \<turnstile>g \<A> \<surd> 
    \<Longrightarrow> constructive_security_sim_obsf real_resource ideal_resource sim (\<I>_real1 \<oplus>\<^sub>\<I> \<I>_real2) \<I>_common (absorb \<A> (obsf_converter ((1\<^sub>C |\<^sub>= 1\<^sub>C) |\<^sub>= conv))) adv"
  assumes WT_conv [WT_intro]: "\<I>_common', \<I>_common \<turnstile>\<^sub>C conv \<surd>"
    and pfinite [pfinite_intro]: "pfinite_converter \<I>_common' \<I>_common conv"
  shows "constructive_security_obsf ((1\<^sub>C |\<^sub>= 1\<^sub>C) |\<^sub>= conv \<rhd> real_resource) ((1\<^sub>C |\<^sub>= 1\<^sub>C) |\<^sub>= conv \<rhd> ideal_resource) sim (\<I>_real1 \<oplus>\<^sub>\<I> \<I>_real2) (\<I>_ideal1 \<oplus>\<^sub>\<I> \<I>_ideal2) \<I>_common' \<A> adv"
    (is "constructive_security_obsf ?real ?ideal _ ?\<I>_real ?\<I>_ideal _ _ _")
proof -
  interpret constructive_security_aux_obsf real_resource ideal_resource sim "\<I>_real1 \<oplus>\<^sub>\<I> \<I>_real2" "\<I>_ideal1 \<oplus>\<^sub>\<I> \<I>_ideal2" \<I>_common adv by fact
  have sim [unfolded comp_converter_id_left]: "\<I>_real1 \<oplus>\<^sub>\<I> \<I>_real2,\<I>_ideal1 \<oplus>\<^sub>\<I> \<I>_ideal2 \<turnstile>\<^sub>C (1\<^sub>C |\<^sub>= 1\<^sub>C) \<odot> sim \<sim> 1\<^sub>C \<odot> sim"
    by(rule eq_\<I>_comp_cong)(rule parallel_converter2_id_id eq_\<I>_converter_reflI WT_intro)+
  show ?thesis
    apply(rule constructive_security_obsf_sim_cong)
      apply(rule constructive_security_obsf_lifting[OF sec sec2, where ?w_adv_ideal="1\<^sub>C |\<^sub>= 1\<^sub>C" and ?w_adv_ideal_inv="1\<^sub>C", unfolded comp_converter_id_left comp_converter_id_right])
              apply(assumption|rule WT_intro sim pfinite_intro parallel_converter2_id_id)+
    done
qed

theorem constructive_security_obsf_trivial:
  fixes res
  assumes [WT_intro]: "\<I> \<oplus>\<^sub>\<I> \<I>_common \<turnstile>res res \<surd>"
  shows "constructive_security_obsf res res 1\<^sub>C \<I> \<I> \<I>_common \<A> 0"
proof
  show "\<I> \<oplus>\<^sub>\<I> \<I>_common \<turnstile>res res \<surd>" and "\<I>, \<I> \<turnstile>\<^sub>C 1\<^sub>C \<surd>" by(rule WT_intro)+
  show "pfinite_converter \<I> \<I> 1\<^sub>C" by(rule pfinite_intro)

  assume WT [WT_intro]: "exception_\<I> (\<I> \<oplus>\<^sub>\<I> \<I>_common) \<turnstile>g \<A> \<surd>"
  have "connect_obsf \<A> (obsf_resource (1\<^sub>C |\<^sub>= 1\<^sub>C \<rhd> res)) = connect_obsf \<A> (obsf_resource (1\<^sub>C \<rhd> res))"
    by(rule connect_eq_resource_cong[OF WT])(fastforce intro: WT_intro eq_\<I>_attach_on' obsf_resource_eq_\<I>_cong parallel_converter2_id_id)+
  then show "advantage \<A> (obsf_resource (1\<^sub>C |\<^sub>= 1\<^sub>C \<rhd> res)) (obsf_resource res) \<le> 0"
    unfolding advantage_def by simp
qed simp

lemma parallel_constructive_security_aux_obsf [locale_witness]:
  assumes "constructive_security_aux_obsf real1 ideal1 sim1 \<I>_real1 \<I>_inner1 \<I>_common1 adv1"
  assumes "constructive_security_aux_obsf real2 ideal2 sim2 \<I>_real2 \<I>_inner2 \<I>_common2 adv2"
  shows "constructive_security_aux_obsf (parallel_wiring \<rhd> real1 \<parallel> real2) (parallel_wiring \<rhd> ideal1 \<parallel> ideal2) (sim1 |\<^sub>= sim2) 
    (\<I>_real1 \<oplus>\<^sub>\<I> \<I>_real2) (\<I>_inner1 \<oplus>\<^sub>\<I> \<I>_inner2) (\<I>_common1 \<oplus>\<^sub>\<I> \<I>_common2)
    (adv1 + adv2)"
proof
  interpret sec1: constructive_security_aux_obsf real1 ideal1 sim1 \<I>_real1 \<I>_inner1 \<I>_common1 adv1 by fact
  interpret sec2: constructive_security_aux_obsf real2 ideal2 sim2 \<I>_real2 \<I>_inner2 \<I>_common2 adv2 by fact

  show "(\<I>_real1 \<oplus>\<^sub>\<I> \<I>_real2) \<oplus>\<^sub>\<I> (\<I>_common1 \<oplus>\<^sub>\<I> \<I>_common2) \<turnstile>res parallel_wiring \<rhd> real1 \<parallel> real2 \<surd>"
    and "(\<I>_inner1 \<oplus>\<^sub>\<I> \<I>_inner2) \<oplus>\<^sub>\<I> (\<I>_common1 \<oplus>\<^sub>\<I> \<I>_common2) \<turnstile>res parallel_wiring \<rhd> ideal1 \<parallel> ideal2 \<surd>"
    and "\<I>_real1 \<oplus>\<^sub>\<I> \<I>_real2, \<I>_inner1 \<oplus>\<^sub>\<I> \<I>_inner2 \<turnstile>\<^sub>C sim1 |\<^sub>= sim2 \<surd>" by(rule WT_intro)+
  show "pfinite_converter (\<I>_real1 \<oplus>\<^sub>\<I> \<I>_real2) (\<I>_inner1 \<oplus>\<^sub>\<I> \<I>_inner2) (sim1 |\<^sub>= sim2)" by(rule pfinite_intro)+
  show "0 \<le> adv1 + adv2" using sec1.adv_nonneg sec2.adv_nonneg by simp
qed

theorem parallel_constructive_security_obsf:
  assumes "constructive_security_obsf real1 ideal1 sim1 \<I>_real1 \<I>_inner1 \<I>_common1 (absorb \<A> (obsf_converter (parallel_wiring \<odot> parallel_converter 1\<^sub>C (converter_of_resource (sim2 |\<^sub>= 1\<^sub>C \<rhd> ideal2))))) adv1"
    (is "constructive_security_obsf _ _ _ _ _ _ ?\<A>1 _")
  assumes "constructive_security_obsf real2 ideal2 sim2 \<I>_real2 \<I>_inner2 \<I>_common2 (absorb \<A> (obsf_converter (parallel_wiring \<odot> parallel_converter (converter_of_resource real1) 1\<^sub>C))) adv2"
    (is "constructive_security_obsf _ _ _ _ _ _ ?\<A>2 _")
  shows "constructive_security_obsf (parallel_wiring \<rhd> real1 \<parallel> real2) (parallel_wiring \<rhd> ideal1 \<parallel> ideal2) (sim1 |\<^sub>= sim2) 
    (\<I>_real1 \<oplus>\<^sub>\<I> \<I>_real2) (\<I>_inner1 \<oplus>\<^sub>\<I> \<I>_inner2) (\<I>_common1 \<oplus>\<^sub>\<I> \<I>_common2)
    \<A> (adv1 + adv2)"
proof -
  interpret sec1: constructive_security_obsf real1 ideal1 sim1 \<I>_real1 \<I>_inner1 \<I>_common1 ?\<A>1 adv1 by fact
  interpret sec2: constructive_security_obsf real2 ideal2 sim2 \<I>_real2 \<I>_inner2 \<I>_common2 ?\<A>2 adv2 by fact

  show ?thesis
  proof
    assume WT [WT_intro]: "exception_\<I> ((\<I>_real1 \<oplus>\<^sub>\<I> \<I>_real2) \<oplus>\<^sub>\<I> (\<I>_common1 \<oplus>\<^sub>\<I> \<I>_common2)) \<turnstile>g \<A> \<surd>"

    have **: "outs_\<I> ((\<I>_real1 \<oplus>\<^sub>\<I> \<I>_real2) \<oplus>\<^sub>\<I> (\<I>_common1 \<oplus>\<^sub>\<I> \<I>_common2)) \<turnstile>\<^sub>R
    ((1\<^sub>C |\<^sub>= sim2) |\<^sub>= 1\<^sub>C |\<^sub>= 1\<^sub>C) \<odot> parallel_wiring \<rhd> real1 \<parallel> ideal2 \<sim>
    parallel_wiring \<odot> (converter_of_resource real1 |\<^sub>\<propto> 1\<^sub>C) \<rhd> sim2 |\<^sub>= 1\<^sub>C \<rhd> ideal2"
      unfolding comp_parallel_wiring
      by(rule eq_resource_on_trans, rule eq_\<I>_attach_on[where conv'="parallel_wiring \<odot> (1\<^sub>C |\<^sub>= sim2 |\<^sub>= 1\<^sub>C)"]
          , (rule WT_intro)+, rule eq_\<I>_comp_cong, rule eq_\<I>_converter_mono)
        (auto simp add: le_\<I>_def attach_compose attach_parallel2 attach_converter_of_resource_conv_parallel_resource
          intro: WT_intro parallel_converter2_eq_\<I>_cong parallel_converter2_id_id eq_\<I>_converter_reflI)

    have ideal2:
      "connect_obsf ?\<A>2 (obsf_resource (sim2 |\<^sub>= 1\<^sub>C \<rhd> ideal2)) =
     connect_obsf \<A> (obsf_resource ((1\<^sub>C |\<^sub>= sim2) |\<^sub>= (1\<^sub>C |\<^sub>= 1\<^sub>C) \<rhd> parallel_wiring \<rhd> real1 \<parallel> ideal2))"
      unfolding distinguish_attach[symmetric]
      apply(rule connect_eq_resource_cong)
        apply(rule WT_intro)
       apply(simp del: outs_plus_\<I>)
       apply(rule eq_resource_on_trans[OF obsf_attach])
          apply(rule pfinite_intro WT_intro)+
       apply(rule obsf_resource_eq_\<I>_cong)
       apply(rule eq_resource_on_sym)
       apply(subst attach_compose[symmetric])
       apply(rule **)
      apply(rule WT_intro)+
      done

    have real2: "connect_obsf ?\<A>2 (obsf_resource real2) = connect_obsf \<A> (obsf_resource (parallel_wiring \<rhd> real1 \<parallel> real2))"
      unfolding distinguish_attach[symmetric]
      apply(rule connect_eq_resource_cong)
        apply(rule WT_intro)
       apply(simp del: outs_plus_\<I>)
       apply(rule eq_resource_on_trans[OF obsf_attach])
          apply(rule pfinite_intro WT_intro)+
       apply(rule obsf_resource_eq_\<I>_cong)
       apply(rule eq_resource_on_sym)
      by(simp add: attach_compose attach_converter_of_resource_conv_parallel_resource)(rule WT_intro)+

    have adv2: "advantage \<A>
     (obsf_resource ((1\<^sub>C |\<^sub>= sim2) |\<^sub>= (1\<^sub>C |\<^sub>= 1\<^sub>C) \<rhd> parallel_wiring \<rhd> real1 \<parallel> ideal2))
     (obsf_resource (parallel_wiring \<rhd> real1 \<parallel> real2)) \<le> adv2"
      unfolding advantage_def ideal2[symmetric] real2[symmetric] by(rule sec2.adv[unfolded advantage_def])(rule WT_intro)+

    have ideal1: 
      "connect_obsf ?\<A>1 (obsf_resource (sim1 |\<^sub>= 1\<^sub>C \<rhd> ideal1)) = 
     connect_obsf \<A> (obsf_resource ((sim1 |\<^sub>= sim2) |\<^sub>= (1\<^sub>C |\<^sub>= 1\<^sub>C) \<rhd> parallel_wiring \<rhd> ideal1 \<parallel> ideal2))"
    proof -
      have *:"((outs_\<I> \<I>_real1 <+> outs_\<I> \<I>_real2) <+> outs_\<I> \<I>_common1 <+> outs_\<I> \<I>_common2) \<turnstile>\<^sub>R
    (sim1 |\<^sub>= sim2) |\<^sub>= (1\<^sub>C |\<^sub>= 1\<^sub>C) \<rhd> parallel_wiring \<rhd> ideal1 \<parallel> ideal2 \<sim>
    parallel_wiring \<odot> (1\<^sub>C |\<^sub>\<propto> converter_of_resource (sim2 |\<^sub>= 1\<^sub>C \<rhd> ideal2)) \<rhd> sim1 |\<^sub>= 1\<^sub>C \<rhd> ideal1"
        by(auto simp add: le_\<I>_def comp_parallel_wiring' attach_compose attach_parallel2 attach_converter_of_resource_conv_parallel_resource2 intro: WT_intro)
      show ?thesis
        unfolding distinguish_attach[symmetric] 
        apply(rule connect_eq_resource_cong)
          apply(rule WT_intro)
         apply(simp del: outs_plus_\<I>)
         apply(rule eq_resource_on_trans[OF obsf_attach])
            apply(rule pfinite_intro WT_intro)+
         apply(rule obsf_resource_eq_\<I>_cong)
         apply(rule eq_resource_on_sym)
        by(simp add: *, (rule WT_intro)+)
    qed

    have real1: "connect_obsf ?\<A>1 (obsf_resource real1) = connect_obsf \<A> (obsf_resource ((1\<^sub>C |\<^sub>= sim2) |\<^sub>= (1\<^sub>C |\<^sub>= 1\<^sub>C) \<rhd> parallel_wiring \<rhd> real1 \<parallel> ideal2))"
    proof -
      have *: "outs_\<I> ((\<I>_real1 \<oplus>\<^sub>\<I> \<I>_real2) \<oplus>\<^sub>\<I> (\<I>_common1 \<oplus>\<^sub>\<I> \<I>_common2)) \<turnstile>\<^sub>R
    parallel_wiring \<odot> ((1\<^sub>C |\<^sub>= 1\<^sub>C) |\<^sub>= sim2 |\<^sub>= 1\<^sub>C) \<rhd> real1 \<parallel> ideal2 \<sim>
    parallel_wiring \<odot> (1\<^sub>C |\<^sub>\<propto> converter_of_resource (sim2 |\<^sub>= 1\<^sub>C \<rhd> ideal2 )) \<rhd> real1"
        by(rule eq_resource_on_trans, rule eq_\<I>_attach_on[where conv'="parallel_wiring \<odot> (1\<^sub>C |\<^sub>= sim2 |\<^sub>= 1\<^sub>C)"]
            , (rule WT_intro)+, rule eq_\<I>_comp_cong, rule eq_\<I>_converter_mono)
          (auto simp add: le_\<I>_def attach_compose attach_converter_of_resource_conv_parallel_resource2 attach_parallel2 
            intro: WT_intro parallel_converter2_eq_\<I>_cong parallel_converter2_id_id eq_\<I>_converter_reflI)

      show ?thesis
        unfolding distinguish_attach[symmetric] 
        apply(rule connect_eq_resource_cong)
          apply(rule WT_intro)
         apply(simp del: outs_plus_\<I>)
         apply(rule eq_resource_on_trans[OF obsf_attach])
            apply(rule pfinite_intro WT_intro)+
         apply(rule obsf_resource_eq_\<I>_cong)
         apply(rule eq_resource_on_sym)
         apply(fold attach_compose)
         apply(subst comp_parallel_wiring)
         apply(rule *)
        apply(rule WT_intro)+
        done
    qed

    have adv1: "advantage \<A> 
     (obsf_resource ((sim1 |\<^sub>= sim2) |\<^sub>= (1\<^sub>C |\<^sub>= 1\<^sub>C) \<rhd> parallel_wiring \<rhd> ideal1 \<parallel> ideal2))
     (obsf_resource ((1\<^sub>C |\<^sub>= sim2) |\<^sub>= (1\<^sub>C |\<^sub>= 1\<^sub>C) \<rhd> parallel_wiring \<rhd> real1 \<parallel> ideal2)) \<le> adv1"
      unfolding advantage_def ideal1[symmetric] real1[symmetric] by(rule sec1.adv[unfolded advantage_def])(rule WT_intro)+

    from adv1 adv2 show "advantage \<A> (obsf_resource ((sim1 |\<^sub>= sim2) |\<^sub>= (1\<^sub>C |\<^sub>= 1\<^sub>C) \<rhd> parallel_wiring \<rhd> ideal1 \<parallel> ideal2))
         (obsf_resource (parallel_wiring \<rhd> real1 \<parallel> real2)) \<le> adv1 + adv2"
      by(auto simp add: advantage_def)
  qed
qed

theorem parallel_constructive_security_obsf_fuse:
  assumes 1: "constructive_security_obsf real1 ideal1 sim1 (\<I>_real1_core \<oplus>\<^sub>\<I> \<I>_real1_rest) (\<I>_ideal1_core \<oplus>\<^sub>\<I> \<I>_ideal1_rest) (\<I>_common1_core \<oplus>\<^sub>\<I> \<I>_common1_rest) (absorb \<A> (obsf_converter (fused_wiring \<odot> parallel_converter 1\<^sub>C (converter_of_resource (sim2 |\<^sub>= 1\<^sub>C \<rhd> ideal2))))) adv1"
    (is "constructive_security_obsf _ _ _ ?\<I>_real1 ?\<I>_ideal1 ?\<I>_common1 ?\<A>1 _")
  assumes 2: "constructive_security_obsf real2 ideal2 sim2 (\<I>_real2_core \<oplus>\<^sub>\<I> \<I>_real2_rest) (\<I>_ideal2_core \<oplus>\<^sub>\<I> \<I>_ideal2_rest) (\<I>_common2_core \<oplus>\<^sub>\<I> \<I>_common2_rest) (absorb \<A> (obsf_converter (fused_wiring \<odot> parallel_converter (converter_of_resource real1) 1\<^sub>C))) adv2"
    (is "constructive_security_obsf _ _ _ ?\<I>_real2 ?\<I>_ideal2 ?\<I>_common2 ?\<A>2 _")
  shows "constructive_security_obsf (fused_wiring \<rhd> real1 \<parallel> real2) (fused_wiring \<rhd> ideal1 \<parallel> ideal2) 
    (parallel_wiring \<odot> (sim1 |\<^sub>= sim2) \<odot> parallel_wiring)
    ((\<I>_real1_core \<oplus>\<^sub>\<I> \<I>_real2_core) \<oplus>\<^sub>\<I> (\<I>_real1_rest \<oplus>\<^sub>\<I> \<I>_real2_rest)) 
    ((\<I>_ideal1_core \<oplus>\<^sub>\<I> \<I>_ideal2_core) \<oplus>\<^sub>\<I> (\<I>_ideal1_rest \<oplus>\<^sub>\<I> \<I>_ideal2_rest))
    ((\<I>_common1_core \<oplus>\<^sub>\<I> \<I>_common2_core) \<oplus>\<^sub>\<I> (\<I>_common1_rest \<oplus>\<^sub>\<I> \<I>_common2_rest))
    \<A> (adv1 + adv2)"
proof -
  interpret sec1: constructive_security_obsf real1 ideal1 sim1 ?\<I>_real1 ?\<I>_ideal1 ?\<I>_common1 ?\<A>1 adv1 by fact
  interpret sec2: constructive_security_obsf real2 ideal2 sim2 ?\<I>_real2 ?\<I>_ideal2 ?\<I>_common2 ?\<A>2 adv2 by fact

  have aux1: "constructive_security_aux_obsf real1 ideal1 sim1 ?\<I>_real1 ?\<I>_ideal1 ?\<I>_common1 adv1" ..
  have aux2: "constructive_security_aux_obsf real2 ideal2 sim2 ?\<I>_real2 ?\<I>_ideal2 ?\<I>_common2 adv2" ..

  have sim: "constructive_security_sim_obsf (parallel_wiring \<rhd> real1 \<parallel> real2) (parallel_wiring \<rhd> ideal1 \<parallel> ideal2) (sim1 |\<^sub>= sim2)
      (?\<I>_real1 \<oplus>\<^sub>\<I> ?\<I>_real2) (?\<I>_common1 \<oplus>\<^sub>\<I> ?\<I>_common2)
      (absorb \<A> (obsf_converter (parallel_wiring |\<^sub>= parallel_wiring)))
      (adv1 + adv2)"
    if [WT_intro]: "exception_\<I> (((\<I>_real1_core \<oplus>\<^sub>\<I> \<I>_real2_core) \<oplus>\<^sub>\<I> (\<I>_real1_rest \<oplus>\<^sub>\<I> \<I>_real2_rest)) \<oplus>\<^sub>\<I> ((\<I>_common1_core \<oplus>\<^sub>\<I> \<I>_common2_core) \<oplus>\<^sub>\<I> (\<I>_common1_rest \<oplus>\<^sub>\<I> \<I>_common2_rest))) \<turnstile>g \<A> \<surd>"
  proof -
    interpret constructive_security_obsf 
      "parallel_wiring \<rhd> real1 \<parallel> real2"
      "parallel_wiring \<rhd> ideal1 \<parallel> ideal2"
      "sim1 |\<^sub>= sim2"
      "?\<I>_real1 \<oplus>\<^sub>\<I> ?\<I>_real2" "?\<I>_ideal1 \<oplus>\<^sub>\<I> ?\<I>_ideal2" "?\<I>_common1 \<oplus>\<^sub>\<I> ?\<I>_common2"
      "absorb \<A> (obsf_converter (parallel_wiring |\<^sub>= parallel_wiring))"
      "adv1 + adv2"
      apply(rule parallel_constructive_security_obsf)
       apply(fold absorb_comp_converter)
       apply(rule constructive_security_obsf_absorb_cong[OF 1])
          apply(rule WT_intro)+
       apply(unfold fused_wiring_def comp_converter_assoc)
       apply(rule obsf_comp_converter)
         apply(rule WT_intro pfinite_intro)+
      apply(rule constructive_security_obsf_absorb_cong[OF 2])
         apply(rule WT_intro)+
      apply(subst fused_wiring_def)                                               
      apply(unfold comp_converter_assoc)
      apply(rule obsf_comp_converter)
        apply(rule WT_intro pfinite_intro wiring_intro parallel_wiring_inverse)+
      done
    show ?thesis ..
  qed
  show ?thesis
    unfolding fused_wiring_def attach_compose
    apply(rule constructive_security_obsf_lifting[where w_adv_ideal_inv=parallel_wiring])
             apply(rule parallel_constructive_security_aux_obsf[OF aux1 aux2])
            apply(erule sim)
           apply(rule WT_intro pfinite_intro parallel_wiring_inverse)+
    done
qed

end