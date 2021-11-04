theory Asymptotic_Security imports Concrete_Security begin

section \<open>Asymptotic security definition\<close>

locale constructive_security_obsf' =
  fixes real_resource :: "security \<Rightarrow> ('a + 'e, 'b + 'f) resource"
    and ideal_resource :: "security \<Rightarrow> ('c + 'e, 'd + 'f) resource"
    and sim :: "security \<Rightarrow> ('a, 'b, 'c, 'd) converter"
    and \<I>_real :: "security \<Rightarrow> ('a, 'b) \<I>"
    and \<I>_ideal :: "security \<Rightarrow> ('c, 'd) \<I>"
    and \<I>_common :: "security \<Rightarrow> ('e, 'f) \<I>"
    and \<A> :: "security \<Rightarrow> ('a + 'e, 'b + 'f) distinguisher_obsf"
  assumes constructive_security_aux_obsf: "\<And>\<eta>.
    constructive_security_aux_obsf (real_resource \<eta>) (ideal_resource \<eta>) (sim \<eta>) (\<I>_real \<eta>) (\<I>_ideal \<eta>) (\<I>_common \<eta>) 0"
    and adv: "\<lbrakk> \<And>\<eta>. exception_\<I> (\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) \<turnstile>g \<A> \<eta> \<surd> \<rbrakk>
      \<Longrightarrow> negligible (\<lambda>\<eta>. advantage (\<A> \<eta>) (obsf_resource (sim \<eta> |\<^sub>= 1\<^sub>C \<rhd> ideal_resource \<eta>)) (obsf_resource (real_resource \<eta>)))"
begin

sublocale constructive_security_aux_obsf 
  "real_resource \<eta>"
  "ideal_resource \<eta>"
  "sim \<eta>" 
  "\<I>_real \<eta>"
  "\<I>_ideal \<eta>"
  "\<I>_common \<eta>"
  "0"
  for \<eta> by(rule constructive_security_aux_obsf)

lemma constructive_security_obsf'D:
  "constructive_security_obsf (real_resource \<eta>) (ideal_resource \<eta>) (sim \<eta>) (\<I>_real \<eta>) (\<I>_ideal \<eta>) (\<I>_common \<eta>) (\<A> \<eta>)
    (advantage (\<A> \<eta>) (obsf_resource (sim \<eta> |\<^sub>= 1\<^sub>C \<rhd> ideal_resource \<eta>)) (obsf_resource (real_resource \<eta>)))"
  by(rule constructive_security_obsf_refl)

end

lemma constructive_security_obsf'I:
  assumes "\<And>\<eta>. constructive_security_obsf (real_resource \<eta>) (ideal_resource \<eta>) (sim \<eta>) (\<I>_real \<eta>) (\<I>_ideal \<eta>) (\<I>_common \<eta>) (\<A> \<eta>) (adv \<eta>)"
    and "(\<And>\<eta>. exception_\<I> (\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) \<turnstile>g \<A> \<eta> \<surd>) \<Longrightarrow> negligible adv"
  shows "constructive_security_obsf' real_resource ideal_resource sim \<I>_real \<I>_ideal \<I>_common \<A>"
proof -
  interpret constructive_security_obsf 
    "real_resource \<eta>"
    "ideal_resource \<eta>"
    "sim \<eta>" 
    "\<I>_real \<eta>"
    "\<I>_ideal \<eta>"
    "\<I>_common \<eta>"
    "\<A> \<eta>"
    "adv \<eta>"
    for \<eta> by fact
  show ?thesis 
  proof
    show "negligible (\<lambda>\<eta>. advantage (\<A> \<eta>) (obsf_resource (sim \<eta> |\<^sub>= 1\<^sub>C \<rhd> ideal_resource \<eta>)) (obsf_resource (real_resource \<eta>)))"
      if "\<And>\<eta>. exception_\<I> (\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) \<turnstile>g \<A> \<eta> \<surd>" using assms(2)[OF that]
      by(rule negligible_mono)(auto intro!: eventuallyI landau_o.big_mono simp add: advantage_nonneg adv_nonneg adv[OF that])
  qed(rule WT_intro pfinite_intro order_refl)+
qed

lemma constructive_security_obsf'_into_constructive_security:
  assumes "\<And>\<A> :: security \<Rightarrow> ('a + 'b, 'c + 'd) distinguisher_obsf. 
   \<lbrakk>  \<And>\<eta>. interaction_bounded_by (\<lambda>_. True) (\<A> \<eta>) (bound \<eta>);
      \<And>\<eta>. lossless \<Longrightarrow> plossless_gpv (exception_\<I> (\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>)) (\<A> \<eta>) \<rbrakk>
   \<Longrightarrow> constructive_security_obsf' real_resource ideal_resource sim \<I>_real \<I>_ideal \<I>_common \<A>"
    and correct: "\<exists>cnv. \<forall>\<D>. (\<forall>\<eta>. \<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g \<D> \<eta> \<surd>) \<longrightarrow>
               (\<forall>\<eta>. interaction_any_bounded_by (\<D> \<eta>) (bound \<eta>)) \<longrightarrow>
               (\<forall>\<eta>. lossless \<longrightarrow> plossless_gpv (\<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) (\<D> \<eta>)) \<longrightarrow>
               (\<forall>\<eta>. wiring (\<I>_ideal \<eta>) (\<I>_real \<eta>) (cnv \<eta>) (w \<eta>)) \<and>
               Negligible.negligible (\<lambda>\<eta>. advantage (\<D> \<eta>) (ideal_resource \<eta>) (cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> real_resource \<eta>))"
  shows "constructive_security real_resource ideal_resource sim \<I>_real \<I>_ideal \<I>_common bound lossless w"
proof
  interpret constructive_security_obsf' real_resource ideal_resource sim \<I>_real \<I>_ideal \<I>_common \<open>\<lambda>_. Done undefined\<close>
    by(rule assms) simp_all 
  show "\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>res real_resource \<eta> \<surd>" 
    and "\<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>res ideal_resource \<eta> \<surd>"
    and "\<I>_real \<eta>, \<I>_ideal \<eta> \<turnstile>\<^sub>C sim \<eta> \<surd>" for \<eta> by(rule WT_intro)+ 

  show "\<exists>cnv. \<forall>\<D>. (\<forall>\<eta>. \<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g \<D> \<eta> \<surd>) \<longrightarrow>
               (\<forall>\<eta>. interaction_any_bounded_by (\<D> \<eta>) (bound \<eta>)) \<longrightarrow>
               (\<forall>\<eta>. lossless \<longrightarrow> plossless_gpv (\<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) (\<D> \<eta>)) \<longrightarrow>
               (\<forall>\<eta>. wiring (\<I>_ideal \<eta>) (\<I>_real \<eta>) (cnv \<eta>) (w \<eta>)) \<and>
               Negligible.negligible (\<lambda>\<eta>. advantage (\<D> \<eta>) (ideal_resource \<eta>) (cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> real_resource \<eta>))"
    by fact
next
  fix \<A> :: "security \<Rightarrow> ('a + 'b, 'c + 'd) distinguisher"
  assume WT_adv [WT_intro]: "\<And>\<eta>. \<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g \<A> \<eta> \<surd>"
    and bound [interaction_bound]: "\<And>\<eta>. interaction_any_bounded_by (\<A> \<eta>) (bound \<eta>)"
    and lossless: "\<And>\<eta>. lossless \<Longrightarrow> plossless_gpv (\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) (\<A> \<eta>)"
  let ?\<A> = "\<lambda>\<eta>. obsf_distinguisher (\<A> \<eta>)"
  interpret constructive_security_obsf' real_resource ideal_resource sim \<I>_real \<I>_ideal \<I>_common ?\<A>
  proof(rule assms)
    show "interaction_any_bounded_by (?\<A> \<eta>) (bound \<eta>)" for \<eta> by(rule interaction_bound)+
    show "plossless_gpv (exception_\<I> (\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>)) (?\<A> \<eta>)" if lossless for \<eta>
      using WT_adv[of \<eta>] lossless that by(simp)
  qed
  have "negligible (\<lambda>\<eta>. advantage (?\<A> \<eta>) (obsf_resource (sim \<eta> |\<^sub>= 1\<^sub>C \<rhd> ideal_resource \<eta>)) (obsf_resource (real_resource \<eta>)))"
    by(rule adv)(rule WT_intro)+
  then show "negligible (\<lambda>\<eta>. advantage (\<A> \<eta>) (sim \<eta> |\<^sub>= 1\<^sub>C \<rhd> ideal_resource \<eta>) (real_resource \<eta>))"
    unfolding advantage_obsf_distinguisher .
qed

subsection \<open>Composition theorems\<close>

theorem constructive_security_obsf'_composability:
  fixes real
  assumes "constructive_security_obsf' middle ideal sim_inner \<I>_middle \<I>_inner \<I>_common (\<lambda>\<eta>. absorb (\<A> \<eta>) (obsf_converter (sim_outer \<eta> |\<^sub>= 1\<^sub>C)))"
  assumes "constructive_security_obsf' real middle sim_outer \<I>_real \<I>_middle \<I>_common \<A>"
  shows "constructive_security_obsf' real ideal (\<lambda>\<eta>. sim_outer \<eta> \<odot> sim_inner \<eta>) \<I>_real \<I>_inner \<I>_common \<A>"
proof(rule constructive_security_obsf'I)
  let ?\<A> = "\<lambda>\<eta>. absorb (\<A> \<eta>) (obsf_converter (sim_outer \<eta> |\<^sub>= 1\<^sub>C))"
  interpret inner: constructive_security_obsf' middle ideal sim_inner \<I>_middle \<I>_inner \<I>_common ?\<A> by fact
  interpret outer: constructive_security_obsf' real middle sim_outer \<I>_real \<I>_middle \<I>_common \<A> by fact

  let ?adv1 = "\<lambda>\<eta>. advantage (?\<A> \<eta>) (obsf_resource (sim_inner \<eta> |\<^sub>= 1\<^sub>C \<rhd> ideal \<eta>)) (obsf_resource (middle \<eta>))"
  let ?adv2 = "\<lambda>\<eta>. advantage (\<A> \<eta>) (obsf_resource (sim_outer \<eta> |\<^sub>= 1\<^sub>C \<rhd> middle \<eta>)) (obsf_resource (real \<eta>))"
  let ?adv = "\<lambda>\<eta>. ?adv1 \<eta> + ?adv2 \<eta>"    
  show "constructive_security_obsf (real \<eta>) (ideal \<eta>) (sim_outer \<eta> \<odot> sim_inner \<eta>) (\<I>_real \<eta>) (\<I>_inner \<eta>) (\<I>_common \<eta>) (\<A> \<eta>) (?adv \<eta>)" for \<eta>
    using inner.constructive_security_obsf'D outer.constructive_security_obsf'D
    by(rule constructive_security_obsf_composability)
  assume [WT_intro]: "exception_\<I> (\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) \<turnstile>g \<A> \<eta> \<surd>" for \<eta>
  have "negligible ?adv1" by(rule inner.adv)(rule WT_intro)+
  also have "negligible ?adv2" by(rule outer.adv)(rule WT_intro)+
  finally (negligible_plus) show "negligible ?adv" .
qed

theorem constructive_security_obsf'_lifting: (* TODO: generalize! *)
  assumes sec: "constructive_security_obsf' real_resource ideal_resource sim \<I>_real \<I>_ideal \<I>_common (\<lambda>\<eta>. absorb (\<A> \<eta>) (obsf_converter (1\<^sub>C |\<^sub>= conv \<eta>)))"
  assumes WT_conv [WT_intro]: "\<And>\<eta>. \<I>_common' \<eta>, \<I>_common \<eta> \<turnstile>\<^sub>C conv \<eta> \<surd>"
    and pfinite [pfinite_intro]: "\<And>\<eta>. pfinite_converter (\<I>_common' \<eta>) (\<I>_common \<eta>) (conv \<eta>)"
  shows "constructive_security_obsf'
     (\<lambda>\<eta>. 1\<^sub>C |\<^sub>= conv \<eta> \<rhd> real_resource \<eta>) (\<lambda>\<eta>. 1\<^sub>C |\<^sub>= conv \<eta> \<rhd> ideal_resource \<eta>) sim
     \<I>_real \<I>_ideal \<I>_common' \<A>"
proof(rule constructive_security_obsf'I)
  let ?\<A> = "\<lambda>\<eta>. absorb (\<A> \<eta>) (obsf_converter (1\<^sub>C |\<^sub>= conv \<eta>))"
  interpret constructive_security_obsf' real_resource ideal_resource sim \<I>_real \<I>_ideal \<I>_common ?\<A> by fact
  let ?adv = "\<lambda>\<eta>. advantage (?\<A> \<eta>) (obsf_resource (sim \<eta> |\<^sub>= 1\<^sub>C \<rhd> ideal_resource \<eta>)) (obsf_resource (real_resource \<eta>))" 

  fix \<eta> :: security
  show "constructive_security_obsf (1\<^sub>C |\<^sub>= conv \<eta> \<rhd> real_resource \<eta>) (1\<^sub>C |\<^sub>= conv \<eta> \<rhd> ideal_resource \<eta>) (sim \<eta>)
     (\<I>_real \<eta>) (\<I>_ideal \<eta>) (\<I>_common' \<eta>) (\<A> \<eta>)
     (?adv \<eta>)"
    using constructive_security_obsf.constructive_security_aux_obsf[OF constructive_security_obsf'D]
     constructive_security_obsf.constructive_security_sim_obsf[OF constructive_security_obsf'D]
    by(rule constructive_security_obsf_lifting_usr)(rule WT_intro pfinite_intro)+
  show "negligible ?adv" if [WT_intro]: "\<And>\<eta>. exception_\<I> (\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common' \<eta>) \<turnstile>g \<A> \<eta> \<surd>"
    by(rule adv)(rule WT_intro)+
qed

theorem constructive_security_obsf'_trivial:
  fixes res
  assumes [WT_intro]: "\<And>\<eta>. \<I> \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>res res \<eta> \<surd>"
  shows "constructive_security_obsf' res res (\<lambda>_. 1\<^sub>C) \<I> \<I> \<I>_common \<A>"
proof(rule constructive_security_obsf'I)
  show "constructive_security_obsf (res \<eta>) (res \<eta>) 1\<^sub>C (\<I> \<eta>) (\<I> \<eta>) (\<I>_common \<eta>) (\<A> \<eta>) 0" for \<eta>
    using assms by(rule constructive_security_obsf_trivial)
qed simp

theorem parallel_constructive_security_obsf':
  assumes "constructive_security_obsf' real1 ideal1 sim1 \<I>_real1 \<I>_inner1 \<I>_common1 (\<lambda>\<eta>. absorb (\<A> \<eta>) (obsf_converter (parallel_wiring \<odot> parallel_converter 1\<^sub>C (converter_of_resource (sim2 \<eta> |\<^sub>= 1\<^sub>C \<rhd> ideal2 \<eta>)))))"
    (is "constructive_security_obsf' _ _ _ _ _ _ ?\<A>1")
  assumes "constructive_security_obsf' real2 ideal2 sim2 \<I>_real2 \<I>_inner2 \<I>_common2 (\<lambda>\<eta>. absorb (\<A> \<eta>) (obsf_converter (parallel_wiring \<odot> parallel_converter (converter_of_resource (real1 \<eta>)) 1\<^sub>C)))"
    (is "constructive_security_obsf' _ _ _ _ _ _ ?\<A>2")
  shows "constructive_security_obsf' (\<lambda>\<eta>. parallel_wiring \<rhd> real1 \<eta> \<parallel> real2 \<eta>) (\<lambda>\<eta>. parallel_wiring \<rhd> ideal1 \<eta> \<parallel> ideal2 \<eta>) (\<lambda>\<eta>. sim1 \<eta> |\<^sub>= sim2 \<eta>) 
    (\<lambda>\<eta>. \<I>_real1 \<eta> \<oplus>\<^sub>\<I> \<I>_real2 \<eta>) (\<lambda>\<eta>. \<I>_inner1 \<eta> \<oplus>\<^sub>\<I> \<I>_inner2 \<eta>) (\<lambda>\<eta>. \<I>_common1 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta>) \<A>"
proof(rule constructive_security_obsf'I)
  interpret sec1: constructive_security_obsf' real1 ideal1 sim1 \<I>_real1 \<I>_inner1 \<I>_common1 ?\<A>1 by fact
  interpret sec2: constructive_security_obsf' real2 ideal2 sim2 \<I>_real2 \<I>_inner2 \<I>_common2 ?\<A>2 by fact
  let ?adv1 = "\<lambda>\<eta>. advantage (?\<A>1 \<eta>) (obsf_resource (sim1 \<eta> |\<^sub>= 1\<^sub>C \<rhd> ideal1 \<eta>)) (obsf_resource (real1 \<eta>))"
  let ?adv2 = "\<lambda>\<eta>. advantage (?\<A>2 \<eta>) (obsf_resource (sim2 \<eta> |\<^sub>= 1\<^sub>C \<rhd> ideal2 \<eta>)) (obsf_resource (real2 \<eta>))"
  let ?adv = "\<lambda>\<eta>. ?adv1 \<eta> + ?adv2 \<eta>"
  show "constructive_security_obsf (parallel_wiring \<rhd> real1 \<eta> \<parallel> real2 \<eta>) (parallel_wiring \<rhd> ideal1 \<eta> \<parallel> ideal2 \<eta>)
     (sim1 \<eta> |\<^sub>= sim2 \<eta>) (\<I>_real1 \<eta> \<oplus>\<^sub>\<I> \<I>_real2 \<eta>) (\<I>_inner1 \<eta> \<oplus>\<^sub>\<I> \<I>_inner2 \<eta>) (\<I>_common1 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta>) (\<A> \<eta>)
     (?adv \<eta>)" for \<eta>
    using sec1.constructive_security_obsf'D sec2.constructive_security_obsf'D
    by(rule parallel_constructive_security_obsf)
  assume [WT_intro]: "exception_\<I> ((\<I>_real1 \<eta> \<oplus>\<^sub>\<I> \<I>_real2 \<eta>) \<oplus>\<^sub>\<I> (\<I>_common1 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta>)) \<turnstile>g \<A> \<eta> \<surd>" for \<eta>
  have "negligible ?adv1" by(rule sec1.adv)(rule WT_intro)+
  also have "negligible ?adv2" by(rule sec2.adv)(rule WT_intro)+
  finally (negligible_plus) show "negligible ?adv" .
qed

end