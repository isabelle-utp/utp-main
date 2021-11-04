theory DH_OTP imports
  One_Time_Pad
  Diffie_Hellman_CC
begin

text \<open>
  We need both a group structure and a boolean algebra.
  Unfortunately, records allow only one extension slot, so we can't have just a single
  structure with both operations.
\<close>

context diffie_hellman begin

lemma WT_ideal_rest [WT_intro]:
  assumes WT_auth1_rest [WT_intro]: "WT_rest \<I>_adv_rest1 \<I>_usr_rest1 I_auth1_rest auth1_rest"
    and WT_auth2_rest [WT_intro]: "WT_rest \<I>_adv_rest2 \<I>_usr_rest2 I_auth2_rest auth2_rest"
  shows "WT_rest (\<I>_full \<oplus>\<^sub>\<I> (\<I>_adv_rest1 \<oplus>\<^sub>\<I> \<I>_adv_rest2)) ((\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<oplus>\<^sub>\<I> (\<I>_usr_rest1 \<oplus>\<^sub>\<I> \<I>_usr_rest2))
     (\<lambda>(_, s). pred_prod I_auth1_rest I_auth2_rest s) (ideal_rest auth1_rest auth2_rest)"
  apply(rule WT_rest.intros)
  subgoal
    by(auto 4 4 split: sum.splits simp add: translate_eoracle_def parallel_eoracle_def dest: assms[THEN WT_restD_rfunc_adv])
  subgoal
    apply(auto 4 4 split: sum.splits simp add: translate_eoracle_def parallel_eoracle_def plus_eoracle_def dest: assms[THEN WT_restD_rfunc_usr])
    apply(simp add: map_sum_def split: sum.splits)
    done
  subgoal by(simp add: assms[THEN WT_restD_rinit])
done

end


locale dh_otp = dh: diffie_hellman \<G> + otp: one_time_pad \<L>
  for \<G> :: "'grp cyclic_group"
    and \<L> :: "'grp boolean_algebra" +
  assumes carrier_\<G>_\<L>: "carrier \<G> = carrier \<L>"
begin

theorem secure:
  assumes "WT_rest \<I>_adv_resta \<I>_usr_resta I_auth_rest auth_rest"
    and "WT_rest \<I>_adv_rest1 \<I>_usr_rest1 I_auth1_rest auth1_rest"
    and "WT_rest \<I>_adv_rest2 \<I>_usr_rest2 I_auth2_rest auth2_rest"
  shows
    "constructive_security_obsf
      (1\<^sub>C |\<^sub>= wiring_c1r22_c1r22 (CNV otp.enc_callee ()) (CNV otp.dec_callee ()) |\<^sub>= 1\<^sub>C \<rhd>
       fused_wiring \<rhd> diffie_hellman.real_resource \<G> auth1_rest auth2_rest \<parallel> dh.auth.resource auth_rest)
      (otp.sec.resource (otp.ideal_rest (dh.ideal_rest auth1_rest auth2_rest) auth_rest))
      ((1\<^sub>C \<odot>
        (parallel_wiring \<odot> ((let sim = CNV dh.sim_callee None in (sim |\<^sub>= 1\<^sub>C) \<odot> lassocr\<^sub>C) |\<^sub>= 1\<^sub>C) \<odot> parallel_wiring) \<odot>
        1\<^sub>C) \<odot>
       (otp.sim |\<^sub>= 1\<^sub>C))
      ((((\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_uniform (otp.sec.Inp_Fedit ` carrier \<G>) UNIV)) \<oplus>\<^sub>\<I>
         (\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_uniform (otp.sec.Inp_Fedit ` carrier \<G>) UNIV))) \<oplus>\<^sub>\<I>
        (\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_uniform (otp.sec.Inp_Fedit ` carrier \<L>) UNIV))) \<oplus>\<^sub>\<I>
       ((\<I>_adv_rest1 \<oplus>\<^sub>\<I> \<I>_adv_rest2) \<oplus>\<^sub>\<I> \<I>_adv_resta))
      ((\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_uniform (otp.sec.Inp_Fedit ` carrier \<L>) UNIV)) \<oplus>\<^sub>\<I>
       ((\<I>_full \<oplus>\<^sub>\<I> (\<I>_adv_rest1 \<oplus>\<^sub>\<I> \<I>_adv_rest2)) \<oplus>\<^sub>\<I> \<I>_adv_resta))
      ((\<I>_uniform (otp.sec.Inp_Send ` carrier \<L>) UNIV \<oplus>\<^sub>\<I> \<I>_uniform UNIV (otp.sec.Out_Recv ` carrier \<L>)) \<oplus>\<^sub>\<I>
       (((\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<oplus>\<^sub>\<I> (\<I>_usr_rest1 \<oplus>\<^sub>\<I> \<I>_usr_rest2)) \<oplus>\<^sub>\<I> \<I>_usr_resta))
      \<A> (0 + (ddh.advantage \<G>
                (diffie_hellman.DH_adversary \<G> auth1_rest auth2_rest
                  (absorb
                    (absorb \<A>
                      (obsf_converter (1\<^sub>C |\<^sub>= wiring_c1r22_c1r22 (CNV otp.enc_callee ()) (CNV otp.dec_callee ()) |\<^sub>= 1\<^sub>C)))
                    (obsf_converter
                      (fused_wiring \<odot> (1\<^sub>C |\<^sub>\<propto> converter_of_resource (1\<^sub>C |\<^sub>= 1\<^sub>C \<rhd> dh.auth.resource auth_rest)))))) +
               0))"
  using assms apply -
  apply(rule constructive_security_obsf_composability)
   apply(rule otp.secure)
    apply(rule WT_intro, assumption+)
  unfolding otp.real_resource_def attach_c1f22_c1f22_def[abs_def] attach_compose
  apply(rule constructive_security_obsf_lifting_[where w_adv_real="1\<^sub>C" and w_adv_ideal_inv="1\<^sub>C"])
          apply(rule parallel_constructive_security_obsf_fuse)
           apply(fold carrier_\<G>_\<L>)[1]
           apply(rule dh.secure, assumption, assumption, rule constructive_security_obsf_trivial)
          defer
          defer
          defer
          apply(rule WT_intro)+
       apply(simp add: comp_converter_id_left)
       apply(rule parallel_converter2_id_id pfinite_intro wiring_intro)+
    apply(rule WT_intro|assumption)+
    apply simp
   apply(unfold wiring_c1r22_c1r22_def)
   apply(rule WT_intro)+
    apply(fold carrier_\<G>_\<L>)[1]
    apply(rule WT_intro)+

  apply(rule pfinite_intro)
   apply(rule pfinite_intro)
      apply(rule pfinite_intro)
       apply(rule pfinite_intro)
      apply(rule pfinite_intro)
     apply(unfold carrier_\<G>_\<L>)
     apply(rule pfinite_intro)
    apply(rule WT_intro)+
  apply(rule pfinite_intro)
  done

end

end