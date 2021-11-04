theory One_Time_Pad
  imports
    Sigma_Commit_Crypto.Xor
    "../Asymptotic_Security"
    "../Construction_Utility"
    "../Specifications/Key"
    "../Specifications/Channel"
begin

section \<open>One-time-pad construction\<close>

locale one_time_pad =
    key: ideal_key "carrier \<L>"  +
    auth: ideal_channel "id :: 'msg \<Rightarrow> 'msg" False +
    sec: ideal_channel "\<lambda>_ :: 'msg. carrier \<L>" False +
    boolean_algebra \<L>
  for 
    \<L> :: "('msg, 'more) boolean_algebra_scheme" (structure) +
  assumes
    nempty_carrier: "carrier \<L> \<noteq> {}" and
    finite_carrier: "finite (carrier \<L>)"
begin


subsection \<open>Defining user callees\<close>

definition enc_callee :: " unit \<Rightarrow> 'msg sec.iusr_alice 
  \<Rightarrow> (sec.ousr_alice \<times> unit, key.iusr_alice + 'msg sec.iusr_alice, 'msg key.ousr_alice + auth.ousr_alice) gpv"
  where
    "enc_callee \<equiv> stateless_callee (\<lambda>inp. case inp of sec.Inp_Send msg \<Rightarrow>
      if msg \<in> carrier \<L> then
        Pause 
          (Inl key.Inp_Alice) 
          (\<lambda>kout. case projl kout of key.Out_Alice key \<Rightarrow> 
            let cipher = key \<oplus> msg in
            Pause (Inr (auth.Inp_Send cipher)) (\<lambda>_. Done sec.Out_Send))
      else
        Fail)"

definition dec_callee :: " unit \<Rightarrow> sec.iusr_bob 
  \<Rightarrow> ('msg sec.ousr_bob \<times> unit, key.iusr_bob + auth.iusr_bob, 'msg key.ousr_bob + 'msg auth.ousr_bob) gpv"
  where
    "dec_callee \<equiv> stateless_callee (\<lambda>_.
      Pause 
        (Inr auth.Inp_Recv) 
        (\<lambda>cout. case cout of 
          Inr (auth.Out_Recv cipher) \<Rightarrow>
            Pause 
              (Inl key.Inp_Bob) 
              (\<lambda>kout. case projl kout of key.Out_Bob key \<Rightarrow>
                Done (sec.Out_Recv (key \<oplus> cipher)))
        | _ \<Rightarrow> Fail))"


subsection \<open>Defining adversary converter\<close>

type_synonym 'msg' astate = "'msg' option"

definition look_callee :: "'msg astate \<Rightarrow> sec.iadv_look 
  \<Rightarrow> ('msg sec.oadv_look \<times> 'msg astate, sec.iadv_look,  'msg set sec.oadv_look) gpv"
  where
    "look_callee \<equiv> \<lambda>state inp.   
      Pause 
        sec.Inp_Look
        (\<lambda>cout. case cout of
          sec.Out_Look msg_set \<Rightarrow> 
            (case state of
              None \<Rightarrow> do {
                msg \<leftarrow> lift_spmf (spmf_of_set (msg_set));
                Done (auth.Out_Look msg, Some msg)  }
            | Some msg \<Rightarrow> Done (auth.Out_Look msg, Some msg)))"

definition sim :: "
  (key.iadv + auth.iadv_drop + auth.iadv_look + 'msg auth.iadv_fedit,
    key.oadv + auth.oadv_drop + 'msg auth.oadv_look + auth.oadv_fedit,
    sec.iadv_drop + sec.iadv_look + 'msg sec.iadv_fedit,
    sec.oadv_drop + 'msg set sec.oadv_look + sec.oadv_fedit) converter"
  where
    "sim \<equiv> 
      let look_converter = converter_of_callee look_callee None in
      ldummy_converter (\<lambda>_. key.Out_Adversary) (1\<^sub>C |\<^sub>= look_converter |\<^sub>= 1\<^sub>C)"


subsection \<open>Defining event-translator\<close>

type_synonym estate = "bool \<times> (key.party + auth.party) set"

abbreviation einit :: estate
  where
    "einit \<equiv> (False, {})"

definition sec_party_of_key_party :: "key.party \<Rightarrow> sec.party" 
  where
    "sec_party_of_key_party \<equiv> key.case_party sec.Alice sec.Bob"

abbreviation etran_base_helper :: "estate \<Rightarrow> key.party + auth.party \<Rightarrow> sec.event list"
  where
    "etran_base_helper \<equiv> (\<lambda>(s_flg, s_kap) item. 
      let sp_of = case_sum sec_party_of_key_party id in
      let se_of = (\<lambda>chk out. if s_flg \<and> chk then [out] else []) in
      let chk_alice = Inl key.Alice \<in> s_kap \<and> Inr auth.Alice \<in> s_kap in
      let chk_bob = Inl key.Bob \<in> s_kap \<and> Inr auth.Bob \<in> s_kap in
      sec.case_party
        (se_of chk_alice (sec.Event_Shell sec.Alice))
        (se_of chk_bob (sec.Event_Shell sec.Bob))
        (sp_of item))"

abbreviation etran_base :: "(estate, key.party + auth.party, sec.event list) oracle'"
  where
    "etran_base \<equiv> (\<lambda>(s_flg, s_kap) item.  
      let s_kap' = insert item s_kap in
      let event = etran_base_helper (s_flg, s_kap') item in
      if item \<notin> s_kap then return_spmf (event, s_flg, s_kap') else return_pmf None)"

fun etran :: "(estate, key.event + auth.event, sec.event list) oracle'"
  where
    "etran state (Inl (key.Event_Shell party)) = etran_base state (Inl party)"
  | "etran (False, s_kap) (Inl key.Event_Kernel) = 
      (let check_alice = Inl key.Alice \<in> s_kap \<and> Inr auth.Alice \<in> s_kap in
      let check_bob = Inl key.Bob \<in> s_kap \<and> Inr auth.Bob \<in> s_kap in
      let e_alice = if check_alice then [sec.Event_Shell sec.Alice] else [] in
      let e_bob = if check_bob then [sec.Event_Shell sec.Bob] else [] in
      return_spmf (e_alice @ e_bob, True, s_kap))"
  | "etran state (Inr (auth.Event_Shell party)) = etran_base state (Inr party)"
  | "etran _ _ = return_pmf None"


subsubsection \<open>Basic lemmas for automated handling of @{term sec_party_of_key_party}\<close>

lemma sec_party_of_key_party_simps [simp]:
  "sec_party_of_key_party key.Alice = sec.Alice"
  "sec_party_of_key_party key.Bob = sec.Bob"
  by(simp_all add: sec_party_of_key_party_def)

lemma sec_party_of_key_party_eq_simps [simp]:
  "sec_party_of_key_party p = sec.Alice \<longleftrightarrow> p = key.Alice"
  "sec_party_of_key_party p = sec.Bob \<longleftrightarrow> p = key.Bob"
  by(simp_all add: sec_party_of_key_party_def split: key.party.split)

lemma key_case_party_collapse [simp]: "key.case_party x x p = x"
  by(simp split: key.party.split)

lemma sec_case_party_collapse [simp]: "sec.case_party x x p = x"
  by(simp split: sec.party.split)

lemma Alice_in_sec_party_of_key_party [simp]:
  "sec.Alice \<in> sec_party_of_key_party ` P \<longleftrightarrow> key.Alice \<in> P"
  by(auto simp add: sec_party_of_key_party_def split: key.party.splits)

lemma Bob_in_sec_party_of_key_party [simp]:
  "sec.Bob \<in> sec_party_of_key_party ` P \<longleftrightarrow> key.Bob \<in> P"
  by(auto simp add: sec_party_of_key_party_def split: key.party.splits)

lemma case_sec_party_of_key_party [simp]: "sec.case_party a b (sec_party_of_key_party x) = key.case_party a b x"
  by(simp add: sec_party_of_key_party_def split: sec.party.split key.party.split)


subsection \<open>Defining Ideal and Real constructions\<close>

context 
  fixes 
    key_rest :: "('key_s_rest, key.event, 'key_iadv_rest, 'key_iusr_rest, 'key_oadv_rest, 'key_ousr_rest) rest_wstate" and
    auth_rest :: "('auth_s_rest, auth.event, 'auth_iadv_rest, 'auth_iusr_rest, 'auth_oadv_rest, 'auth_ousr_rest) rest_wstate"
begin

definition ideal_rest 
  where
    "ideal_rest \<equiv> translate_rest einit etran (parallel_rest key_rest auth_rest)"

definition ideal_resource 
  where
    "ideal_resource \<equiv> (sim |\<^sub>= 1\<^sub>C) |\<^sub>= 1\<^sub>C |\<^sub>= 1\<^sub>C  \<rhd> (sec.resource ideal_rest)"

definition real_resource 
  where
    "real_resource \<equiv> attach_c1f22_c1f22 (CNV enc_callee ()) (CNV dec_callee ()) (key.resource key_rest) (auth.resource auth_rest)"


subsection \<open>Wiring and simplifying the Ideal construction\<close>

definition ideal_s_core' :: "((_ \<times> 'msg astate \<times> _) \<times> _) \<times> estate \<times> 'msg sec.state"
  where
    "ideal_s_core' \<equiv> ((((), None, ()), ()), (False, {}), sec.State_Void, {})"

definition ideal_s_rest' :: "_ \<times> 'key_s_rest \<times> 'auth_s_rest"
  where
    "ideal_s_rest' \<equiv> (((), ()), rinit key_rest, rinit auth_rest)"

primcorec ideal_core' :: "(((unit \<times> _ \<times> unit) \<times> unit) \<times>  _,  _, key.iadv + _, _, _, _) core"
  where
    "cpoke ideal_core' = (\<lambda>(s_advusr, s_event, s_core) event. do {
        (events, s_event') \<leftarrow> (etran s_event event);
        s_core' \<leftarrow> foldl_spmf sec.poke (return_spmf s_core) events;
        return_spmf (s_advusr, s_event', s_core')
    })"
  | "cfunc_adv ideal_core' = (\<lambda>((s_adv, s_usr), s_core) iadv.
      let handle_l = (\<lambda>_. Done (Inl key.Out_Adversary, s_adv)) in
      let handle_r = (\<lambda>qr. map_gpv (map_prod Inr id) id ((1\<^sub>I \<ddagger>\<^sub>I look_callee \<ddagger>\<^sub>I 1\<^sub>I) s_adv qr)) in
      map_spmf 
        (\<lambda>((oadv, s_adv'), s_core'). (oadv, (s_adv', s_usr), s_core'))
        (exec_gpv \<dagger>sec.iface_adv (case_sum handle_l handle_r iadv) s_core))"
  | "cfunc_usr ideal_core' = \<dagger>\<dagger>sec.iface_usr"

primcorec ideal_rest' :: "((unit \<times> unit) \<times> _, _, _, _, _, _, _) rest_scheme"
  where
    "rinit ideal_rest' = (((), ()), rinit key_rest, rinit auth_rest)"
  | "rfunc_adv ideal_rest' = \<dagger>(parallel_eoracle (rfunc_adv key_rest) (rfunc_adv auth_rest))"
  | "rfunc_usr ideal_rest' = \<dagger>(parallel_eoracle (rfunc_usr key_rest) (rfunc_usr auth_rest))"


subsubsection \<open>The ideal attachment lemma\<close>
  
lemma attach_ideal: "ideal_resource = RES (fused_resource.fuse ideal_core' ideal_rest') (ideal_s_core', ideal_s_rest')"
proof -

  have fact1: "ideal_rest' = attach_rest 1\<^sub>I 1\<^sub>I (Pair ((), ())) (parallel_rest key_rest auth_rest)"  (is "?L = ?R")
  proof -

    have "rinit ?L = rinit ?R"
      by simp

    moreover have "rfunc_adv ?L = rfunc_adv ?R"
      unfolding attach_rest_id_oracle_adv parallel_eoracle_def
      by (simp add: extend_state_oracle_def)

    moreover have "rfunc_usr ?L = rfunc_usr ?R"
      unfolding attach_rest_id_oracle_usr parallel_eoracle_def
      by (simp add: extend_state_oracle_def)

    ultimately show ?thesis
      by (coinduction) blast
  qed

  have fact2: "ideal_core' =
    (let handle_l = (\<lambda>s ql. Generative_Probabilistic_Value.Done (Inl key.Out_Adversary, s)) in
     let handle_r = (\<lambda>s qr. map_gpv (map_prod Inr id) id ((1\<^sub>I \<ddagger>\<^sub>I look_callee \<ddagger>\<^sub>I 1\<^sub>I) s qr)) in
     let tcore = translate_core etran sec.core in
    attach_core (\<lambda>s. case_sum (handle_l s) (handle_r s)) 1\<^sub>I tcore)" (is "?L = ?R")
  proof -

    have "cpoke ?L = cpoke ?R"
      by (simp add: split_def map_spmf_conv_bind_spmf)

    moreover have "cfunc_adv ?L = cfunc_adv ?R"
      unfolding attach_core_def
      by (simp add: split_def)

    moreover have "cfunc_usr ?L = cfunc_usr ?R"
      unfolding Let_def attach_core_id_oracle_usr
      by (clarsimp simp add: extend_state_oracle_def[symmetric])
    
    ultimately show ?thesis
      by (coinduction) blast
  qed

  show ?thesis
    unfolding ideal_resource_def sec.resource_def sim_def ideal_rest_def ideal_s_core'_def ideal_s_rest'_def
    apply(simp add: conv_callee_parallel_id_right[symmetric, where s'="()"])
    apply(simp add: conv_callee_parallel_id_left[symmetric, where s="()"])
    apply(simp add: ldummy_converter_of_callee)
    apply(subst fused_resource_move_translate[of _ einit etran])
    apply(simp add: resource_of_oracle_state_iso)
    apply(simp add: iso_swapar_def split_beta ideal_rest_def)
    apply(subst (1 2 3) converter_of_callee_id_oracle[symmetric, of "()"])
    apply(subst attach_parallel_fuse'[where f_init="Pair ((), ())"])
    apply(simp add: fact1[symmetric] fact2[symmetric, simplified Let_def])
    done  
qed

subsection \<open>Wiring and simplifying the Real construction\<close>

definition real_s_core' :: "_ \<times> 'msg key.state \<times> 'msg auth.state"
  where
    "real_s_core' \<equiv> (((), (), ()), (key.PState_Store, {}), (auth.State_Void, {}))"

definition real_s_rest'
  where
    "real_s_rest' \<equiv> ideal_s_rest'"

primcorec real_core' :: "((unit \<times> _) \<times> _, _, _, _, _, _) core"
  where
    "cpoke real_core' = (\<lambda>(s_advusr, s_core) event. 
      map_spmf (Pair s_advusr) (parallel_handler key.poke auth.poke s_core event))"
  | "cfunc_adv real_core' = \<dagger>(key.iface_adv \<ddagger>\<^sub>O auth.iface_adv)"
  | "cfunc_usr real_core' = (\<lambda>((s_adv, s_usr), s_core) iusr.
      let handle_req = lsumr \<circ> map_sum id (rsuml \<circ> map_sum swap_sum id \<circ> lsumr) \<circ> rsuml in
      let handle_ret = lsumr \<circ> (map_sum id (rsuml \<circ> (map_sum swap_sum id \<circ> lsumr)) \<circ> rsuml) in
      map_spmf 
        (\<lambda>((ousr, s_usr'), s_core'). (ousr, (s_adv, s_usr'), s_core'))
        (exec_gpv 
          (key.iface_usr \<ddagger>\<^sub>O auth.iface_usr)
          (map_gpv' id handle_req  handle_ret ((enc_callee \<ddagger>\<^sub>I dec_callee) s_usr iusr)) s_core))"

definition real_rest'
  where
    "real_rest' \<equiv> ideal_rest'"


subsubsection \<open>The real attachment lemma\<close>

private lemma WT_callee_real1: "((\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_full)) \<oplus>\<^sub>\<I> ((\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_full)) \<turnstile>c 
  (key.fuse key_rest \<ddagger>\<^sub>O auth.fuse auth_rest) s \<surd>"
  apply(rule WT_calleeI)
  apply(cases s)
  apply(case_tac call)
   apply(rename_tac [!] x)
   apply(case_tac [!] x)
     apply(rename_tac [!] y)
     apply(case_tac [!] y)
  by(auto simp add: fused_resource.fuse.simps)

private lemma WT_callee_real2: "(\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<oplus>\<^sub>\<I> (((\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_full)) \<oplus>\<^sub>\<I> \<I>_full) \<turnstile>c
  fused_resource.fuse (parallel_core key.core auth.core) (parallel_rest key_rest auth_rest) s \<surd>"
  apply(rule WT_calleeI)
  apply(cases s)
  apply(case_tac call)
   apply(rename_tac [!] x)
   apply(case_tac [!] x)
     apply(rename_tac [!] y)
     apply(case_tac [!] y)
         apply(rename_tac [5] z)
         apply(rename_tac [6] z)
         apply(case_tac [5] z)
          apply(case_tac [7] z)
  by(auto simp add: fused_resource.fuse.simps)


lemma attach_real: "real_resource = RES (fused_resource.fuse real_core' real_rest') (real_s_core', real_s_rest')"
proof -

  have fact1: "real_core' = attach_core 1\<^sub>I (attach_wiring_right parallel_wiring\<^sub>w (enc_callee \<ddagger>\<^sub>I dec_callee)) 
    (parallel_core key.core auth.core) " (is "?L = ?R")
  proof-

    have "cpoke ?L = cpoke ?R"
      by simp

    moreover have "cfunc_adv ?L = cfunc_adv ?R"
      unfolding attach_core_id_oracle_adv
      by (simp add: extend_state_oracle_def)

    moreover have "cfunc_usr ?L = cfunc_usr ?R"
      unfolding parallel_wiring\<^sub>w_def swap_lassocr\<^sub>w_def swap\<^sub>w_def lassocr\<^sub>w_def rassocl\<^sub>w_def
      by (simp add: attach_wiring_right_simps parallel2_wiring_simps comp_wiring_simps)

    ultimately show ?thesis
      by (coinduction) blast
  qed

  have fact2: "real_rest' = attach_rest 1\<^sub>I 1\<^sub>I (Pair ((), ())) (parallel_rest key_rest auth_rest) "  (is "?L = ?R")
  proof -
    have "rinit ?L = rinit ?R"
      unfolding real_rest'_def ideal_rest'_def 
      by simp

    moreover have "rfunc_adv ?L = rfunc_adv ?R"
      unfolding real_rest'_def ideal_rest'_def attach_rest_id_oracle_adv 
      by (simp add: extend_state_oracle_def)

    moreover have "rfunc_usr ?L = rfunc_usr ?R"
      unfolding real_rest'_def ideal_rest'_def attach_rest_id_oracle_usr
      by (simp add: extend_state_oracle_def)

    ultimately show ?thesis
      by (coinduction) blast
  qed

  show ?thesis
    unfolding real_resource_def attach_c1f22_c1f22_def wiring_c1r22_c1r22_def key.resource_def auth.resource_def
    apply(subst resource_of_parallel_oracle[symmetric])
    apply(subst attach_compose)
    apply(subst attach_wiring_resource_of_oracle)
       apply(rule wiring_intro)
      apply (rule WT_resource_of_oracle[OF WT_callee_real1])
     apply simp
    subgoal
      apply(subst parallel_oracle_fuse)
      apply(subst resource_of_oracle_state_iso)
       apply simp
      apply(simp add: parallel_state_iso_def)
      apply(subst conv_callee_parallel[symmetric])
      apply(subst eq_resource_on_UNIV_iff[symmetric])
      apply(rule eq_resource_on_trans)
       apply(rule eq_\<I>_attach_on')
         apply (rule WT_resource_of_oracle[OF WT_callee_real2])
        apply(rule parallel_converter2_eq_\<I>_cong)
         apply(rule eq_\<I>_converter_reflI)
         apply(rule WT_intro)+
        apply(rule parallel_converter2_eq_\<I>_cong)
         apply(rule comp_converter_of_callee_wiring)
          apply(rule wiring_intro)
         apply(subst conv_callee_parallel)
         apply(rule WT_intro)
          apply (rule WT_converter_of_callee[where \<I>=\<I>_full and \<I>'="\<I>_full \<oplus>\<^sub>\<I> \<I>_full"])
           apply (rule WT_gpv_\<I>_mono)
            apply (rule WT_gpv_full)
           apply (rule \<I>_full_le_plus_\<I>)
            apply(rule order_refl)
           apply(rule order_refl)
          apply (clarsimp simp add: enc_callee_def stateless_callee_def split!: sec.iusr_alice.splits key.ousr_alice.splits)
         apply (rule WT_converter_of_callee[where \<I>=\<I>_full and \<I>'="\<I>_full \<oplus>\<^sub>\<I> \<I>_full"])
          apply (rule WT_gpv_\<I>_mono)
           apply (rule WT_gpv_full)
          apply (rule \<I>_full_le_plus_\<I>)
           apply(rule order_refl)
          apply(rule order_refl)
         apply (clarsimp simp add: enc_callee_def stateless_callee_def split!: sec.iusr_alice.splits key.ousr_alice.splits)
        apply(subst id_converter_eq_self)
         apply(rule order_refl)
        apply simp
       apply simp
      apply(subst eq_resource_on_UNIV_iff)
      apply(subst (1 2 3) converter_of_callee_id_oracle[symmetric, of "()"])
      apply(subst attach_parallel_fuse')
      apply(simp add: fact1 fact2 real_s_core'_def real_s_rest'_def ideal_s_rest'_def)
    done
  done
qed


subsection \<open>Proving the trace-equivalence of simplified Ideal and Real constructions\<close>

context
begin


subsubsection \<open>Proving the trace-equivalence of cores\<close>

private abbreviation 
  "a_I \<equiv> \<lambda>(x, y). ((((), x, ()), ()), y)"

private abbreviation
  "a_R \<equiv> \<lambda>x. (((), (), ()), x)"

abbreviation
  "asm_act \<equiv> (\<lambda>flg pset_sec pset_key pset_auth pset_union.
     pset_union = pset_key <+> pset_auth \<and>
     (flg \<longrightarrow> pset_sec = sec_party_of_key_party ` pset_key \<inter> pset_auth))"

private inductive S :: "(((_ \<times> 'msg option \<times> _) \<times> _) \<times> estate \<times> 'msg sec.state) spmf 
  \<Rightarrow> (_ \<times> 'msg key.state \<times> 'msg auth.state) spmf \<Rightarrow> bool"
  where
\<comment> \<open>(Auth =a)@(Key =0)\<close>
    s_0_0: "S (return_spmf (a_I (None, (False, s_act_ka), sec.State_Void, s_act_s))) 
      (return_spmf (a_R ((key.PState_Store, s_act_k), auth.State_Void, s_act_a)))"
  if "asm_act False s_act_s s_act_k s_act_a s_act_ka" and "s_act_s = {}"
\<comment> \<open>(Auth =a)@(Key =1)\<close>
  | s_0_1: "S (return_spmf (a_I (None, (True, s_act_ka), sec.State_Void, s_act)))
      (map_spmf (\<lambda>key. a_R ((key.State_Store key, s_act_k), auth.State_Void, s_act_a)) (spmf_of_set (carrier \<L>)))"
  if "asm_act True s_act s_act_k s_act_a s_act_ka"
\<comment> \<open>../(Auth =a)@(Key =1) \# wl\<close>
  | s_1_1: "S (return_spmf (a_I (None, (True ,s_act_ka), sec.State_Store msg, s_act_s)))
      (map_spmf (\<lambda>key. a_R ((key.State_Store key, s_act_k), auth.State_Store (key \<oplus> msg), s_act_a)) (spmf_of_set (carrier \<L>)))"
  if "asm_act True s_act_s s_act_k s_act_a s_act_ka" and "key.Alice \<in> s_act_k" and "auth.Alice \<in> s_act_a" and "msg \<in> carrier \<L>"
  | s_2_1: "S (return_spmf (a_I (None, (True ,s_act_ka), sec.State_Collect msg, s_act_s)))
      (map_spmf (\<lambda>key. a_R ((key.State_Store key, s_act_k), auth.State_Collect (key \<oplus> msg), s_act_a)) (spmf_of_set (carrier \<L>)))"
  if "asm_act True s_act_s s_act_k s_act_a s_act_ka" and "key.Alice \<in> s_act_k" and "auth.Alice \<in> s_act_a" and "msg \<in> carrier \<L>"
  | s_3_1: "S (return_spmf (a_I (None, (True ,s_act_ka), sec.State_Collected, s_act_s)))
      (map_spmf (\<lambda>key. a_R ((key.State_Store key, s_act_k), auth.State_Collected, s_act_a)) (spmf_of_set (carrier \<L>)))"
  if "asm_act True s_act_s s_act_k s_act_a s_act_ka" and "s_act_k = {key.Alice, key.Bob}" and "s_act_a = {auth.Alice, auth.Bob}"
\<comment> \<open>../(Auth =a)@(Key =1) \# look\<close>
  | s_1'_1: "S (return_spmf (a_I (Some (key \<oplus> msg), (True ,s_act_ka), sec.State_Store msg, s_act_s)))
      (return_spmf (a_R ((key.State_Store key, s_act_k), auth.State_Store (key \<oplus> msg), s_act_a)))"
  if "asm_act True s_act_s s_act_k s_act_a s_act_ka" and "key.Alice \<in> s_act_k" and "auth.Alice \<in> s_act_a" and "msg \<in> carrier \<L>" and "key \<in> carrier \<L>"
  | s_2'_1: "S (return_spmf (a_I (Some (key \<oplus> msg), (True ,s_act_ka), sec.State_Collect msg, s_act_s)))
      (return_spmf (a_R ((key.State_Store key, s_act_k), auth.State_Collect (key \<oplus> msg), s_act_a)))"
  if "asm_act True s_act_s s_act_k s_act_a s_act_ka" and "key.Alice \<in> s_act_k" and "auth.Alice \<in> s_act_a" and "msg \<in> carrier \<L>" and "key \<in> carrier \<L>"
  | s_3'_1: "S (return_spmf (a_I (Some (key \<oplus> msg), (True ,s_act_ka), sec.State_Collected, s_act_s)))
      (return_spmf (a_R ((key.State_Store key, s_act_k), auth.State_Collected, s_act_a)))"
  if "asm_act True s_act_s s_act_k s_act_a s_act_ka" and "s_act_k = {key.Alice, key.Bob}" and "s_act_a = {auth.Alice, auth.Bob}" and "msg \<in> carrier \<L>" and "key \<in> carrier \<L>"

private lemma trace_eq_core: "trace_core_eq ideal_core' real_core' 
  UNIV (UNIV <+> UNIV <+> UNIV <+> (auth.Inp_Fedit ` carrier \<L>)) ((sec.Inp_Send ` carrier \<L>) <+> UNIV) 
  (return_spmf ideal_s_core') (return_spmf real_s_core')"
proof -

  have inj_xor: "\<lbrakk>msg \<in> carrier \<L> ; x \<in> carrier \<L>; y \<in> carrier \<L>; x \<oplus> msg = y \<oplus> msg\<rbrakk> \<Longrightarrow> x = y" for msg x y
    by (metis (no_types, hide_lams) local.xor_ac(2) local.xor_left_inverse)

  note [simp] = enc_callee_def dec_callee_def look_callee_def nempty_carrier finite_carrier
    exec_gpv_bind spmf.map_comp map_bind_spmf bind_map_spmf bind_spmf_const o_def Let_def
      
  show ?thesis
    apply (rule trace_core_eq_simI_upto[where S=S])
    subgoal Init_OK 
      by (simp add: ideal_s_core'_def real_s_core'_def S.simps)
    subgoal POut_OK for s_i s_r query
      apply (cases query)
      subgoal for e_key 
        apply (cases e_key)
        subgoal for e_shell by (erule S.cases) (auto simp add: map_spmf_conv_bind_spmf[symmetric] split: key.party.splits)
        subgoal e_kernel by (erule S.cases) (auto simp add: map_spmf_conv_bind_spmf[symmetric])
        done
      subgoal for e_auth
        apply (cases e_auth)
        subgoal for e_shell
          by (erule S.cases) (auto simp add: map_spmf_conv_bind_spmf[symmetric] split:auth.party.splits)
        done
      done
    subgoal PState_OK for s_i s_r query
      apply (cases query)
      subgoal for e_key
        apply (cases e_key)
        subgoal for e_shell by (erule S.cases) (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro!: trace_eq_simcl.base S.intros[simplified] split: key.party.splits)
        subgoal e_kernel by (erule S.cases) (auto simp add: map_spmf_conv_bind_spmf[symmetric] sec_party_of_key_party_def intro!: trace_eq_simcl.base S.intros[simplified] split: key.party.splits)    
        done
      subgoal for e_auth
        apply (cases e_auth)
        subgoal for e_shell by (erule S.cases) (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro!: trace_eq_simcl.base S.intros[simplified] split:auth.party.splits)
        done
      done
    subgoal AOut_OK for s_i s_r query
      apply (cases query)
      subgoal for q_key by (erule S.cases) simp_all 
      subgoal for q_auth
        apply (cases q_auth)
        subgoal for q_auth_drop by (erule S.cases) (simp_all add: id_oracle_def)
        subgoal for q_auth_lfe
          apply (cases q_auth_lfe)
          subgoal for q_auth_look
          proof (erule S.cases, goal_cases)
            case (3 s_act_s s_act_k s_act_a s_act_ka msg) \<comment> \<open>Corresponds to @{thm [source] s_1_1}\<close>
            then show ?case 
              apply(simp add: exec_gpv_extend_state_oracle exec_gpv_map_gpv_id exec_gpv_plus_oracle_right exec_gpv_plus_oracle_left)
              apply (subst one_time_pad[symmetric, of "msg"])
               apply (simp_all add: xor_comm)
              apply (rule bind_spmf_cong[OF HOL.refl])
              by (simp add: xor_comm)
          qed simp_all
          subgoal for q_auth_fedit  by (erule S.cases) (auto simp add: id_oracle_def split:auth.iadv_fedit.split)
          done
        done
      done
    subgoal AState_OK for s_i s_r query
      apply (cases query)
      subgoal for q_key by (erule S.cases) (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro!: trace_eq_simcl.base S.intros[simplified])
      subgoal for q_auth
        apply (cases q_auth)
        subgoal for q_auth_drop by (erule S.cases) (auto simp add: id_oracle_def)
        subgoal for q_auth_lfe
          apply (cases q_auth_lfe)
          subgoal for q_auth_look
          proof (erule S.cases, goal_cases)
            case (3 s_act_s s_act_k s_act_a s_act_ka msg) \<comment> \<open>Corresponds to @{thm [source] s_1_1}\<close>
            then show ?case 
              apply(simp add: exec_gpv_extend_state_oracle exec_gpv_map_gpv_id exec_gpv_plus_oracle_right exec_gpv_plus_oracle_left)
              apply (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric])
              apply (subst (1 2) cond_spmf_fst_map_Pair1; clarsimp simp add: set_spmf_of_set inj_on_def intro: inj_xor)
               apply (rule inj_xor, simp_all)             
              apply(subst (1 2 3) inv_into_f_f)
              by (auto simp add: S.simps inj_on_def intro: inj_xor)
          qed (auto intro!: trace_eq_simcl.base S.intros[simplified])
          subgoal for q_auth_fedit by (erule S.cases) (auto simp add: map_spmf_conv_bind_spmf[symmetric] id_oracle_def intro!: trace_eq_simcl.base S.intros[simplified])
          done
        done
      done
    subgoal UOut_OK for s_i s_r query
      apply (cases query)
      subgoal for q_alice
      proof (erule S.cases, goal_cases)
        case (2 s_act_s s_act_k s_act_a s_act_ka) \<comment> \<open>Corresponds to @{thm [source] s_0_1}\<close>
        then show ?case 
          apply (cases "auth.Alice \<in> s_act_a"; cases "key.Alice \<in> s_act_k")
             apply (simp_all add: stateless_callee_def split_def split!: auth.iusr_alice.split)
          done 
      qed (simp_all add: stateless_callee_def split: auth.iusr_alice.split)
      subgoal for q_bob
      proof (erule S.cases, goal_cases)
        case (4 s_act_s s_act_k s_act_a s_act_ka msg) \<comment> \<open>Corresponds to @{thm [source] s_2_1}\<close>
        then show ?case 
          apply (cases "sec.Bob \<in> s_act_s")
          subgoal
            apply (clarsimp simp add: stateless_callee_def)
            apply (simp add: spmf_rel_eq[symmetric])
            apply (rule rel_spmf_bindI2)
            by simp_all
          subgoal by (cases "sec.Bob \<in> s_act_a") (clarsimp simp add: stateless_callee_def)+
          done
      qed (simp_all add: stateless_callee_def)
      done
    subgoal UState_OK for s_i s_r query
      apply (cases query)
      subgoal for q_alice
      proof (erule S.cases, goal_cases)
        case (2 s_act s_act_k s_act_a s_act_ka) \<comment> \<open>Corresponds to @{thm [source] s_0_1}\<close>
        then show ?case 
          apply (cases "auth.Alice \<in> s_act_a"; cases "key.Alice \<in> s_act_k")
          subgoal
            apply (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric] stateless_callee_def split_def split!: auth.iusr_alice.split if_splits)
            apply(rule trace_eq_simcl.base)
            apply (rule S.intros(3)[simplified])
            by simp_all
          by (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric] stateless_callee_def split_def split: auth.iusr_alice.split)+
      qed (auto simp add: stateless_callee_def split: auth.iusr_alice.split_asm)
      subgoal for q_bob
      proof (erule S.cases, goal_cases)
        case (4 s_act_s s_act_k s_act_a s_act_ka msg) \<comment> \<open>Corresponds to @{thm [source] s_2_1}\<close>
        then show ?case 
          apply (cases "sec.Bob \<in> s_act_s")
          subgoal 
            apply (clarsimp simp add: stateless_callee_def map_spmf_conv_bind_spmf[symmetric])
            apply (subst map_spmf_of_set_inj_on)
             apply (simp_all add: inj_on_def)
            apply (subst map_spmf_of_set_inj_on[symmetric])
             apply (simp add: inj_on_def)
            apply clarsimp
            apply(rule trace_eq_simcl.base)
            apply (rule S.intros(5)[simplified])
              apply (simp_all split: sec.party.splits )
            by auto
          subgoal by (clarsimp simp add: stateless_callee_def split: if_splits)
          done
      next
        case (7 s_act_s s_act_k s_act_a s_act_ka msg key) \<comment> \<open>Corresponds to @{thm [source] s_2'_1}\<close>
        then show ?case 
          apply (cases "sec.Bob \<in> s_act_s")
          subgoal 
            apply (clarsimp simp add: stateless_callee_def map_spmf_conv_bind_spmf[symmetric])
            apply (rule S.intros(8)[simplified])
                apply simp_all
            by auto
          subgoal by (clarsimp simp add: stateless_callee_def split: if_splits)
          done
      qed (auto simp add: stateless_callee_def split: auth.iusr_alice.split_asm)
      done
    done
qed


subsubsection \<open>Proving the trace equivalence of fused cores and rests\<close>

private definition \<I>_adv_core :: "(key.iadv + 'msg auth.iadv, key.oadv + 'msg auth.oadv) \<I>"
  where "\<I>_adv_core \<equiv> \<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_uniform (sec.Inp_Fedit ` (carrier \<L>)) UNIV))"

private definition \<I>_usr_core :: "('msg sec.iusr, 'msg sec.ousr) \<I>"
  where "\<I>_usr_core \<equiv> \<I>_uniform (sec.Inp_Send ` (carrier \<L>)) UNIV \<oplus>\<^sub>\<I> \<I>_uniform UNIV (sec.Out_Recv ` carrier \<L>)"

private definition invar_ideal' :: "((_ \<times> 'msg astate \<times> _) \<times> _) \<times> estate \<times> 'msg sec.state \<Rightarrow> bool"
  where "invar_ideal' = pred_prod (pred_prod (pred_prod (\<lambda>_. True) (pred_prod (pred_option (\<lambda>x. x \<in> carrier \<L>)) (\<lambda>_. True))) (\<lambda>_. True)) (pred_prod (\<lambda>_. True) (pred_prod (sec.pred_s_kernel (\<lambda>x. x \<in> carrier \<L>)) (\<lambda>_. True)))"

private definition invar_real' :: "_ \<times> ('msg key.s_kernel \<times> _) \<times> 'msg sec.s_kernel \<times> _ \<Rightarrow> bool"
  where "invar_real' = pred_prod (\<lambda>_. True) (pred_prod (pred_prod (key.pred_s_kernel (\<lambda>x. x \<in> carrier \<L>)) (\<lambda>_. True)) (pred_prod (sec.pred_s_kernel (\<lambda>x. x \<in> carrier \<L>)) (\<lambda>_. True)))"

lemma invar_ideal_s_core' [simp]: "invar_ideal' ideal_s_core'"
  by(simp add: invar_ideal'_def ideal_s_core'_def)

lemma invar_real_s_core' [simp]: "invar_real' real_s_core'"
  by(simp add: invar_real'_def real_s_core'_def)

lemma WT_ideal_core' [WT_intro]: "WT_core \<I>_adv_core \<I>_usr_core invar_ideal' ideal_core'"
  apply(rule WT_core.intros)
  apply                
    (auto split!: sum.splits option.splits if_split_asm simp add: \<I>_adv_core_def \<I>_usr_core_def exec_gpv_map_gpv_id exec_gpv_extend_state_oracle exec_gpv_plus_oracle_left exec_gpv_plus_oracle_right invar_ideal'_def sec.in_set_spmf_iface_drop sec.in_set_spmf_iface_look sec.in_set_spmf_iface_fedit sec.in_set_spmf_iface_alice sec.in_set_spmf_iface_bob id_oracle_def look_callee_def exec_gpv_bind set_spmf_of_set sec.poke_alt_def foldl_spmf_pair_right)
  done

lemma WT_ideal_rest' [WT_intro]:
  assumes "WT_rest \<I>_adv_restk \<I>_usr_restk I_key_rest key_rest"
    and "WT_rest \<I>_adv_resta \<I>_usr_resta I_auth_rest auth_rest"
  shows "WT_rest (\<I>_adv_restk \<oplus>\<^sub>\<I> \<I>_adv_resta) (\<I>_usr_restk \<oplus>\<^sub>\<I> \<I>_usr_resta) (\<lambda>(_, s_rest). pred_prod I_key_rest I_auth_rest s_rest) ideal_rest'"
  by(rule WT_rest.intros)(fastforce simp add: fused_resource.fuse.simps parallel_eoracle_def dest: WT_restD_rfunc_adv[OF assms(1)] WT_restD_rfunc_adv[OF assms(2)] WT_restD_rfunc_usr[OF assms(1)] WT_restD_rfunc_usr[OF assms(2)] simp add: assms[THEN WT_restD_rinit])+


lemma WT_real_core' [WT_intro]: "WT_core \<I>_adv_core \<I>_usr_core invar_real' real_core'"
  apply(rule WT_core.intros)
   apply(auto simp add: \<I>_adv_core_def \<I>_usr_core_def enc_callee_def dec_callee_def
        stateless_callee_def Let_def exec_gpv_extend_state_oracle exec_gpv_map_gpv' exec_gpv_plus_oracle_left exec_gpv_plus_oracle_right
        invar_real'_def in_set_spmf_parallel_handler key.in_set_spmf_poke sec.poke_alt_def auth.in_set_spmf_iface_look auth.in_set_spmf_iface_fedit
        sec.in_set_spmf_iface_alice sec.in_set_spmf_iface_bob
        split!: key.ousr_alice.splits key.ousr_bob.splits auth.ousr_alice.splits auth.ousr_bob.splits sum.splits if_split_asm)
    done

private lemma trace_eq_sec: 
    fixes \<I>_adv_restk \<I>_adv_resta \<I>_usr_restk \<I>_usr_resta 
  defines "outs_adv \<equiv> (UNIV <+> UNIV <+> UNIV <+> sec.Inp_Fedit ` carrier \<L>) <+> outs_\<I> (\<I>_adv_restk \<oplus>\<^sub>\<I> \<I>_adv_resta)"
      and "outs_usr \<equiv> (sec.Inp_Send ` carrier \<L> <+> UNIV) <+> outs_\<I> (\<I>_usr_restk \<oplus>\<^sub>\<I> \<I>_usr_resta)"
  assumes WT_key [WT_intro]: "WT_rest \<I>_adv_restk \<I>_usr_restk I_key_rest key_rest" 
      and WT_auth [WT_intro]: "WT_rest \<I>_adv_resta \<I>_usr_resta I_auth_rest auth_rest"
    shows "(outs_adv <+> outs_usr) \<turnstile>\<^sub>C fused_resource.fuse ideal_core' ideal_rest' ((ideal_s_core', ideal_s_rest')) \<approx> 
      fused_resource.fuse real_core' real_rest' ((real_s_core', real_s_rest'))"
proof -
  define e\<I>_adv_rest :: "(_, _ \<times> (key.event + auth.event) list) \<I>"
    where "e\<I>_adv_rest \<equiv> map_\<I> id (case_sum (map_prod Inl (map Inl)) (map_prod Inr (map Inr))) (e\<I> \<I>_adv_restk \<oplus>\<^sub>\<I> e\<I> \<I>_adv_resta)"
  define e\<I>_usr_rest :: "(_, _ \<times> (key.event + auth.event) list) \<I>"
    where "e\<I>_usr_rest \<equiv> map_\<I> id (case_sum (map_prod Inl (map Inl)) (map_prod Inr (map Inr))) (e\<I> \<I>_usr_restk \<oplus>\<^sub>\<I> e\<I> \<I>_usr_resta)"

  note I_defs = \<I>_adv_core_def \<I>_usr_core_def
  note eI_defs = e\<I>_adv_rest_def e\<I>_usr_rest_def 

  have fact1[unfolded outs_plus_\<I>]: 
    "trace_rest_eq ideal_rest' ideal_rest' (outs_\<I> (\<I>_adv_restk \<oplus>\<^sub>\<I> \<I>_adv_resta)) (outs_\<I> (\<I>_usr_restk \<oplus>\<^sub>\<I> \<I>_usr_resta)) s s" for s
    apply(rule rel_rest'_into_trace_rest_eq[where S="(=)" and M="(=)", unfolded eq_onp_def], simp_all)
    apply(fold relator_eq)
    apply(rule rel_rest'_mono[THEN predicate2D, rotated -1, OF HOL.refl[of ideal_rest', folded relator_eq]])
    by auto

  have fact2 [unfolded eI_defs]: "callee_invariant_on (callee_of_rest ideal_rest') (\<lambda>(_, s_rest). pred_prod I_key_rest I_auth_rest s_rest) (e\<I>_adv_rest \<oplus>\<^sub>\<I> e\<I>_usr_rest)"
    apply unfold_locales
    subgoal for s x y s'
      apply(cases "(snd s, x)" rule: parallel_oracle.cases)
       apply(auto 4 3 simp add: parallel_eoracle_def eI_defs split!: sum.splits dest: WT_restD(1,2)[OF WT_key] WT_restD(1,2)[OF WT_auth])
      done
    subgoal for s
      apply(fastforce intro!: WT_calleeI simp add: parallel_eoracle_def eI_defs image_image dest: WT_restD(1,2)[OF WT_key] WT_restD(1,2)[OF WT_auth] intro: rev_image_eqI)
      done
    done

  have fact3[unfolded I_defs]: "callee_invariant_on (callee_of_core ideal_core') invar_ideal' (\<I>_full \<oplus>\<^sub>\<I> (\<I>_adv_core \<oplus>\<^sub>\<I> \<I>_usr_core))"
    by(rule WT_intro)+

  have fact4[unfolded I_defs]: "callee_invariant_on (callee_of_core real_core') invar_real' (\<I>_full \<oplus>\<^sub>\<I> (\<I>_adv_core \<oplus>\<^sub>\<I> \<I>_usr_core))"
    by(rule WT_intro)+

  note nempty_carrier[simp]
  show ?thesis using WT_key[THEN WT_restD_rinit] WT_auth[THEN WT_restD_rinit]
    apply (simp add: real_rest'_def real_s_rest'_def assms(1, 2))
    thm fuse_trace_eq[where \<I>E=\<I>_full and \<I>CA=\<I>_adv_core and \<I>CU=\<I>_usr_core and \<I>RA=e\<I>_adv_rest and \<I>RU=e\<I>_usr_rest,unfolded eI_defs \<I>_adv_core_def \<I>_usr_core_def,simplified]
    apply (rule fuse_trace_eq[where \<I>E=\<I>_full and \<I>CA=\<I>_adv_core and \<I>CU=\<I>_usr_core and \<I>RA=e\<I>_adv_rest and \<I>RU=e\<I>_usr_rest
      and ?IR1.0 = "\<lambda>(_, s_rest). pred_prod I_key_rest I_auth_rest s_rest"
      and ?IR2.0 = "\<lambda>(_, s_rest). pred_prod I_key_rest I_auth_rest s_rest"
      and ?IC1.0 = invar_ideal' and ?IC2.0=invar_real',
      unfolded eI_defs \<I>_adv_core_def \<I>_usr_core_def, simplified])
    by (simp_all add: trace_eq_core fact1 fact2 fact3 fact4 ideal_s_rest'_def)
qed


subsubsection \<open>Simplifying the final resource by moving the interfaces from core to rest\<close>


lemma connect[unfolded \<I>_adv_core_def \<I>_usr_core_def]:
    fixes \<I>_adv_restk \<I>_adv_resta \<I>_usr_restk \<I>_usr_resta 
  defines "\<I> \<equiv> (\<I>_adv_core \<oplus>\<^sub>\<I> (\<I>_adv_restk \<oplus>\<^sub>\<I> \<I>_adv_resta)) \<oplus>\<^sub>\<I> (\<I>_usr_core \<oplus>\<^sub>\<I> (\<I>_usr_restk \<oplus>\<^sub>\<I> \<I>_usr_resta))"
  assumes [WT_intro]: "WT_rest \<I>_adv_restk \<I>_usr_restk I_key_rest key_rest" 
      and [WT_intro]: "WT_rest \<I>_adv_resta \<I>_usr_resta I_auth_rest auth_rest"
      and "exception_\<I> \<I> \<turnstile>g D \<surd>"
    shows "connect D (obsf_resource ideal_resource) = connect D (obsf_resource real_resource)"
proof -
  note I_defs = \<I>_adv_core_def \<I>_usr_core_def

  have fact1: "\<I> \<turnstile>res RES (fused_resource.fuse ideal_core' ideal_rest') s \<surd>" 
    if "pred_prod I_key_rest I_auth_rest (snd (snd s))" "invar_ideal' (fst s)"
    for s
    unfolding assms(1)
    apply(rule callee_invariant_on.WT_resource_of_oracle[where I="pred_prod invar_ideal' (\<lambda>(_, s_rest). pred_prod I_key_rest I_auth_rest s_rest)"])
    subgoal by(rule fused_resource.callee_invariant_on_fuse)(rule WT_intro)+
    subgoal using that by(cases s)(simp)
    done

  have fact2: "\<I> \<turnstile>res RES (fused_resource.fuse real_core' real_rest') s \<surd>" 
    if "pred_prod I_key_rest I_auth_rest (snd (snd s))" "invar_real' (fst s)"
    for s
    unfolding real_rest'_def assms(1)
    apply(rule callee_invariant_on.WT_resource_of_oracle[where I="pred_prod invar_real' (\<lambda>(_, s_rest). pred_prod I_key_rest I_auth_rest s_rest)"])
    subgoal by(rule fused_resource.callee_invariant_on_fuse)(rule WT_intro)+
    subgoal using that by(cases s)(simp)
    done

  show ?thesis
    unfolding attach_ideal attach_real
    apply (rule connect_cong_trace[where \<I>="exception_\<I> \<I>"])
    apply (rule trace_eq_obsf_resourceI, subst trace_eq'_resource_of_oracle)
    apply (rule trace_eq_sec[OF assms(2) assms(3)])
    subgoal by (rule assms(4))
    subgoal using WT_gpv_outs_gpv[OF assms(4)] by(simp add: I_defs assms(1) nempty_carrier)
    subgoal using assms(2,3)[THEN WT_restD_rinit] by (intro WT_obsf_resource)(rule fact1; simp add: ideal_s_rest'_def)
    subgoal using assms(2,3)[THEN WT_restD_rinit] by (intro WT_obsf_resource)(rule fact2; simp add: real_s_rest'_def ideal_s_rest'_def)
    done
qed

end

end


end


subsection \<open>Concrete security\<close>

context one_time_pad begin

lemma WT_enc_callee [WT_intro]:
  "\<I>_uniform (sec.Inp_Send ` carrier \<L>) UNIV, \<I>_uniform UNIV (key.Out_Alice ` carrier \<L>) \<oplus>\<^sub>\<I>  \<I>_uniform (sec.Inp_Send ` carrier \<L>) UNIV \<turnstile>\<^sub>C CNV enc_callee () \<surd>"
  by (rule WT_converter_of_callee) (auto 4 3 simp add: enc_callee_def stateless_callee_def image_def split!: key.ousr_alice.split)

lemma WT_dec_callee [WT_intro]:
  "\<I>_uniform UNIV (sec.Out_Recv ` carrier \<L>), \<I>_uniform UNIV (key.Out_Bob ` carrier \<L>) \<oplus>\<^sub>\<I> \<I>_uniform UNIV (sec.Out_Recv ` carrier \<L>) \<turnstile>\<^sub>C CNV dec_callee () \<surd>"
  by(rule WT_converter_of_callee)(auto simp add: dec_callee_def stateless_callee_def split!: sec.ousr_bob.splits)

lemma pfinite_enc_callee [pfinite_intro]: 
   "pfinite_converter (\<I>_uniform (sec.Inp_Send ` carrier \<L>) UNIV) (\<I>_uniform UNIV (key.Out_Alice ` carrier \<L>) \<oplus>\<^sub>\<I> \<I>_uniform (sec.Inp_Send ` carrier \<L>) UNIV) (CNV enc_callee ())"
  apply(rule raw_converter_invariant.pfinite_converter_of_callee[where I="\<lambda>_. True"])
  subgoal by unfold_locales(auto simp add: enc_callee_def stateless_callee_def)
  subgoal by(auto simp add: enc_callee_def stateless_callee_def)
  subgoal by simp
  done

lemma pfinite_dec_callee [pfinite_intro]:
  "pfinite_converter (\<I>_uniform UNIV (sec.Out_Recv ` carrier \<L>)) (\<I>_uniform UNIV (key.Out_Bob ` carrier \<L>) \<oplus>\<^sub>\<I> \<I>_uniform UNIV (sec.Out_Recv ` carrier \<L>)) (CNV dec_callee ())"
  apply(rule raw_converter_invariant.pfinite_converter_of_callee[where I="\<lambda>_. True"])
  subgoal by unfold_locales(auto simp add: dec_callee_def stateless_callee_def)
  subgoal by(auto simp add: dec_callee_def stateless_callee_def)
  subgoal by simp
  done

context 
  fixes 
    key_rest :: "('key_s_rest, key.event, 'key_iadv_rest, 'key_iusr_rest, 'key_oadv_rest, 'key_ousr_rest) rest_wstate" and
    auth_rest :: "('auth_s_rest, auth.event, 'auth_iadv_rest, 'auth_iusr_rest, 'auth_oadv_rest, 'auth_ousr_rest) rest_wstate" and
    \<I>_adv_restk and \<I>_adv_resta and \<I>_usr_restk and \<I>_usr_resta and I_key_rest and I_auth_rest
  assumes 
    WT_key_rest [WT_intro]: "WT_rest \<I>_adv_restk \<I>_usr_restk I_key_rest key_rest" and 
    WT_auth_rest [WT_intro]: "WT_rest \<I>_adv_resta \<I>_usr_resta I_auth_rest auth_rest"
begin

theorem secure:
  defines "\<I>_real \<equiv> ((\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_uniform (sec.Inp_Fedit ` (carrier \<L>)) UNIV))) \<oplus>\<^sub>\<I> (\<I>_adv_restk \<oplus>\<^sub>\<I> \<I>_adv_resta))" 
      and "\<I>_common_core \<equiv> \<I>_uniform (sec.Inp_Send ` (carrier \<L>)) UNIV \<oplus>\<^sub>\<I> \<I>_uniform UNIV (sec.Out_Recv ` carrier \<L>)"
      and "\<I>_common_rest \<equiv> \<I>_usr_restk \<oplus>\<^sub>\<I> \<I>_usr_resta"
      and "\<I>_ideal \<equiv> (\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_uniform (sec.Inp_Fedit ` (carrier \<L>)) UNIV)) \<oplus>\<^sub>\<I> (\<I>_adv_restk \<oplus>\<^sub>\<I> \<I>_adv_resta)" 
    shows "constructive_security_obsf (real_resource TYPE(_) TYPE(_) key_rest auth_rest) (sec.resource (ideal_rest key_rest auth_rest)) (sim |\<^sub>= 1\<^sub>C) \<I>_real \<I>_ideal (\<I>_common_core \<oplus>\<^sub>\<I> \<I>_common_rest) \<A> 0" 
proof
  let ?\<I>_common = "\<I>_common_core \<oplus>\<^sub>\<I> \<I>_common_rest"
  show "\<I>_real \<oplus>\<^sub>\<I> ?\<I>_common \<turnstile>res real_resource TYPE(_) TYPE(_) key_rest auth_rest \<surd>"
    unfolding \<I>_real_def \<I>_common_core_def \<I>_common_rest_def real_resource_def attach_c1f22_c1f22_def wiring_c1r22_c1r22_def fused_wiring_def
    by(rule WT_intro | simp )+

  show [WT_intro]: "\<I>_ideal \<oplus>\<^sub>\<I> ?\<I>_common \<turnstile>res sec.resource (ideal_rest key_rest auth_rest) \<surd>"
    unfolding \<I>_common_core_def \<I>_common_rest_def \<I>_ideal_def ideal_rest_def
    by(rule WT_intro)+ simp

  show [WT_intro]: "\<I>_real, \<I>_ideal \<turnstile>\<^sub>C sim |\<^sub>= 1\<^sub>C \<surd>" 
    unfolding \<I>_real_def \<I>_ideal_def
    apply(rule WT_intro)+
    subgoal
      unfolding sim_def Let_def look_callee_def
      apply (fold conv_callee_parallel_id_right[where s'="()"])
      apply (fold conv_callee_parallel_id_left[where s="()"])
      apply (subst ldummy_converter_of_callee)
      apply (rule WT_converter_of_callee)
       by (auto simp add: id_oracle_def map_gpv_conv_bind[symmetric] map_lift_spmf
          split: auth.oadv_look.split option.split )
    by (rule WT_intro)

  show "pfinite_converter \<I>_real \<I>_ideal (sim |\<^sub>= 1\<^sub>C)"
    unfolding \<I>_real_def \<I>_ideal_def
    apply(rule pfinite_intro)+
    subgoal 
      unfolding sim_def Let_def look_callee_def
      apply (fold conv_callee_parallel_id_right[where s'="()"])
      apply (fold conv_callee_parallel_id_left[where s="()"])
      apply (subst ldummy_converter_of_callee)
      apply(rule raw_converter_invariant.pfinite_converter_of_callee[where I="\<lambda>_. True"])
      subgoal 
        by unfold_locales (auto split!: sum.split sec.oadv_look.split option.split 
            simp add: left_gpv_map id_oracle_def intro!: WT_intro WT_gpv_right_gpv WT_gpv_left_gpv)
      by (auto split!: sum.splits sec.oadv_look.splits option.splits)
    by (rule pfinite_intro)

  assume WT [WT_intro]: "exception_\<I> (\<I>_real \<oplus>\<^sub>\<I> ?\<I>_common) \<turnstile>g \<A> \<surd>"
  show "advantage \<A> (obsf_resource ((sim |\<^sub>= 1\<^sub>C) |\<^sub>= (1\<^sub>C |\<^sub>= 1\<^sub>C) \<rhd> sec.resource (ideal_rest key_rest auth_rest)))
    (obsf_resource (real_resource TYPE(_) TYPE(_) key_rest auth_rest)) \<le> 0"
    using connect[OF WT_key_rest, OF WT_auth_rest, OF WT[unfolded assms(1, 2, 3)]]
    unfolding advantage_def by (simp add: ideal_resource_def)
qed simp

end

end


subsection \<open>Asymptotic security\<close>

locale one_time_pad' =
  fixes \<L> :: "security \<Rightarrow> ('msg, 'more) boolean_algebra_scheme"
  assumes one_time_pad [locale_witness]: "\<And>\<eta>. one_time_pad (\<L> \<eta>)"
begin

sublocale one_time_pad "\<L> \<eta>" for \<eta> ..

definition real_resource' where "real_resource' rest1 rest2 \<eta> = real_resource TYPE(_) TYPE(_) \<eta> (rest1 \<eta>) (rest2 \<eta>)"
definition ideal_resource' where "ideal_resource' rest1 rest2 \<eta> = sec.resource \<eta> (ideal_rest (rest1 \<eta>) (rest2 \<eta>))"
definition sim' where "sim' \<eta> = (sim |\<^sub>= 1\<^sub>C)"

context 
  fixes 
    key_rest :: "nat \<Rightarrow> ('key_s_rest, key.event, 'key_iadv_rest, 'key_iusr_rest, 'key_oadv_rest, 'key_ousr_rest) rest_wstate" and
    auth_rest :: "nat \<Rightarrow> ('auth_s_rest, auth.event, 'auth_iadv_rest, 'auth_iusr_rest, 'auth_oadv_rest, 'auth_ousr_rest) rest_wstate" and
    \<I>_adv_restk and \<I>_adv_resta and \<I>_usr_restk and \<I>_usr_resta and I_key_rest and I_auth_rest
  assumes 
    WT_key_res: "\<And>\<eta>. WT_rest (\<I>_adv_restk \<eta>) (\<I>_usr_restk \<eta>) (I_key_rest \<eta>) (key_rest \<eta>)" and 
    WT_auth_rest: "\<And>\<eta>. WT_rest (\<I>_adv_resta \<eta>) (\<I>_usr_resta \<eta>) (I_auth_rest \<eta>) (auth_rest \<eta>)"
begin

theorem secure':
  defines "\<I>_real \<equiv> \<lambda>\<eta>. ((\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_uniform (sec.Inp_Fedit ` (carrier (\<L> \<eta>))) UNIV))) \<oplus>\<^sub>\<I> (\<I>_adv_restk \<eta> \<oplus>\<^sub>\<I> \<I>_adv_resta \<eta>))"
      and "\<I>_common \<equiv> \<lambda>\<eta>. ((\<I>_uniform (sec.Inp_Send ` (carrier (\<L> \<eta>))) UNIV \<oplus>\<^sub>\<I> \<I>_uniform UNIV (sec.Out_Recv ` carrier (\<L> \<eta>))) \<oplus>\<^sub>\<I> (\<I>_usr_restk \<eta> \<oplus>\<^sub>\<I> \<I>_usr_resta \<eta>))"
      and "\<I>_ideal \<equiv> \<lambda>\<eta>. (\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_uniform (sec.Inp_Fedit ` (carrier (\<L> \<eta>))) UNIV)) \<oplus>\<^sub>\<I> (\<I>_adv_restk \<eta> \<oplus>\<^sub>\<I> \<I>_adv_resta \<eta>)" 
    shows "constructive_security_obsf' (real_resource' key_rest auth_rest) (ideal_resource' key_rest auth_rest) sim' \<I>_real \<I>_ideal \<I>_common \<A>"
proof(rule constructive_security_obsf'I)
  show "constructive_security_obsf (real_resource' key_rest auth_rest \<eta>) (ideal_resource' key_rest auth_rest \<eta>)
          (sim' \<eta>) (\<I>_real \<eta>) (\<I>_ideal \<eta>) (\<I>_common \<eta>) (\<A> \<eta>) 0" for \<eta>
    unfolding real_resource'_def ideal_resource'_def sim'_def \<I>_real_def \<I>_common_def \<I>_ideal_def
    by(rule secure)(rule WT_key_res WT_auth_rest)+
qed simp

end


end

end
