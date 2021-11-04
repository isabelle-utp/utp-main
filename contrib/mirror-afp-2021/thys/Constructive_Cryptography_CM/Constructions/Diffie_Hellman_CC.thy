theory Diffie_Hellman_CC
  imports
    Game_Based_Crypto.Diffie_Hellman
    "../Asymptotic_Security"
    "../Construction_Utility"
    "../Specifications/Key" 
    "../Specifications/Channel"
begin

hide_const (open) Resumption.Pause Monomorphic_Monad.Pause Monomorphic_Monad.Done

no_notation Sublist.parallel (infixl "\<parallel>" 50)
no_notation plus_oracle (infix "\<oplus>\<^sub>O" 500)


section \<open>Diffie-Hellman construction\<close>

locale diffie_hellman =
    auth: ideal_channel "id :: 'grp \<Rightarrow> 'grp" False +
    key: ideal_key "carrier \<G>" +
    cyclic_group \<G>
  for
    \<G> :: "'grp cyclic_group" (structure)
begin


subsection \<open>Defining user callees\<close>

datatype 'grp' cstate = CState_Void | CState_Half nat | CState_Full "nat \<times> 'grp'"

datatype icnv_alice = Inp_Activation_Alice
datatype icnv_bob = Iact_Activation_Bob

datatype ocnv_alice = Out_Activation_Alice
datatype ocnv_bob = Out_Activation_Bob

fun alice_callee :: "'grp cstate \<Rightarrow> key.iusr_alice + icnv_alice 
  \<Rightarrow> (('grp key.ousr_alice + ocnv_alice) \<times> 'grp cstate, 'grp auth.iusr_alice + auth.iusr_bob, auth.ousr_alice + 'grp auth.ousr_bob) gpv"
  where
    "alice_callee CState_Void (Inr _) = do {
      x \<leftarrow> lift_spmf (sample_uniform (order \<G>));
      let msg = \<^bold>g [^] x;
      Pause
        (Inl (auth.Inp_Send msg))
        (\<lambda>rsp. case rsp of
          Inl _ \<Rightarrow> Done (Inr Out_Activation_Alice, CState_Half x)
        | Inr _ \<Rightarrow> Fail) }"
  | "alice_callee (CState_Half x) (Inl _) =
      Pause
        (Inr auth.Inp_Recv)
        (\<lambda>rsp. case rsp of
          Inl _ \<Rightarrow> Fail
        | Inr msg \<Rightarrow> case msg of
            auth.Out_Recv gy \<Rightarrow> 
              let key = gy [^] x in 
              Done (Inl (key.Out_Alice key), CState_Full (x, key)))"
  | "alice_callee (CState_Full (x, key)) (Inl _) = Done (Inl (key.Out_Alice key), CState_Full (x, key))"
  | "alice_callee _ _ = Fail"

fun bob_callee :: "'grp cstate  \<Rightarrow> key.iusr_bob + icnv_bob 
  \<Rightarrow> (('grp key.ousr_bob + ocnv_bob) \<times> 'grp cstate, auth.iusr_bob + 'grp auth.iusr_alice, 'grp auth.ousr_bob + auth.ousr_alice) gpv"
  where
    "bob_callee CState_Void (Inr _) = do {
      y \<leftarrow> lift_spmf (sample_uniform (order \<G>));
      let msg = \<^bold>g [^] y;
      Pause
        (Inr (auth.Inp_Send msg))
        (\<lambda>rsp. case rsp of
          Inl _ \<Rightarrow> Fail
        | Inr _ \<Rightarrow> Done (Inr Out_Activation_Bob, CState_Half y)) }"
  | "bob_callee (CState_Half y) (Inl _) =
      Pause
        (Inl auth.Inp_Recv)
        (\<lambda>rsp. case rsp of
          Inl msg \<Rightarrow> case msg of
            auth.Out_Recv gx \<Rightarrow>
              let k = gx [^] y in 
              Done (Inl (key.Out_Bob k), CState_Full (y, k))
        | Inr _ \<Rightarrow> Fail)"
  | "bob_callee (CState_Full (y, key)) (Inl _) =  Done (Inl (key.Out_Bob key), CState_Full (y, key))"
  | "bob_callee _ _ = Fail"


subsection \<open>Defining adversary callee\<close>
(*
astate_rbase \<longrightarrow> ranmed to \<longrightarrow> asate_chann
datatype astate_chann = AState_Available | AState_Unavailable
type_synonym 'grp' astate_lbase = "('grp' \<times> 'grp') option"
type_synonym 'grp' astate_single = "'grp' astate_lbase \<times> astate_rbase"*)
type_synonym 'grp' astate = "('grp' \<times> 'grp') option"

type_synonym 'grp' isim = "'grp' auth.iadv + 'grp' auth.iadv"
datatype osim = Out_Simulator

fun sim_callee_base :: "(('grp \<times> 'grp) \<Rightarrow> 'grp ) \<Rightarrow> ('grp astate, 'grp auth.iadv, 'grp auth.oadv) oracle'"
  where
    "sim_callee_base _ _ (Inl _) = return_pmf None"
  | "sim_callee_base pick gpair_opt (Inr (Inl _)) = do {
      sample \<leftarrow> do {
        x \<leftarrow> sample_uniform (order \<G>);
        y \<leftarrow> sample_uniform (order \<G>);
        return_spmf (\<^bold>g [^] x, \<^bold>g [^] y) };
      let sample' = case_option sample id gpair_opt;
      return_spmf (Inr (Inl (auth.Out_Look (pick sample'))), Some sample')  }"
  | "sim_callee_base _ gpair_opt (Inr (Inr _ )) = return_spmf (Inr (Inr auth.Out_Fedit), gpair_opt)"
  
fun sim_callee :: "'grp astate \<Rightarrow> 'grp auth.iadv + 'grp auth.iadv 
  \<Rightarrow> (('grp auth.oadv + 'grp auth.oadv) \<times> 'grp astate, key.iadv + 'grp isim, key.oadv + osim) gpv"
  where
    "sim_callee s_gpair query = 
      (let handle = (\<lambda>gpair_pick wrap_out q_split. do {
        _ \<leftarrow> Pause (Inr query) Done;
        (out, s_gpair') \<leftarrow> lift_spmf (sim_callee_base gpair_pick s_gpair q_split);
        Done (wrap_out out, s_gpair')  }) in 
      case_sum (handle fst Inl) (handle snd Inr) query)"

subsection \<open>Defining event-translator\<close>

datatype estate_base = EState_Void | EState_Store | EState_Collect
type_synonym estate = "bool \<times> (estate_base \<times> auth.s_shell) \<times> estate_base \<times> auth.s_shell"

definition einit :: estate
  where
    "einit \<equiv> (False, (EState_Void, {}), EState_Void, {})"

definition eleak :: "(estate, key.event, 'grp isim, osim) eoracle" 
  where
    "eleak \<equiv> (\<lambda>(s_flg, (s_event1, s_shell1), s_event2, s_shell2) query.
      let handle_arg1 = (\<lambda>s q. case (s, q) of (EState_Store, Some (Inr (Inr _))) \<Rightarrow> (True, EState_Collect) | (s', _) \<Rightarrow> (False, s')) in
      let handle_arg2 = (\<lambda>s q D. case (s, q) of (EState_Store, Inr  _) \<Rightarrow> D | _ \<Rightarrow> return_pmf None) in
      let (is_ch1, s_event1') = handle_arg1 s_event1 (case_sum Some (\<lambda>_. None) query) in
      let (is_ch2, s_event2') = handle_arg1 s_event2 (case_sum (\<lambda>_. None) Some query) in
      let check_pst1 = is_ch1 \<and> s_event2' \<noteq> EState_Void \<and> auth.Bob \<in> s_shell1 \<and> auth.Alice \<in> s_shell2 in
      let check_pst2 = is_ch2 \<and> s_event1' \<noteq> EState_Void \<and> auth.Alice \<in> s_shell1 \<and> auth.Bob \<in> s_shell2 in
      let e_pstfix1 = if check_pst1 then [key.Event_Shell key.Bob] else [] in
      let e_pstfix2 = if check_pst2 then [key.Event_Shell key.Alice] else [] in
      let e_prefix = if \<not>s_flg then [key.Event_Kernel] else [] in
      let (s_flg', event) = if is_ch2 \<or> is_ch1 then (True, e_prefix @ e_pstfix1 @ e_pstfix2) else (s_flg, []) in
      let result_base = return_spmf ((Out_Simulator, event), s_flg', (s_event1', s_shell1), s_event2', s_shell2) in
      case_sum (handle_arg2 s_event1) (handle_arg2 s_event2) query result_base)"

fun etran_base :: "(key.party \<times> key.party \<Rightarrow> key.party \<times> key.party) 
  \<Rightarrow> (estate, auth.event, key.event list) oracle'"
  where                                                         
    "etran_base mod_event (s_flg, (s_event1, s_shell1), s_event2, s_shell2) (auth.Event_Shell party) = 
      (let party_dual = auth.case_party (auth.Bob) (auth.Alice) party in
      let epair = auth.case_party prod.swap id party (key.Bob, key.Alice) in
      let (s_event_eq, s_event_neq) = auth.case_party prod.swap id party (s_event1, s_event2) in
      let check = party_dual \<in> s_shell2 \<and> s_event_eq = EState_Collect \<and> s_event_neq \<noteq> EState_Void in
      let event = if check then [key.Event_Shell ((fst o mod_event) epair)] else [] in
      let s_shell1' = insert party s_shell1 in
      if party \<in> s_shell1 then
        return_pmf None
      else
        return_spmf (event, s_flg, (s_event1, s_shell1'), s_event2, s_shell2))"

fun etran :: "(estate, (icnv_alice + icnv_bob) + auth.event + auth.event, key.event list) oracle'"
  where
    "etran (s_flg, (EState_Void, s_shell1), s_event2, s_shell2) (Inl (Inl _)) = 
      (let check = (s_event2 = EState_Collect \<and> auth.Alice \<in> s_shell1 \<and> auth.Bob \<in> s_shell2) in
      let event = if check then [key.Event_Shell key.Alice] else [] in
      let state = (s_flg, (EState_Store, s_shell1), s_event2, s_shell2) in
      if auth.Alice \<in> s_shell1 then return_spmf (event, state) else return_pmf None)"
  | "etran (s_flg, (s_event1, s_shell1), EState_Void, s_shell2) (Inl (Inr _)) = 
      (let check = (s_event1 = EState_Collect \<and> auth.Bob \<in> s_shell1 \<and> auth.Alice \<in> s_shell2) in
      let event = if check then [key.Event_Shell key.Bob] else [] in
      let state =  (s_flg, (s_event1, s_shell1), EState_Store, s_shell2) in
      if auth.Alice \<in> s_shell2 then return_spmf (event, state) else return_pmf None)"
  | "etran state (Inr query) =  
      (let handle = (\<lambda>mod_s mod_e q. do {
        (evt, state') \<leftarrow> etran_base mod_e (mod_s state) q;
        return_spmf (evt, mod_s state')  }) in
      case_sum (handle id id) (handle (apsnd prod.swap) prod.swap) query)"
  | "etran _ _ = return_pmf None"


subsection \<open>Defining Ideal and Real constructions\<close>

context 
  fixes 
    auth1_rest :: "('auth1_s_rest, auth.event, 'auth1_iadv_rest, 'auth1_iusr_rest, 'auth1_oadv_rest, 'auth1_ousr_rest) rest_wstate" and 
    auth2_rest :: "('auth2_s_rest, auth.event, 'auth2_iadv_rest, 'auth2_iusr_rest, 'auth2_oadv_rest, 'auth2_ousr_rest) rest_wstate"
begin

primcorec ideal_core_alt
  where
    "cpoke ideal_core_alt =  cpoke (translate_core etran key.core)"
  | "cfunc_adv ideal_core_alt = \<dagger>(cfunc_adv key.core) \<oplus>\<^sub>O (\<lambda>(se, sc) q. do {
      ((out, es), se') \<leftarrow> eleak se q;
      sc' \<leftarrow> foldl_spmf (cpoke key.core) (return_spmf sc) es;
      return_spmf (out, se', sc')   })"
  | "cfunc_usr ideal_core_alt = cfunc_usr (translate_core etran key.core)"

primcorec ideal_rest_alt
  where
    "rinit ideal_rest_alt = rinit (parallel_rest auth1_rest auth2_rest)"
  | "rfunc_adv ideal_rest_alt = (\<lambda>s q. map_spmf (apfst (apsnd (map Inr))) (rfunc_adv (parallel_rest auth1_rest auth2_rest) s q))"
  | "rfunc_usr ideal_rest_alt = (
      let handle = map_sum (\<lambda>_ :: icnv_alice. Out_Activation_Alice) (\<lambda>_ :: icnv_bob. Out_Activation_Bob) in
      plus_eoracle (\<lambda>s q. return_spmf ((handle q, [q]), s)) (rfunc_usr (parallel_rest auth1_rest auth2_rest)))"

primcorec ideal_rest 
  where
    "rinit ideal_rest = (einit, rinit ideal_rest_alt)"
  | "rfunc_adv ideal_rest = (\<lambda>s q. case q of 
      Inl ql \<Rightarrow> map_spmf (apfst (map_prod Inl id)) (eleak\<dagger> s ql)
    | Inr qr \<Rightarrow> map_spmf (apfst (map_prod Inr id)) (translate_eoracle etran \<dagger>(rfunc_adv ideal_rest_alt) s qr))"
  | "rfunc_usr ideal_rest = translate_eoracle etran \<dagger>(rfunc_usr ideal_rest_alt)"

definition ideal_resource 
  where
    "ideal_resource \<equiv> 
      (let sim = CNV sim_callee None in
      attach ((sim |\<^sub>= 1\<^sub>C ) \<odot> lassocr\<^sub>C |\<^sub>= 1\<^sub>C |\<^sub>= 1\<^sub>C) (key.resource ideal_rest))"

definition real_resource 
  where
    "real_resource \<equiv> 
      (let dh_wiring = parallel_wiring \<odot> (CNV alice_callee CState_Void |\<^sub>= CNV bob_callee CState_Void) \<odot> parallel_wiring \<odot> (1\<^sub>C |\<^sub>= swap\<^sub>C) in
      attach (((1\<^sub>C |\<^sub>= 1\<^sub>C) |\<^sub>= rassocl\<^sub>C \<odot> (dh_wiring |\<^sub>= 1\<^sub>C)) \<odot> fused_wiring) ((auth.resource auth1_rest) \<parallel> (auth.resource auth2_rest)))"


subsection \<open>Wiring and simplifying the Ideal construction\<close>

abbreviation basic_rest_sinit
  where
    "basic_rest_sinit \<equiv> (((), ()), rinit auth1_rest, rinit auth2_rest)"
  
primcorec basic_rest :: "((unit \<times> unit) \<times> _, _, _, _, _, _, _) rest_scheme"
  where
    "rinit basic_rest = (rinit auth1_rest, rinit auth2_rest)"
  | "rfunc_adv basic_rest = \<dagger>(parallel_eoracle (rfunc_adv auth1_rest) (rfunc_adv auth2_rest))"
  | "rfunc_usr basic_rest = \<dagger>(parallel_eoracle (rfunc_usr auth1_rest) (rfunc_usr auth2_rest))"

definition ideal_s_core' :: "('grp astate \<times> _) \<times> _ \<times> 'grp key.state"
  where
    "ideal_s_core' \<equiv> ((None, ()), einit, key.PState_Store, {})"

definition ideal_s_rest'
  where
    "ideal_s_rest' \<equiv> basic_rest_sinit"

primcorec ideal_core' 
  where
    "cpoke ideal_core' = (\<lambda>(s_cnv, s_event, s_core) event. do {
      (events, s_event') \<leftarrow> (etran s_event event);
      s_core' \<leftarrow> foldl_spmf key.poke (return_spmf s_core) events;
      return_spmf (s_cnv, s_event', s_core')  })"
  | "cfunc_adv ideal_core' = (\<lambda>((s_sim, _), s_event_core) q. 
      map_spmf 
        (\<lambda>((out, s_sim'), s_event_core'). (out, (s_sim', ()), s_event_core'))
        (exec_gpv
          (\<dagger>key.iface_adv \<oplus>\<^sub>O (\<lambda>(se, sc) isim. do {
            ((out, es), se') \<leftarrow> eleak se isim;
            sc' \<leftarrow> foldl_spmf (cpoke key.core) (return_spmf sc) es;
            return_spmf (out, se', sc')   }))
          (sim_callee s_sim q) s_event_core))"
  | "cfunc_usr ideal_core' = (\<lambda>(s_cnv, s_core) q. 
      map_spmf (\<lambda>(out, s_core'). (out, s_cnv, s_core')) (\<dagger>key.iface_usr s_core q))"

primcorec ideal_rest'
  where
    "rinit ideal_rest' = rinit basic_rest"
  | "rfunc_adv ideal_rest' = (\<lambda>s q. map_spmf (apfst (apsnd (map Inr))) (rfunc_adv basic_rest s q))"
  | "rfunc_usr ideal_rest' = (
      let handle = map_sum (\<lambda>_ :: icnv_alice. Out_Activation_Alice) (\<lambda>_ :: icnv_bob. Out_Activation_Bob) in
      plus_eoracle (\<lambda>s q. return_spmf ((handle q, [q]), s)) (rfunc_usr basic_rest))"


subsubsection \<open>The ideal attachment lemma\<close>

context
begin

lemma ideal_resource_shift_interface: "key.resource ideal_rest = RES 
    (apply_wiring (rassocl\<^sub>w |\<^sub>w (id, id)) (fused_resource.fuse ideal_core_alt ideal_rest_alt)) 
    ((einit, key.PState_Store, {}), rinit ideal_rest_alt)"
proof -
  have "state_iso (rprodl \<circ> apfst prod.swap, apfst prod.swap \<circ> lprodr)"
    by(simp add: state_iso_def rprodl_def lprodr_def apfst_def; unfold_locales; simp add: split_def)

  note f1= resource_of_oracle_state_iso[OF this]

  have f2: "key.fuse ideal_rest = apply_state_iso (rprodl \<circ> apfst prod.swap, apfst prod.swap \<circ> lprodr)
         (apply_wiring (rassocl\<^sub>w |\<^sub>w (id, id)) (fused_resource.fuse ideal_core_alt ideal_rest_alt))"
    by (rule move_simulator_interface[unfolded apply_wiring_state_iso_assoc, where etran=etran and ifunc=eleak and einit=einit and 
          core=key.core and rest=ideal_rest and core'=ideal_core_alt and rest'=ideal_rest_alt]) simp_all

  show ?thesis
    unfolding key.resource_def
    by (subst f2, subst f1) simp
qed

private lemma ideal_resource_alt_def: "ideal_resource = 
  (let sim = CNV sim_callee None in
  let s_init = ((einit, key.PState_Store, {}), rinit ideal_rest_alt) in
  attach ((sim |\<^sub>= 1\<^sub>C) |\<^sub>= 1\<^sub>C |\<^sub>= 1\<^sub>C) (RES (fused_resource.fuse ideal_core_alt ideal_rest_alt) s_init))"
proof -
  note ideal_resource_shift_interface
  moreover have "sim = CNV sim_callee None \<Longrightarrow>
  (sim |\<^sub>= 1\<^sub>C) \<odot> lassocr\<^sub>C |\<^sub>= 1\<^sub>C |\<^sub>= 1\<^sub>C \<rhd> RES (apply_wiring (rassocl\<^sub>w |\<^sub>w (id, id)) (fused_resource.fuse ideal_core_alt ideal_rest_alt)) s = 
  (sim |\<^sub>= 1\<^sub>C) |\<^sub>= 1\<^sub>C |\<^sub>= 1\<^sub>C \<rhd> RES (fused_resource.fuse ideal_core_alt ideal_rest_alt) s"  (is "?L \<Longrightarrow> ?R") for sim s
  proof -
    have fact1: "\<I>_full, \<I>_full \<oplus>\<^sub>\<I> \<I>_full \<turnstile>\<^sub>C CNV sim_callee s \<surd>" for s
      apply(subst WT_converter_of_callee)
        apply (rule WT_gpv_\<I>_mono)
         apply (rule WT_gpv_full)
        apply (rule \<I>_full_le_plus_\<I>)
         apply(rule order_refl)
        apply(rule order_refl)
      by (simp_all add: )

    have fact2: "(\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_full)) \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<turnstile>c
      apply_wiring (rassocl\<^sub>w |\<^sub>w (id, id)) (fused_resource.fuse ideal_core_alt ideal_rest_alt) s \<surd>" for s
      apply (rule WT_calleeI)
      subgoal for call
        apply (cases s, cases call)
         apply (rename_tac [!] x)
         apply (case_tac [!] x)
           apply (rename_tac [2] y)
           apply (case_tac [2] y)
        by (auto simp add: apply_wiring_def rassocl\<^sub>w_def parallel2_wiring_def fused_resource.fuse.simps)
      done

    note [simp] = spmf.map_comp map_bind_spmf bind_map_spmf bind_spmf_const o_def

    assume ?L
    then show ?R
      apply simp
      apply (subst (1 2) conv_callee_parallel_id_right[symmetric, where s'="()"])
      apply(subst eq_resource_on_UNIV_iff[symmetric])
      apply (subst eq_resource_on_trans)
        apply (rule eq_\<I>_attach_on')
          defer
          apply (rule parallel_converter2_eq_\<I>_cong)
           apply (rule comp_converter_of_callee_wiring)
            apply (rule wiring_lassocr)
           apply (subst conv_callee_parallel_id_right)
           apply(rule WT_intro)+ 
            apply (rule fact1)
           apply(rule WT_intro)+
          apply (rule eq_\<I>_converter_reflI)
          apply(rule WT_intro)+
         defer
         apply (subst (1 2 3 4) converter_of_callee_id_oracle[symmetric, where s="()"])
         apply (subst conv_callee_parallel[symmetric])+
         apply (subst (1 2) attach_CNV_RES)
      subgoal 
        apply (rule eq_resource_on_resource_of_oracleI[where S="(=)"])
         defer
         apply simp
        apply (rule rel_funI)+
        apply (simp add: prod.rel_eq eq_on_def)
        subgoal for s' s q' q 
          apply (cases s; cases q)
           apply (rename_tac [!] x)
           apply (case_tac [!] x)
             apply (rename_tac [!] y)
             apply (case_tac [4] y)
              apply (auto simp add: apply_wiring_def parallel2_wiring_def attach_wiring_right_def 
                rassocl\<^sub>w_def lassocr\<^sub>w_def map_fun_def map_prod_def split_def)
          subgoal for s_flg _ _ _ _ _ _ _ _ _ q
            apply (case_tac "(s_flg, q)" rule: sim_callee.cases)
            apply (simp_all add: split_def split!: sum.split if_splits cong: if_cong)
            by (rule rel_spmf_bindI'[where A="(=)"], simp, clarsimp split!: sum.split if_splits 
                simp add: split_def map_gpv_conv_bind[symmetric] map_lift_spmf map'_lift_spmf)+
          by (simp add: spmf_rel_eq map_fun_def id_oracle_def split_def; 
              rule bind_spmf_cong[OF refl], clarsimp split!: sum.split if_splits 
                simp add: split_def map_gpv_conv_bind[symmetric] map_lift_spmf map'_lift_spmf)+ 
        done
        apply simp
       apply (rule WT_resource_of_oracle[OF fact2])
      by simp
  qed

  ultimately show ?thesis
    unfolding ideal_resource_def by simp
qed

lemma attach_ideal: "ideal_resource = RES (fused_resource.fuse ideal_core' ideal_rest') (ideal_s_core', ideal_s_rest')"
proof -

  have fact1: "ideal_rest' = attach_rest 1\<^sub>I 1\<^sub>I id ideal_rest_alt"  (is "?L = ?R")
  proof -
    note [simp] = spmf.map_comp map_bind_spmf bind_map_spmf bind_spmf_const o_def

    have "rinit ?L = rinit ?R"
      by simp

    moreover have "rfunc_adv ?L = rfunc_adv ?R"
      unfolding attach_rest_id_oracle_adv 
      by (simp add: extend_state_oracle_def split_def map_spmf_conv_bind_spmf)

    moreover have "rfunc_usr ?L = rfunc_usr ?R"
      unfolding attach_rest_id_oracle_usr 
      apply (rule ext)+
      subgoal for s q by (cases q) (simp_all add: split_def extend_state_oracle_def plus_eoracle_def)
      done

    ultimately show ?thesis
      by (coinduction) simp
  qed

  have fact2: "ideal_core' = attach_core sim_callee 1\<^sub>I ideal_core_alt" (is "?L = ?R")
  proof -

    have "cpoke ?L = cpoke ?R"
      by (simp add: split_def map_spmf_conv_bind_spmf)

    moreover have "cfunc_adv ?L = cfunc_adv ?R"
      unfolding attach_core_def
      by (simp add: split_def)

    moreover have "cfunc_usr ?L = cfunc_usr ?R"
      unfolding attach_core_id_oracle_usr
      by simp
    
    ultimately show ?thesis
      by (coinduction) simp
  qed

  show ?thesis
    unfolding ideal_resource_alt_def Let_def
    apply(subst (1 2 3) converter_of_callee_id_oracle[symmetric, of "()"])
    apply(subst attach_parallel_fuse')
    by (simp add: fact1 fact2 ideal_s_core'_def ideal_s_rest'_def)
qed

end


subsection \<open>Wiring and simplifying the Real construction\<close>

definition real_s_core' :: "(_ \<times> 'grp cstate \<times> 'grp cstate) \<times> 'grp auth.state \<times> 'grp auth.state"
  where
    "real_s_core' \<equiv> (((), CState_Void, CState_Void), (auth.State_Void, {}), (auth.State_Void, {}))"

definition real_s_rest'
  where
    "real_s_rest' \<equiv> basic_rest_sinit"

primcorec real_core' :: "((unit \<times> _) \<times> _, _, _, _, _, _) core"
  where
    "cpoke real_core' = (\<lambda>(s_advusr, s_core) event. 
      map_spmf (Pair s_advusr) (parallel_handler auth.poke auth.poke s_core event))"
  | "cfunc_adv real_core' = \<dagger>(auth.iface_adv \<ddagger>\<^sub>O auth.iface_adv)" 
  | "cfunc_usr real_core' =  (\<lambda>((s_adv, s_usr), s_core) iusr.
      let handle_req = lsumr \<circ> map_sum id (rsuml \<circ> map_sum swap_sum id \<circ> lsumr) \<circ> rsuml in
      let handle_ret = lsumr \<circ> (map_sum id (rsuml \<circ> (map_sum swap_sum id \<circ> lsumr)) \<circ> rsuml) \<circ> map_sum id swap_sum in
      let handle_inp =  map_sum id swap_sum \<circ> (lsumr \<circ> map_sum id (rsuml \<circ> map_sum swap_sum id \<circ> lsumr) \<circ> rsuml) in      
      let handle_out = apfst (lsumr \<circ> (map_sum id (rsuml \<circ> (map_sum swap_sum id \<circ> lsumr)) \<circ> rsuml)) in
      map_spmf 
        (\<lambda>((ousr, s_usr'), s_core'). (ousr, (s_adv, s_usr'), s_core'))
        (exec_gpv 
          (auth.iface_usr \<ddagger>\<^sub>O auth.iface_usr)
          (map_gpv' 
            handle_out handle_inp handle_ret
            ((alice_callee \<ddagger>\<^sub>I bob_callee) s_usr (handle_req iusr)))
          s_core))"

definition real_rest' :: "((unit \<times> unit) \<times> _, _, _, _, _, _, _) rest_scheme"
  where
    "real_rest' \<equiv> basic_rest"


subsubsection \<open>The real attachment lemma\<close>

lemma attach_real: "real_resource = 1\<^sub>C |\<^sub>= rassocl\<^sub>C \<rhd> RES (fused_resource.fuse real_core' real_rest') (real_s_core', real_s_rest')"
proof -

  have att_core: "real_core' = attach_core 1\<^sub>I
            (attach_wiring parallel_wiring\<^sub>w
              (attach_wiring_right (parallel_wiring\<^sub>w \<circ>\<^sub>w (id, id) |\<^sub>w swap\<^sub>w) (alice_callee \<ddagger>\<^sub>I bob_callee)))
            (parallel_core auth.core auth.core)" (is "?L = ?R")
  proof -

    have "cpoke ?L = cpoke ?R"
      by simp

    moreover have "cfunc_adv ?L = cfunc_adv ?R"
      unfolding attach_core_id_oracle_adv
      by (simp add: extend_state_oracle_def)

    moreover have "cfunc_usr ?L = cfunc_usr ?R"
      unfolding parallel_wiring\<^sub>w_def swap_lassocr\<^sub>w_def swap\<^sub>w_def lassocr\<^sub>w_def rassocl\<^sub>w_def
      apply (simp add: parallel2_wiring_simps comp_wiring_simps)
      apply (simp add: attach_wiring_simps attach_wiring_right_simps)
      by (simp add: map_gpv_conv_map_gpv' map_gpv'_comp apfst_def)

    ultimately show ?thesis 
      by (coinduction) blast
  qed

  have att_rest: "real_rest' = attach_rest 1\<^sub>I 1\<^sub>I id (parallel_rest auth1_rest auth2_rest)" (is "?L = ?R")
  proof -
    have "rinit ?L = rinit ?R"
      unfolding real_rest'_def
      by simp

    moreover have "rfunc_adv ?L = rfunc_adv ?R"
      unfolding real_rest'_def attach_rest_id_oracle_adv
      by (simp add: extend_state_oracle_def)

    moreover have "rfunc_usr ?L = rfunc_usr ?R"
      unfolding real_rest'_def attach_rest_id_oracle_usr
      by (simp add: extend_state_oracle_def)

    ultimately show ?thesis 
      by (coinduction) blast
  qed

  have fact1: "
    (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_full), (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<turnstile>\<^sub>C 
      CNV (alice_callee \<ddagger>\<^sub>I bob_callee) (CState_Void, CState_Void) \<surd>"
    apply(subst conv_callee_parallel)
    apply(rule WT_intro)
     apply (rule WT_converter_of_callee[where \<I>="\<I>_full \<oplus>\<^sub>\<I> \<I>_full" and \<I>'="\<I>_full \<oplus>\<^sub>\<I> \<I>_full"])
      apply (rule WT_gpv_\<I>_mono)
       apply (rule WT_gpv_full)
      apply (rule \<I>_full_le_plus_\<I>)
       apply(rule order_refl)
      apply(rule order_refl)
    subgoal for s q
      apply (cases s; cases q)
      apply (auto simp add: Let_def  split!: cstate.splits if_splits auth.ousr_bob.splits)
      by (metis auth.ousr_bob.exhaust range_eqI)
    apply (rule WT_converter_of_callee[where \<I>="\<I>_full \<oplus>\<^sub>\<I> \<I>_full" and \<I>'="\<I>_full \<oplus>\<^sub>\<I> \<I>_full"])
     apply (rule WT_gpv_\<I>_mono)
      apply (rule WT_gpv_full)
     apply (rule \<I>_full_le_plus_\<I>)
      apply(rule order_refl)
     apply(rule order_refl)
    subgoal for s q
      apply (cases s; cases q)
      apply (auto simp add: Let_def  split!: cstate.splits if_splits auth.ousr_bob.splits)
      by (metis auth.ousr_bob.exhaust range_eqI)
    done


  have fact2: "
    (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_full),(\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<turnstile>\<^sub>C 
      CNV (alice_callee \<ddagger>\<^sub>I bob_callee) (CState_Void, CState_Void) \<odot> parallel_wiring \<odot> (1\<^sub>C |\<^sub>= swap\<^sub>C) \<surd>"
    apply(rule WT_intro)
     apply (rule fact1)
    apply(rule WT_intro)+
    done

  have fact3: "
    (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_full),(\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_full)  \<turnstile>\<^sub>C 
      CNV (alice_callee \<ddagger>\<^sub>I bob_callee) (CState_Void, CState_Void) \<odot> parallel_wiring \<odot> (1\<^sub>C |\<^sub>= swap\<^sub>C) \<sim> 
      CNV (attach_wiring_right (parallel_wiring\<^sub>w \<circ>\<^sub>w (id, id) |\<^sub>w swap\<^sub>w) (alice_callee \<ddagger>\<^sub>I bob_callee)) (CState_Void, CState_Void)"
    apply (rule comp_converter_of_callee_wiring)
     apply(rule wiring_intro)+
    apply(rule fact1)
    done

  have fact4: "
    (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_full),(\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<turnstile>\<^sub>C 
      parallel_wiring \<odot> CNV (alice_callee \<ddagger>\<^sub>I bob_callee) (CState_Void, CState_Void) \<odot> parallel_wiring \<odot> (1\<^sub>C |\<^sub>= swap\<^sub>C) \<sim>
      CNV (attach_wiring parallel_wiring\<^sub>w (attach_wiring_right (parallel_wiring\<^sub>w \<circ>\<^sub>w (id, id) |\<^sub>w swap\<^sub>w) (alice_callee \<ddagger>\<^sub>I bob_callee))) (CState_Void, CState_Void)"
    apply (rule eq_\<I>_converter_trans)
     apply (rule eq_\<I>_comp_cong)
      apply(rule eq_\<I>_converter_reflI)
      apply(rule WT_intro)
     apply (rule fact3)
    apply (rule comp_wiring_converter_of_callee)
     apply (rule wiring_intro)
    apply (subst eq_\<I>_converterD_WT[OF fact3, simplified fact2, symmetric])
    by blast

  show ?thesis 
    unfolding real_resource_def auth.resource_def
    apply (subst resource_of_parallel_oracle[symmetric])
    apply (subst attach_compose)
    apply(subst attach_wiring_resource_of_oracle)
       apply (rule wiring_intro)
      apply (rule WT_resource_of_oracle[where \<I>="((\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_full)) \<oplus>\<^sub>\<I> ((\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_full))"])
    subgoal for _ s
      apply (rule WT_calleeI)
      apply (cases s)
      apply(case_tac call)
       apply(rename_tac [!] x)
       apply(case_tac [!] x)
         apply(rename_tac [!] y)
         apply(case_tac [!] y)
             apply(auto simp add: fused_resource.fuse.simps)
      done
     apply simp
    subgoal
      apply (subst parallel_oracle_fuse)
      apply(subst resource_of_oracle_state_iso)
       apply simp
      apply(simp add: parallel_state_iso_def)
      apply(subst parallel_converter2_comp2_out)
      apply(subst conv_callee_parallel[symmetric])
      apply(subst eq_resource_on_UNIV_iff[symmetric])
      apply(rule eq_resource_on_trans)
       apply(rule eq_\<I>_attach_on')
         prefer 2
         apply (rule eq_\<I>_comp_cong)
          apply(rule eq_\<I>_converter_reflI)
          apply(rule WT_intro)+
         apply(rule parallel_converter2_eq_\<I>_cong)
          apply(rule eq_\<I>_converter_reflI)
          apply(rule WT_intro)+
         apply(rule parallel_converter2_eq_\<I>_cong)
          prefer 2
          apply(rule eq_\<I>_converter_reflI)
          apply(rule WT_intro)+
         apply(rule fact4)
        prefer 3
        apply(subst attach_compose)
        apply(fold converter_of_callee_id_oracle[where s="()"])
        apply(subst attach_parallel_fuse'[where f_init=id])
        apply(unfold converter_of_callee_id_oracle)
        apply(subst eq_resource_on_UNIV_iff)
      subgoal by (simp add: att_core[symmetric] att_rest[symmetric] real_s_core'_def real_s_rest'_def)
       apply (rule WT_resource_of_oracle[where \<I>="(\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<oplus>\<^sub>\<I> (((\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_full)) \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_full))"])
      subgoal for s
        apply (rule WT_calleeI)
        apply (cases s)
        apply(case_tac call)
         apply(rename_tac [!] x)
         apply(case_tac [!] x)
           apply(rename_tac [!] y)
           apply(case_tac [!] y)
               apply(rename_tac [5-6] z)
               apply (case_tac [5-6] z)
                 apply (auto simp add: fused_resource.fuse.simps parallel_eoracle_def)
        done
      apply simp
      done
    done
qed


subsection \<open>A lazy construction and its DH reduction\<close>


subsubsection \<open>Defining a lazy construction with an inlined sampler\<close>

\<comment> \<open>"sample triple" and  "basic core" states\<close>
type_synonym 'grp' st_state =  "('grp' \<times> 'grp' \<times> 'grp') option"
type_synonym 'grp' bc_state = "('grp' st_state \<times> 'grp' cstate \<times> 'grp' cstate) \<times> 'grp' auth.state \<times> 'grp' auth.state"

context
  fixes sample_triple :: "('grp \<times> 'grp \<times> 'grp) spmf"
begin

abbreviation basic_core_sinit :: "'grp bc_state"
  where
    "basic_core_sinit \<equiv> ((None, CState_Void, CState_Void), (auth.State_Void, {}), auth.State_Void, {})"

fun basic_core_helper_base :: "('grp bc_state, unit, unit) oracle'"
  where
    "basic_core_helper_base ((s_key, CState_Void, s_cnv2), (auth.State_Void, parties1), s_auth2) _ =
      (if auth.Alice \<in> parties1 
      then return_spmf ((), (s_key, CState_Half 0, s_cnv2), (auth.State_Store \<one>, parties1), s_auth2)
      else return_pmf None)"
  | "basic_core_helper_base _ _ = return_pmf None"

definition basic_core_helper :: "('grp bc_state, icnv_alice + icnv_bob) handler"
  where
    "basic_core_helper \<equiv> (\<lambda>state query.
      let handle = \<lambda>((sk, (sc1, sc2)), sa1, sa2). ((sk, (sc2, sc1)), sa2, sa1) in
      let func = \<lambda>h_s f s. map_spmf (h_s o snd) (f (h_s s) ()) in      
      let func_alc = func id basic_core_helper_base in
      let func_bob = func handle basic_core_helper_base in
      case_sum (\<lambda>_. func_alc state) (\<lambda>_. func_bob state) query)"

fun basic_core_oracle_adv :: " unit + unit \<Rightarrow>  ('grp st_state \<times> 'grp auth.state, 'grp auth.iadv, 'grp auth.oadv) oracle'"
  where
    "basic_core_oracle_adv sel (None, auth.State_Store _, parties) (Inr (Inl _)) = do {
      (gxy, gx, gy) \<leftarrow> sample_triple;
      let out = case_sum (\<lambda>_. gx) (\<lambda>_. gy) sel;
      return_spmf (Inr (Inl (auth.Out_Look out)), Some (gxy, gx, gy), auth.State_Store \<one>, parties)
    }"
  | "basic_core_oracle_adv sel (Some dhs, auth.State_Store _, parties) (Inr (Inl _)) = 
      (case dhs of (gxy, gx, gy) \<Rightarrow>
        let out = case_sum (\<lambda>_. gx) (\<lambda>_. gy) sel in
        return_spmf (Inr (Inl (auth.Out_Look out)), Some dhs, auth.State_Store \<one>, parties))"
  | "basic_core_oracle_adv _ (s_key, auth.State_Store _, parties) (Inr (Inr _)) = 
      return_spmf (Inr (Inr auth.Out_Fedit), s_key, auth.State_Collect \<one>, parties)"
  | "basic_core_oracle_adv _ _ _ = return_pmf None"


fun basic_core_oracle_usr_base :: "('grp bc_state, unit, 'grp) oracle'"
  where
    "basic_core_oracle_usr_base ((s_key, CState_Half _, s_cnv2), s_auth1, auth.State_Collect _, parties2) _ =
      (let h_state = \<lambda>k. ((Some k, CState_Full (0, \<one>), s_cnv2), s_auth1, auth.State_Collected, parties2) in
      if auth.Bob \<in> parties2  then 
        (case s_key of
          None \<Rightarrow> do {
            (gxy, gx, gy) \<leftarrow> sample_triple;
            return_spmf (gxy, h_state (gxy, gx, gy)) }
        | Some (gxy, gx, gy) \<Rightarrow> return_spmf (gxy, h_state (gxy, gx, gy)))
      else return_pmf None)"
  | "basic_core_oracle_usr_base ((Some dhs, CState_Full _, s_cnv2), s_auth1, auth.State_Collected, parties2) _ = 
      (case dhs of (gxy, gx, gy) \<Rightarrow>
        return_spmf (gxy, (Some dhs, CState_Full (0, \<one>), s_cnv2), s_auth1, auth.State_Collected, parties2))"
  | "basic_core_oracle_usr_base _ _ = return_pmf None"
  
definition basic_core_oracle_usr :: "(_, key.iusr_alice + key.iusr_bob, _) oracle'"
  where
    "basic_core_oracle_usr \<equiv> (\<lambda>state query.
      let handle = \<lambda>((sk, (sc1, sc2)), sa1, sa2). ((sk, (sc2, sc1)), sa2, sa1) in      
      let func = \<lambda>h_o h_s f s. map_spmf (map_prod h_o h_s) (f (h_s s) ()) in
      let func_alc = func (Inl o key.Out_Alice) id basic_core_oracle_usr_base in
      let func_bob = func (Inr o key.Out_Bob) handle basic_core_oracle_usr_base in
      case_sum (\<lambda>_. func_alc state) (\<lambda>_. func_bob state) query)"

primcorec basic_core 
  where
    "cpoke basic_core = (\<lambda>(s_other, s_core) event. 
      map_spmf (Pair s_other) (parallel_handler auth.poke auth.poke s_core event))"
  | "cfunc_adv basic_core = (\<lambda>((s_key, s_cnv), s_auth1, s_auth2) iadv. 
      let handle = (\<lambda>sel s_init h_out h_state query. 
        map_spmf 
          (\<lambda>(out, (s_key', s_auth')). (h_out out, (s_key', s_cnv), h_state s_auth' s_auth1 s_auth2)) 
          (basic_core_oracle_adv sel (s_key, s_init) query)) in
      case_sum (handle (Inl ()) s_auth1 Inl (\<lambda>x y z. (x, z))) (handle (Inr ()) s_auth2 Inr (\<lambda>x y z. (y, x))) iadv)"
  | "cfunc_usr basic_core = 
      (let handle = map_sum (\<lambda>_. Out_Activation_Alice) (\<lambda>_. Out_Activation_Bob) in
      basic_core_oracle_usr \<oplus>\<^sub>O (\<lambda>s q. map_spmf (Pair (handle q)) (basic_core_helper s q)))"

primcorec lazy_core
  where
    "cpoke lazy_core = (\<lambda>s. case_sum (\<lambda>q. basic_core_helper s q) (cpoke basic_core s))"
  | "cfunc_adv lazy_core = cfunc_adv basic_core "
  | "cfunc_usr lazy_core = basic_core_oracle_usr"

definition lazy_rest
  where
    "lazy_rest \<equiv> ideal_rest'"

end


subsubsection \<open>Defining a lazy construction with an external sampler\<close>

context
begin

private type_synonym  ('grp', 'iadv_rest', 'iusr_rest') dh_inp = "
  (('grp' auth.iadv + 'grp' auth.iadv) + 'iadv_rest') + (key.iusr_alice + key.iusr_bob) + (icnv_alice + icnv_bob) + 'iusr_rest'"

private type_synonym  ('grp', 'oadv_rest', 'ousr_rest') dh_out = "
  (('grp' auth.oadv + 'grp' auth.oadv) + 'oadv_rest') + ('grp' key.ousr_alice + 'grp' key.ousr_bob) + (ocnv_alice + ocnv_bob) + 'ousr_rest'"

fun interceptor_base_look :: " unit + unit \<Rightarrow> 'grp st_state \<times> 'grp auth.state 
  \<Rightarrow> ('grp auth.oadv_look \<times> 'grp st_state, unit, 'grp \<times> 'grp \<times> 'grp) gpv"
  where
    "interceptor_base_look sel (None, auth.State_Store _, parties) = do {
      (gxy, gx, gy) \<leftarrow> Pause () Done;
      let out = case_sum (\<lambda>_. gx) (\<lambda>_. gy) sel;
      Done (auth.Out_Look out, Some (gxy, gx, gy))  }"
  | "interceptor_base_look sel (Some dhs, auth.State_Store _, parties) = (
      case dhs of (gxy, gx, gy) \<Rightarrow>
      let out = case_sum (\<lambda>_. gx) (\<lambda>_. gy) sel in
      Done (auth.Out_Look out, Some (gxy, gx, gy)))"
  | "interceptor_base_look _ _ = Fail"

fun interceptor_base_recv :: "'grp bc_state \<Rightarrow> ('grp \<times> 'grp bc_state, unit, 'grp \<times> 'grp \<times> 'grp) gpv"
  where
    "interceptor_base_recv ((s_key, CState_Half _, s_cnv2), s_auth1, auth.State_Collect _, parties2) = (
      let h_state = \<lambda>k. ((Some k, CState_Full (0, \<one>), s_cnv2), s_auth1, auth.State_Collected, parties2) in
      if auth.Bob \<in> parties2 then 
        case s_key of 
          None \<Rightarrow> do {
            (gxy, gx, gy) \<leftarrow> Pause () Done; 
            Done (gxy, h_state (gxy, gx, gy))  }
        | Some (gxy, gx, gy) \<Rightarrow> Done (gxy, h_state (gxy, gx, gy))
      else
        Fail)"
  | "interceptor_base_recv ((Some dhs, CState_Full _, s_cnv2), s_auth1, auth.State_Collected, parties2) = (
      case dhs of (gxy, gx, gy) \<Rightarrow>
        Done (gxy, (Some dhs, CState_Full (0, \<one>), s_cnv2), s_auth1, auth.State_Collected, parties2))"
  | "interceptor_base_recv _ = Fail"

fun interceptor :: " _ \<Rightarrow> (_, _, _) dh_inp  \<Rightarrow>  (('grp, _, _) dh_out \<times> _, unit, 'grp \<times> 'grp \<times> 'grp) gpv"
  where
    "interceptor (sc, sr) (Inl (Inl (q))) = (
      let select_s = (case sc of ((sk, _), sa1, sa2) \<Rightarrow> case_sum (\<lambda>_. (sk, sa1)) (\<lambda>_. (sk, sa2))) in
      let handle_s = (\<lambda>x. case sc of ((sk, (sc1, sc2)), sa1, sa2) \<Rightarrow> ((x, (sc1, sc2)), sa1, sa2)) in
      let func_look = (\<lambda>sel h_o. do {
        (o_look, dhs) \<leftarrow> interceptor_base_look (sel ()) (select_s (sel ())) ;
        Done (Inl (Inl (h_o (Inr (Inl o_look)))), handle_s dhs, sr)  }) in
      let func_dfe = do {
        (out, sc') \<leftarrow> lift_spmf (cfunc_adv (lazy_core undefined) sc q);
        Done (Inl (Inl out), sc', sr)  } in
      case q of
        (Inl (Inr (Inl _))) \<Rightarrow> func_look Inl Inl
      | (Inr (Inr (Inl _))) \<Rightarrow> func_look Inr Inr
      | _ \<Rightarrow> func_dfe)"
  | "interceptor (sc, sr) (Inl (Inr (q))) = do { 
      ((out, es), sr') \<leftarrow> lift_spmf (rfunc_adv lazy_rest sr q);
      sc' \<leftarrow> lift_spmf (foldl_spmf (\<lambda>a e. cpoke (lazy_core undefined) a e) (return_spmf sc) es);
      Done (Inl (Inr out), (sc', sr'))  }"
  | "interceptor (sc, sr) (Inr (Inl (q))) = (
      let handle = \<lambda>((sk, (sc1, sc2)), sa1, sa2). ((sk, (sc2, sc1)), sa2, sa1) in
      let func_recv = (\<lambda>h_o h_s. do {
        (o_recv, sc') \<leftarrow> interceptor_base_recv (h_s sc);
        Done (Inr (Inl (h_o o_recv)), h_s sc', sr)  }) in 
      case_sum (\<lambda>_. func_recv (Inl o key.Out_Alice) id) (\<lambda>_. func_recv (Inr o key.Out_Bob) handle) q)"
  | "interceptor (sc, sr) (Inr (Inr (q))) = do { 
      ((out, es), sr') \<leftarrow> lift_spmf (rfunc_usr lazy_rest sr q);
      sc' \<leftarrow> lift_spmf (foldl_spmf (\<lambda>a e. cpoke (lazy_core undefined) a e) (return_spmf sc) es);
      Done (Inr (Inr out), (sc', sr'))  }"

end


subsubsection \<open>Reduction to Diffie-Hellman game\<close>

definition DH0_sample :: "('grp \<times> 'grp \<times> 'grp) spmf"
  where
    "DH0_sample = do {
      x \<leftarrow> sample_uniform (order \<G>);
      y \<leftarrow> sample_uniform (order \<G>);
      return_spmf ((\<^bold>g [^] x) [^] y, \<^bold>g [^] x, \<^bold>g [^] y)  }"

definition DH1_sample :: "('grp \<times> 'grp \<times> 'grp) spmf"
  where
    "DH1_sample = do {
      x \<leftarrow> sample_uniform (order \<G>);
      y \<leftarrow> sample_uniform (order \<G>);
      z \<leftarrow> sample_uniform (order \<G>);
      return_spmf (\<^bold>g [^] z, \<^bold>g [^] x, \<^bold>g [^] y)  }"

lemma lossless_DH0_sample [simp]: "lossless_spmf DH0_sample"
  by (auto simp add: DH0_sample_def sample_uniform_def intro: order_gt_0)

lemma lossless_DH1_sample [simp]: "lossless_spmf DH1_sample"
  by (auto simp add: DH1_sample_def sample_uniform_def intro: order_gt_0)

definition DH_adversary_curry :: "('grp \<times> 'grp \<times> 'grp \<Rightarrow> bool spmf) \<Rightarrow> 'grp \<Rightarrow> 'grp \<Rightarrow> 'grp \<Rightarrow> bool spmf"
  where
    "DH_adversary_curry \<equiv> (\<lambda>A x y z. bind_spmf (return_spmf (z, x, y)) A)"

definition DH_adversary 
  where
    "DH_adversary D \<equiv> DH_adversary_curry (\<lambda>xyz. 
      run_gpv (obsf_oracle (obsf_oracle (\<lambda>(tpl, s) q. map_spmf (apsnd (Pair tpl) \<circ> fst) (exec_gpv (\<lambda>_ _. return_spmf (tpl, ())) (interceptor s q) ()))))
        (obsf_distinguisher D) (OK (OK (xyz, basic_core_sinit, basic_rest_sinit))))"

context
begin

private abbreviation "S_ic_asm s_cnv1 s_cnv2 s_krn1 s_krn2 \<equiv> 
  let s_cnvs = {CState_Void} \<union> {CState_Half 0} \<union> {CState_Full (0, \<one>)} in
  let s_krns = {auth.State_Void} \<union> {auth.State_Store  \<one>} \<union> {auth.State_Collect  \<one>} \<union> {auth.State_Collected} in
  s_cnv1 \<in> s_cnvs \<and> s_cnv2 \<in> s_cnvs \<and> s_krn1 \<in> s_krns \<and> s_krn2 \<in> s_krns"

private inductive S_ic :: "('grp \<times> 'grp \<times> 'grp) spmf \<Rightarrow> ('grp bc_state \<times> (unit \<times> unit) \<times> 'auth1_s_rest \<times> 'auth2_s_rest) spmf  \<Rightarrow> 
    (('grp \<times> 'grp \<times> 'grp) \<times> 'grp bc_state \<times> (unit \<times> unit) \<times> 'auth1_s_rest \<times> 'auth2_s_rest) spmf  \<Rightarrow> bool"
  for \<S> :: "('grp \<times> 'grp \<times> 'grp) spmf"  where
    "S_ic \<S> (return_spmf (((None, s_cnv1, s_cnv2), (s_krn1, s_act1), s_krn2, s_act2), ((), ()), s_rest1, s_rest2)) 
      (map_spmf (\<lambda>x. (x, (((None, s_cnv1, s_cnv2), (s_krn1, s_act1), s_krn2, s_act2), ((), ()), s_rest1, s_rest2))) \<S>)"
  if "S_ic_asm s_cnv1 s_cnv2 s_krn1 s_krn2"
  | "S_ic \<S> (return_spmf (((Some x, s_cnv1, s_cnv2), (s_krn1, s_act1), s_krn2, s_act2), ((), ()), s_rest1, s_rest2)) 
      (return_spmf (x, (((Some x, s_cnv1, s_cnv2), (s_krn1, s_act1), s_krn2, s_act2), ((), ()), s_rest1, s_rest2)))"
  if "S_ic_asm s_cnv1 s_cnv2 s_krn1 s_krn2"

private lemma trace_eq_intercept:
  defines "outs_adv \<equiv> ((UNIV <+> UNIV <+> UNIV) <+> UNIV <+> UNIV <+> UNIV) <+>  UNIV <+> UNIV"
      and "outs_usr \<equiv> (UNIV <+> UNIV) <+> (UNIV <+> UNIV) <+> UNIV <+> UNIV"
  assumes "lossless_spmf sample_triple"
    shows "trace_callee_eq (fused_resource.fuse (lazy_core sample_triple) lazy_rest) 
    (\<lambda>(tpl, s) q. map_spmf (apsnd (Pair tpl) \<circ> fst) (exec_gpv (\<lambda>_ _. return_spmf (tpl, ())) (interceptor s q) ()))
    (outs_adv <+> outs_usr) 
    (return_spmf (basic_core_sinit, basic_rest_sinit)) (pair_spmf sample_triple (return_spmf (basic_core_sinit, basic_rest_sinit)))" 
    (is "trace_callee_eq ?L ?R ?OI ?sl ?sr")
proof -
  have auth_poke_alt[simplified split_def Let_def]: 
    "auth.poke = (\<lambda>(sl, sr) q. let p = auth.case_event id q in
      map_spmf (Pair sl) (if p \<in> sr then return_pmf None else return_spmf (insert p sr)))"
    by (rule ext)+ (simp add: split_def Let_def split!: auth.event.splits)

  note S_ic_cases = S_ic.cases[where \<S>=sample_triple, simplified]
  note S_ic_intros = S_ic.intros[where \<S>=sample_triple, simplified]

  note [simp] = assms(3)[unfolded lossless_spmf_def] mk_lossless_lossless[OF assms(3)] 
    fused_resource.fuse.simps lazy_rest_def basic_core_oracle_usr_def basic_core_helper_def
    exec_gpv_bind spmf.map_comp map_bind_spmf bind_map_spmf bind_spmf_const o_def Let_def split_def
    extend_state_oracle_def plus_eoracle_def parallel_eoracle_def map_fun_def
  
  have "trace_callee_eq ?L ?R ?OI ?sl ?sr"
    unfolding assms(1,2) apply (rule trace'_eqI_sim_upto[where S="S_ic sample_triple"])
    subgoal Init_OK
      by (simp add: map_spmf_conv_bind_spmf[symmetric] pair_spmf_alt_def S_ic_intros)
    subgoal Out_OK for sl sr q
      apply (cases q)
      subgoal for q_adv
        apply (cases q_adv)
        subgoal for q_adv_core
          apply (cases q_adv_core)
          subgoal for q_acore1
            apply (cases q_acore1)
            subgoal for q_drop by (erule S_ic_cases) simp_all
            subgoal for q_lfe
              apply (cases q_lfe)
              subgoal for q_look
                apply (erule S_ic_cases)
                subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2  s_act1 s_act2 s_rest1 s_rest2
                  by (simp, case_tac "(Inl (), (None, s_krn1, s_act1))" rule: interceptor_base_look.cases) auto
                subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 x s_act1 s_act2 s_rest1 s_rest2
                  by (simp, case_tac "(Inl (), (Some x, s_krn1, s_act1))" rule: interceptor_base_look.cases) auto
                done
              subgoal for q_fedit
                apply (erule S_ic_cases)
                subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 s_act1 s_act2 s_rest1 s_rest2
                  by (simp, case_tac "(Inl (), (None, s_krn1, s_act1), Inr (Inr q_fedit))" rule: basic_core_oracle_adv.cases) simp_all
                subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 x s_act1 s_act2 s_rest1 s_rest2
                  by (simp, case_tac "(Inl (), (Some x, s_krn1, s_act1), Inr (Inr q_fedit))" rule: basic_core_oracle_adv.cases) simp_all
                done
              done
            done
          subgoal for q_acore2
            apply (cases q_acore2)
            subgoal for q_drop by (erule S_ic_cases) simp_all
            subgoal for q_lfe
              apply (cases q_lfe)
              subgoal for q_look
                apply (erule S_ic_cases)
                subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 s_act1 s_act2 s_rest1 s_rest2
                  by (simp, case_tac "(Inr (), (None, s_krn2, s_act2))" rule: interceptor_base_look.cases) auto
                subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 x s_act1 s_act2 s_rest1 s_rest2
                  by (simp, case_tac "(Inr (), (Some x, s_krn2, s_act2))" rule: interceptor_base_look.cases) auto
                done
              subgoal for q_fedit
                apply (erule S_ic_cases)
                subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 s_act1 s_act2 s_rest1 s_rest2
                  by (simp, case_tac "(Inr (), (None, s_krn2, s_act2), Inr (Inr q_fedit))" rule: basic_core_oracle_adv.cases) simp_all
                subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 x s_act1 s_act2 s_rest1 s_rest2
                  by (simp, case_tac "(Inr (), (Some x, s_krn2, s_act2), Inr (Inr q_fedit))" rule: basic_core_oracle_adv.cases) simp_all
                done
              done
            done
          done
        subgoal for q_adv_rest
          apply (cases q_adv_rest)
          subgoal for q_arest1 by (erule S_ic_cases) simp_all
          subgoal for q_arest2 by (erule S_ic_cases) simp_all
          done
        done
      subgoal for q_usr
        apply (cases q_usr)
        subgoal for q_usr_core
          apply (cases q_usr_core)
          subgoal for q_alice
            apply (erule S_ic_cases)
            subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 s_act1 s_act2 s_rest1 s_rest2
              by (simp, case_tac "(((None, s_cnv1, s_cnv2), (s_krn1, s_act1), s_krn2, s_act2), ())" rule: basic_core_oracle_usr_base.cases) (auto split: option.splits)
            subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 x s_act1 s_act2 s_rest1 s_rest2
              by (simp, case_tac "(((Some x, s_cnv1, s_cnv2), (s_krn1, s_act1), s_krn2, s_act2), ())" rule: basic_core_oracle_usr_base.cases) (auto split: option.splits)
            done
          subgoal for q_bob
            apply (erule S_ic_cases)
            subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 s_act1 s_act2 s_rest1 s_rest2
              by (simp, case_tac "(((None, s_cnv2, s_cnv1), (s_krn2, s_act2), s_krn1, s_act1), ())" rule: basic_core_oracle_usr_base.cases) (auto split: option.splits)
            subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 x s_act1 s_act2 s_rest1 s_rest2
              by (simp, case_tac "(((Some x, s_cnv2, s_cnv1), (s_krn2, s_act2), s_krn1, s_act1), ())" rule: basic_core_oracle_usr_base.cases) (auto split: option.splits)
            done
          done
        subgoal for q_usr_rest
          apply (cases q_usr_rest)
          subgoal for q_act
            apply (cases q_act)
            subgoal for a_alice by (erule S_ic_cases) simp_all
            subgoal for a_bob by (erule S_ic_cases) simp_all
            done
          subgoal for q_urest
            apply (cases q_urest)
            subgoal for q_urest1 by (erule S_ic_cases) simp_all
            subgoal for q_urest2 by (erule S_ic_cases) simp_all
            done
          done
        done
      done
    subgoal State_OK for sl sr q
      apply (cases q)
      subgoal for q_adv
        apply (cases q_adv)
        subgoal for q_adv_core
          apply (cases q_adv_core)
          subgoal for q_acore1
            apply (cases q_acore1)
            subgoal for q_drop by (erule S_ic_cases) simp_all
            subgoal for q_lfe
              apply (cases q_lfe)
              subgoal for q_look
                apply (erule S_ic_cases)
                subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 s_act1 s_act2 s_rest1 s_rest2
                  apply (simp, case_tac "(Inl (), (None, s_krn1, s_act1))" rule: interceptor_base_look.cases)
                         apply (simp_all add: map_spmf_conv_bind_spmf[symmetric])
                  by (auto simp add: map_spmf_conv_bind_spmf[symmetric] cond_spmf_fst_def vimage_def intro!: trace_eq_simcl_map S_ic_intros)
                subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 x s_act1 s_act2 s_rest1 s_rest2
                  apply (simp, case_tac "(Inl (), (Some x, s_krn1, s_act1))" rule: interceptor_base_look.cases)
                  by (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro!: S_ic_intros)
                done
              subgoal for q_fedit
                apply (erule S_ic_cases)
                subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 s_act1 s_act2 s_rest1 s_rest2
                  by (simp, case_tac "(Inl (), (None, s_krn1, s_act1), Inr (Inr q_fedit))" rule: basic_core_oracle_adv.cases)
                    (auto simp add: map_spmf_conv_bind_spmf[symmetric]  intro!: trace_eq_simcl.base S_ic_intros)
                subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 x s_act1 s_act2 s_rest1 s_rest2
                  by (simp, case_tac "(Inl (), (Some x, s_krn1, s_act1), Inr (Inr q_fedit))" rule: basic_core_oracle_adv.cases)
                    (auto simp add: map_spmf_conv_bind_spmf[symmetric]  intro!: trace_eq_simcl.base S_ic_intros)
                done
              done
            done
          subgoal for q_acore2
            apply (cases q_acore2)
            subgoal for q_drop by (erule S_ic_cases) simp_all
            subgoal for q_lfe
              apply (cases q_lfe)
              subgoal for q_look
                apply (erule S_ic_cases)
                subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 s_act1 s_act2 s_rest1 s_rest2
                  apply (simp, case_tac "(Inr (), (None, s_krn2, s_act2))" rule: interceptor_base_look.cases)
                         apply (simp_all add: map_spmf_conv_bind_spmf[symmetric])
                  by (auto simp add: map_spmf_conv_bind_spmf[symmetric] cond_spmf_fst_def vimage_def intro!: trace_eq_simcl_map S_ic_intros)
                subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 x s_act1 s_act2 s_rest1 s_rest2
                  apply (simp, case_tac "(Inr (), (Some x, s_krn2, s_act2))" rule: interceptor_base_look.cases)
                  by (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro!: S_ic_intros)
                done
              subgoal for q_fedit
                apply (erule S_ic_cases)
                subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 s_act1 s_act2 s_rest1 s_rest2
                  by (simp, case_tac "(Inr (), (None, s_krn2, s_act2), Inr (Inr q_fedit))" rule: basic_core_oracle_adv.cases)
                    (auto simp add: map_spmf_conv_bind_spmf[symmetric]  intro!: trace_eq_simcl.base S_ic_intros)
                subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 x s_act1 s_act2 s_rest1 s_rest2
                  by (simp, case_tac "(Inr (), (Some x, s_krn2, s_act2), Inr (Inr q_fedit))" rule: basic_core_oracle_adv.cases)
                    (auto simp add: map_spmf_conv_bind_spmf[symmetric]  intro!: trace_eq_simcl.base S_ic_intros)
                done
              done
            done
          done
        subgoal for q_adv_rest
          apply (cases q_adv_rest)
          subgoal for q_urest1
            apply (erule S_ic_cases)
            subgoal
              apply clarsimp
              apply (subst bind_commute_spmf)
              apply (subst (2) bind_commute_spmf)
              apply (subst (1 2) cond_spmf_fst_bind)
              apply (subst (1 2) cond_spmf_fst_bind)
              apply (clarsimp intro!: trace_eq_simcl_bind simp add: auth_poke_alt set_scale_spmf split: if_split_asm)
              apply (subst (asm) (1 2 3 4) foldl_spmf_helper2[where acc="return_spmf _" and q="\<lambda>(_, (_, x), _). x"
                    and p="\<lambda>(a, (b, _), d). (a, b, d)" and f="\<lambda>(a, b, d) c. (a, (b, c), d)", simplified])
              by (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric] intro!: trace_eq_simcl.base S_ic_intros)
            subgoal
              apply clarsimp
              apply (subst (1 2) cond_spmf_fst_bind)
              apply (subst (1 2) cond_spmf_fst_bind)
              apply (clarsimp intro!: trace_eq_simcl_bind simp add: auth_poke_alt set_scale_spmf split: if_split_asm)
              apply (subst (asm) (1 2 3 4) foldl_spmf_helper2[where acc="return_spmf _" and q="\<lambda>(_, (_, x), _). x"
                    and p="\<lambda>(a, (b, _), d). (a, b, d)" and f="\<lambda>(a, b, d) c. (a, (b, c), d)", simplified])
              by (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric] intro!: S_ic_intros)
            done
          subgoal for q_urest2
            apply (erule S_ic_cases)
            subgoal
              apply clarsimp
              apply (subst bind_commute_spmf)
              apply (subst (2) bind_commute_spmf)
              apply (subst (1 2) cond_spmf_fst_bind)
              apply (subst (1 2) cond_spmf_fst_bind)
              apply (clarsimp intro!: trace_eq_simcl_bind simp add: auth_poke_alt set_scale_spmf split: if_split_asm)
              apply (subst (asm) (1 2 3 4) foldl_spmf_helper2[where acc="return_spmf _" and q="\<lambda>(_, _, _, x). x"
                    and p="\<lambda>(a, b, c, _). (a, b, c)" and f="\<lambda>(a, b, c) d. (a, b, c, d)", simplified])
              by (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric] intro!: trace_eq_simcl.base S_ic_intros)
            subgoal
              apply clarsimp
              apply (subst (1 2) cond_spmf_fst_bind)
              apply (subst (1 2) cond_spmf_fst_bind)
              apply (clarsimp intro!: trace_eq_simcl_bind simp add: auth_poke_alt set_scale_spmf split: if_split_asm)
              apply (subst (asm) (1 2 3 4) foldl_spmf_helper2[where acc="return_spmf _" and q="\<lambda>(_, _, _, x). x"
                    and p="\<lambda>(a, b, c, _). (a, b, c)" and f="\<lambda>(a, b, c) d. (a, b, c, d)", simplified])
              by (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric] intro!: S_ic_intros)
            done
          done
        done
      subgoal for q_usr
        apply (cases q_usr)
        subgoal for q_usr_core
          apply (cases q_usr_core)
          subgoal for q_alice
            apply (erule S_ic_cases)
            subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 s_act1 s_act2 s_rest1 s_rest2
              apply (simp, case_tac "(((None, s_cnv1, s_cnv2), (s_krn1, s_act1), s_krn2, s_act2), ())" rule: basic_core_oracle_usr_base.cases)
            proof (goal_cases)
              case (1 s_key _ s_cnv2 s_auth1 _ parties2 _)
              then show ?case by (auto simp add: map_spmf_conv_bind_spmf[symmetric] cond_spmf_fst_def vimage_def intro!: trace_eq_simcl_map S_ic_intros)
            qed (auto simp add: map_spmf_conv_bind_spmf[symmetric]  intro!: trace_eq_simcl.base S_ic_intros)
            subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 x s_act1 s_act2 s_rest1 s_rest2
              apply (simp, case_tac "(((Some x, s_cnv1, s_cnv2), (s_krn1, s_act1), s_krn2, s_act2), ())" rule: basic_core_oracle_usr_base.cases)
              by (auto simp add: map_spmf_conv_bind_spmf[symmetric]  intro!: trace_eq_simcl.base S_ic_intros)
            done
          subgoal for q_bob
            apply (erule S_ic_cases)
            subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 s_act1 s_act2 s_rest1 s_rest2
              apply (simp, case_tac "(((None, s_cnv2, s_cnv1), (s_krn2, s_act2), s_krn1, s_act1), ())" rule: basic_core_oracle_usr_base.cases)
            proof (goal_cases)
              case (1 s_key _ s_cnv2 s_auth1 _ parties2 _)
              then show ?case by (auto simp add: map_spmf_conv_bind_spmf[symmetric] cond_spmf_fst_def vimage_def intro!: trace_eq_simcl_map S_ic_intros)
            qed (auto simp add: map_spmf_conv_bind_spmf[symmetric]  intro!: trace_eq_simcl.base S_ic_intros)
            subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 x s_act1 s_act2 s_rest1 s_rest2
              apply (simp, case_tac "(((Some x, s_cnv2, s_cnv1), (s_krn2, s_act2), s_krn1, s_act1), ())" rule: basic_core_oracle_usr_base.cases)
              by (auto simp add: map_spmf_conv_bind_spmf[symmetric]  intro!: trace_eq_simcl.base S_ic_intros)
            done
          done
        subgoal for q_usr_rest
          apply (cases q_usr_rest)
          subgoal for q_act
            apply (cases q_act)
            subgoal for a_alice
              apply (erule S_ic_cases)
              subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 s_act1 s_act2 s_rest1 s_rest2
                apply (simp, case_tac "(((None, s_cnv1, s_cnv2), (s_krn1, s_act1), s_krn2, s_act2), ())" rule: basic_core_helper_base.cases)
                by (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro!: trace_eq_simcl.base S_ic_intros)
              subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 x s_act1 s_act2 s_rest1 s_rest2
                apply (simp, case_tac "(((Some x, s_cnv1, s_cnv2), (s_krn1, s_act1), s_krn2, s_act2), ())" rule: basic_core_helper_base.cases)
                by (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro!: trace_eq_simcl.base S_ic_intros)
              done
            subgoal for a_bob
              apply (erule S_ic_cases)
              subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 s_act1 s_act2 s_rest1 s_rest2
                apply (simp, case_tac "(((None, s_cnv2, s_cnv1), (s_krn2, s_act2), s_krn1, s_act1), ())" rule: basic_core_helper_base.cases)
                by (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro!: trace_eq_simcl.base S_ic_intros)
              subgoal for s_cnv1 s_cnv2 s_krn1 s_krn2 x s_act1 s_act2 s_rest1 s_rest2
                apply (simp, case_tac "(((Some x, s_cnv2, s_cnv1), (s_krn2, s_act2), s_krn1, s_act1), ())" rule: basic_core_helper_base.cases)
                by (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro!: trace_eq_simcl.base S_ic_intros)
              done
            done
          subgoal for q_urest
            apply (cases q_urest)
            subgoal for q_urest1
              apply (erule S_ic_cases)
              subgoal
                apply clarsimp
                apply (subst bind_commute_spmf)
                apply (subst (2) bind_commute_spmf)
                apply (subst (1 2) cond_spmf_fst_bind)
                apply (subst (1 2) cond_spmf_fst_bind)
                apply (clarsimp intro!: trace_eq_simcl_bind simp add: auth_poke_alt set_scale_spmf split: if_split_asm)
                apply (subst (asm) (1 2 3 4) foldl_spmf_helper2[where acc="return_spmf _" and q="\<lambda>(_, (_, x), _). x"
                      and p="\<lambda>(a, (b, _), d). (a, b, d)" and f="\<lambda>(a, b, d) c. (a, (b, c), d)", simplified])
                by (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric] intro!: trace_eq_simcl.base S_ic_intros)
              subgoal
                apply clarsimp
                apply (subst (1 2) cond_spmf_fst_bind)
                apply (subst (1 2) cond_spmf_fst_bind)
                apply (clarsimp intro!: trace_eq_simcl_bind simp add: auth_poke_alt set_scale_spmf split: if_split_asm)
                apply (subst (asm) (1 2 3 4) foldl_spmf_helper2[where acc="return_spmf _" and q="\<lambda>(_, (_, x), _). x"
                      and p="\<lambda>(a, (b, _), d). (a, b, d)" and f="\<lambda>(a, b, d) c. (a, (b, c), d)", simplified])
                by (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric] intro!: S_ic_intros)
              done
            subgoal for q_urest2
              apply (erule S_ic_cases)
              subgoal
                apply clarsimp
                apply (subst bind_commute_spmf)
                apply (subst (2) bind_commute_spmf)
                apply (subst (1 2) cond_spmf_fst_bind)
                apply (subst (1 2) cond_spmf_fst_bind)
                apply (clarsimp intro!: trace_eq_simcl_bind simp add: auth_poke_alt set_scale_spmf split: if_split_asm)
                apply (subst (asm) (1 2 3 4) foldl_spmf_helper2[where acc="return_spmf _" and q="\<lambda>(_, _, _, x). x"
                      and p="\<lambda>(a, b, c, _). (a, b, c)" and f="\<lambda>(a, b, c) d. (a, b, c, d)", simplified])
                by (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric] intro!: trace_eq_simcl.base S_ic_intros)
              subgoal
                apply clarsimp
                apply (subst (1 2) cond_spmf_fst_bind)
                apply (subst (1 2) cond_spmf_fst_bind)
                apply (clarsimp intro!: trace_eq_simcl_bind simp add: auth_poke_alt set_scale_spmf split: if_split_asm)
                apply (subst (asm) (1 2 3 4) foldl_spmf_helper2[where acc="return_spmf _" and q="\<lambda>(_, _, _, x). x"
                      and p="\<lambda>(a, b, c, _). (a, b, c)" and f="\<lambda>(a, b, c) d. (a, b, c, d)", simplified])
                by (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric] intro!: S_ic_intros)
              done
            done
          done
        done
      done
    done

  then show ?thesis by simp
qed

private abbreviation "dummy x \<equiv> TRY map_spmf OK x ELSE return_spmf Fault" 

lemma reduction: "advantage D (obsf_resource (RES (fused_resource.fuse (lazy_core DH1_sample) lazy_rest) (basic_core_sinit, basic_rest_sinit)))
  (obsf_resource (RES (fused_resource.fuse (lazy_core DH0_sample) lazy_rest) (basic_core_sinit, basic_rest_sinit))) = ddh.advantage \<G> (DH_adversary D)"
proof -
  have fact1: "bind_spmf (DH0_sample) A = do {
    x \<leftarrow> sample_uniform (order \<G>);
    y \<leftarrow> sample_uniform (order \<G>);
    (DH_adversary_curry A) (\<^bold>g [^] x) (\<^bold>g [^] y) (\<^bold>g [^] (x * y)) 
  }" for A by (simp add: DH0_sample_def DH_adversary_curry_def nat_pow_pow)

  have fact2: "bind_spmf DH1_sample A = do {
    x \<leftarrow> sample_uniform (order \<G>);
    y \<leftarrow> sample_uniform (order \<G>);
    z \<leftarrow> sample_uniform (order \<G>);
    (DH_adversary_curry A) (\<^bold>g [^] x) (\<^bold>g [^] y) (\<^bold>g [^] (z)) 
  }" for A by (simp add: DH1_sample_def DH_adversary_curry_def)

  {
    fix sample_triple :: "('grp \<times> 'grp \<times> 'grp) spmf"
    assume *: "lossless_spmf sample_triple"
    define s_init where "s_init \<equiv> (basic_core_sinit, basic_rest_sinit)"
    have [unfolded s_init_def, simp]: "dummy (dummy (return_spmf s_init)) = return_spmf (OK (OK s_init))" by auto
    have [unfolded s_init_def, simp]: "dummy (dummy (pair_spmf sample_triple (return_spmf s_init))) =
      map_spmf (OK \<circ> OK) (pair_spmf sample_triple (return_spmf s_init))"
      using * by (simp add: o_def map_spmf_conv_bind_spmf pair_spmf_alt_def)

    have "connect D (RES (obsf_oracle (obsf_oracle (fused_resource.fuse (lazy_core sample_triple) lazy_rest))) (OK (OK (basic_core_sinit, basic_rest_sinit)))) = 
      bind_spmf (map_spmf (OK o OK) (pair_spmf sample_triple (return_spmf (basic_core_sinit, basic_rest_sinit)))) 
        (run_gpv (obsf_oracle (obsf_oracle (\<lambda>(tpl, s) q. map_spmf ((apsnd (Pair tpl)) o fst) (exec_gpv (\<lambda>_ _. return_spmf (tpl, ())) (interceptor s q) ())))) D)" for D
      apply (simp add: connect_def exec_gpv_resource_of_oracle spmf.map_comp)
    apply (subst return_bind_spmf[where x="OK (OK (basic_core_sinit, basic_rest_sinit))", symmetric])
    apply (rule trace_callee_eq_run_gpv[where ?I1.0="(\<lambda>_. True)" and ?I2.0="(\<lambda>_. True)" and \<I>=\<I>_full and A=UNIV])
    subgoal by (rule trace_eq_intercept[OF *, THEN trace_callee_eq_obsf_oracleI, THEN trace_callee_eq_obsf_oracleI, simplified])
    by (simp_all add: * pair_spmf_alt_def)
  } note detach_sampler  = this
  
  show ?thesis
    unfolding advantage_def
    apply (subst (1 2) spmf_obsf_distinguisher_obsf_resource_True[symmetric])
    apply (subst (1 2) obsf_resource_of_oracle)+
    by (simp add: detach_sampler pair_spmf_alt_def bind_map_spmf fact1 fact2)
      (simp add: ddh.advantage_def ddh.ddh_0_def ddh.ddh_1_def DH_adversary_def)
qed

end


subsection \<open>Proving the trace-equivalence of simplified Ideal and Lazy constructions\<close>

context
begin

private abbreviation "isample_nat \<equiv> sample_uniform (order \<G>)"
private abbreviation "isample_key \<equiv> spmf_of_set (carrier \<G>)"
private abbreviation "isample_pair_nn \<equiv> pair_spmf isample_nat isample_nat"
private abbreviation "isample_pair_nk \<equiv> pair_spmf isample_nat isample_key"

private inductive S_il :: "(('grp astate \<times> unit) \<times> estate \<times> 'grp key.state) spmf \<Rightarrow> 'grp bc_state spmf \<Rightarrow> bool"
  where
\<comment> \<open>(Auth1 =a)@(Auth2 =0)\<close>
    sil_0_0: "S_il (return_spmf ((None, ()), (False, (EState_Void, s_act1), EState_Void, s_act2), key.PState_Store, {}))
      (return_spmf ((None, CState_Void, CState_Void), (auth.State_Void, s_act1), auth.State_Void, s_act2))"
\<comment> \<open>../(Auth1 =a)@(Auth2 =0) \# wl\<close>
  | sil_1_0: "S_il (return_spmf ((None, ()), (False, (EState_Store, s_act1), EState_Void, s_act2), key.PState_Store, {}))
      (return_spmf ((None, CState_Half 0, CState_Void), (auth.State_Store \<one>, s_act1), auth.State_Void, s_act2))"
  if "auth.Alice \<in> s_act1"
  | sil_2_0: "S_il (map_spmf (\<lambda>k. ((None, ()), (True, (EState_Collect, s_act1), EState_Void, s_act2), key.State_Store k, {})) isample_key)
      (return_spmf ((None, CState_Half 0, CState_Void), (auth.State_Collect \<one>, s_act1), auth.State_Void, s_act2))"
  if "auth.Alice \<in> s_act1"
\<comment> \<open>../(Auth1 =a)@(Auth2 =0) \# look\<close>
  | sil_1'_0: "S_il (map_spmf (\<lambda>y. ((Some (\<^bold>g [^] x, \<^bold>g [^] y), ()), (False, (EState_Store, s_act1), EState_Void, s_act2), key.PState_Store, {})) isample_nat)
      (map_spmf (\<lambda>yz. ((Some (\<^bold>g [^] snd yz, \<^bold>g [^] (x :: nat), \<^bold>g [^] fst yz), CState_Half 0, CState_Void), (auth.State_Store \<one>, s_act1), auth.State_Void, s_act2)) isample_pair_nn)"
  if "auth.Alice \<in> s_act1" 
  | sil_2'_0: "S_il (map_spmf (\<lambda>yk. ((Some (\<^bold>g [^] x, \<^bold>g [^] fst yk), ()), (True, (EState_Collect, s_act1), EState_Void, s_act2), key.State_Store (snd yk), {})) isample_pair_nk)
      (map_spmf (\<lambda>yz. ((Some (\<^bold>g [^] snd yz, \<^bold>g [^] (x :: nat), \<^bold>g [^] fst yz), CState_Half 0, CState_Void), (auth.State_Collect \<one>, s_act1), auth.State_Void, s_act2)) isample_pair_nn)"
  if "auth.Alice \<in> s_act1" 
\<comment> \<open>(Auth1 =a)@(Auth2 =1)\<close>
  | sil_0_1: "S_il (return_spmf ((None, ()), (False, (EState_Void, s_act1), EState_Store, s_act2), key.PState_Store, {}))
      (return_spmf ((None, CState_Void, CState_Half 0), (auth.State_Void, s_act1), auth.State_Store \<one>, s_act2))"
  if "auth.Alice \<in> s_act2"
\<comment> \<open>../(Auth1 =a)@(Auth2 =1) \# wl\<close>
  | sil_1_1: "S_il (return_spmf ((None, ()), (False, (EState_Store, s_act1), EState_Store, s_act2), key.PState_Store, {}))
      (return_spmf ((None, CState_Half 0, CState_Half 0), (auth.State_Store \<one>, s_act1), auth.State_Store \<one>, s_act2))"
  if "auth.Alice \<in> s_act1" and "auth.Alice \<in> s_act2"
  | sil_2_1: "S_il (map_spmf (\<lambda>k.  ((None, ()), (True, (EState_Collect, s_act1), EState_Store, s_act2), key.State_Store k, s_actk)) isample_key)
      (return_spmf ((None, CState_Half 0, CState_Half 0), (auth.State_Collect \<one>, s_act1), auth.State_Store \<one>, s_act2))"
  if "auth.Alice \<in> s_act1" and "auth.Alice \<in> s_act2" and "key.Alice \<notin> s_actk" and "auth.Bob \<in> s_act1 \<longleftrightarrow> key.Bob \<in> s_actk"
  | sil_3_1: "S_il (return_spmf ((None, ()), (True, (EState_Collect, s_act1), EState_Store, s_act2), key.State_Store k, s_actk))
      (map_spmf (\<lambda>xy. ((Some (\<^bold>g [^] (z :: nat),  \<^bold>g [^] fst xy,  \<^bold>g [^] snd xy), CState_Half 0, CState_Full (0, \<one>)), (auth.State_Collected, s_act1), auth.State_Store \<one>, s_act2)) isample_pair_nn)"
  if "auth.Alice \<in> s_act1" and "auth.Alice \<in> s_act2" and "key.Alice \<notin> s_actk" and "auth.Bob \<in> s_act1" and "key.Bob \<in> s_actk" and "k = \<^bold>g [^] z"
\<comment> \<open>../(Auth1 =a)@(Auth2 =1) \# look\<close>
  | sil_1c_1c: "S_il (return_spmf ((Some (\<^bold>g [^] x, \<^bold>g [^] y), ()), (False, (EState_Store, s_act1), EState_Store, s_act2), key.PState_Store, {}))
      (map_spmf (\<lambda>z. ((Some (\<^bold>g [^] z, \<^bold>g [^] (x :: nat), \<^bold>g [^] (y :: nat)), CState_Half 0, CState_Half 0), (auth.State_Store \<one>, s_act1), auth.State_Store \<one>, s_act2)) isample_nat)"
  if "auth.Alice \<in> s_act1" and "auth.Alice \<in> s_act2"
  | sil_2c_1c: "S_il (return_spmf ((Some (\<^bold>g [^] x, \<^bold>g [^] y), ()), (True, (EState_Collect, s_act1), EState_Store, s_act2), key.State_Store k, s_actk))
      (return_spmf ((Some (\<^bold>g [^] z, \<^bold>g [^] (x :: nat), \<^bold>g [^] (y :: nat)), CState_Half 0, CState_Half 0), (auth.State_Collect \<one>, s_act1), auth.State_Store \<one>, s_act2))"
  if "auth.Alice \<in> s_act1" and "auth.Alice \<in> s_act2" and "key.Alice \<notin> s_actk" and "auth.Bob \<in> s_act1 \<longleftrightarrow> key.Bob \<in> s_actk" and  "k = \<^bold>g [^] z" and "z \<in> set_spmf isample_nat"
  | sil_3c_1c: "S_il (return_spmf ((Some (\<^bold>g [^] x, \<^bold>g [^] y), ()), (True, (EState_Collect, s_act1), EState_Store, s_act2), key.State_Store k, s_actk))
      (return_spmf ((Some (\<^bold>g [^] (z :: nat), \<^bold>g [^] (x :: nat), \<^bold>g [^] (y :: nat)), CState_Half 0, CState_Full (0, \<one>)), (auth.State_Collected, s_act1), auth.State_Store \<one>, s_act2))"
  if "auth.Alice \<in> s_act1" and "auth.Alice \<in> s_act2" and "key.Alice \<notin> s_actk" and "auth.Bob \<in> s_act1" and "key.Bob \<in> s_actk" and "k = \<^bold>g [^] z"
\<comment> \<open>(Auth1 =a)@(Auth2 =2)\<close>
  | sil_0_2: "S_il (map_spmf (\<lambda>k. ((None, ()), (True, (EState_Void, s_act1), EState_Collect, s_act2), key.State_Store k, {})) isample_key)
      (return_spmf ((None, CState_Void, CState_Half 0), (auth.State_Void, s_act1), auth.State_Collect \<one>, s_act2))"
  if "auth.Alice \<in> s_act2"
\<comment> \<open>../(Auth1 =a)@(Auth2 =2) \# wl\<close>
  | sil_1_2: "S_il (map_spmf (\<lambda>k. ((None, ()), (True, (EState_Store, s_act1), EState_Collect, s_act2), key.State_Store k, s_actk)) isample_key)
      (return_spmf ((None, CState_Half 0, CState_Half 0), (auth.State_Store \<one>, s_act1), auth.State_Collect \<one>, s_act2))"
  if "auth.Alice \<in> s_act1" and "auth.Alice \<in> s_act2" and "auth.Bob \<in> s_act2 \<longleftrightarrow> key.Alice \<in> s_actk" and "key.Bob \<notin> s_actk"
  | sil_2_2: "S_il (map_spmf (\<lambda>k. ((None, ()), (True, (EState_Collect, s_act1), EState_Collect, s_act2), key.State_Store k, s_actk)) isample_key)
      (return_spmf ((None, CState_Half 0, CState_Half 0), (auth.State_Collect \<one>, s_act1), auth.State_Collect \<one>, s_act2))"
  if "auth.Alice \<in> s_act1" and "auth.Alice \<in> s_act2" and "auth.Bob \<in> s_act2 \<longleftrightarrow> key.Alice \<in> s_actk" and "auth.Bob \<in> s_act1 \<longleftrightarrow> key.Bob \<in> s_actk"
  | sil_3_2: "S_il (return_spmf ((None, ()), (True, (EState_Collect, s_act1), EState_Collect, s_act2), key.State_Store k, s_actk))
      (map_spmf (\<lambda>xy. ((Some (\<^bold>g [^] (z :: nat),  \<^bold>g [^] fst xy,  \<^bold>g [^] snd xy), CState_Half 0, CState_Full (0, \<one>)), (auth.State_Collected, s_act1), auth.State_Collect \<one>, s_act2)) isample_pair_nn)"
  if "auth.Alice \<in> s_act1" and "auth.Alice \<in> s_act2" and "auth.Bob \<in> s_act2 \<longleftrightarrow> key.Alice \<in> s_actk" and "auth.Bob \<in> s_act1" and "key.Bob \<in> s_actk" and "k = \<^bold>g [^] z"
\<comment> \<open>../(Auth1 =a)@(Auth2 =2) \# look\<close>
  | sil_1c_2c: "S_il (return_spmf ((Some (\<^bold>g [^] x, \<^bold>g [^] y), ()), (True, (EState_Store, s_act1), EState_Collect, s_act2), key.State_Store k, s_actk))
      (return_spmf ((Some (\<^bold>g [^] z, \<^bold>g [^] (x :: nat), \<^bold>g [^] (y :: nat)), CState_Half 0, CState_Half 0), (auth.State_Store \<one>, s_act1), auth.State_Collect \<one>, s_act2))"
  if "auth.Alice \<in> s_act1" and "auth.Alice \<in> s_act2" and "auth.Bob \<in> s_act2 \<longleftrightarrow> key.Alice \<in> s_actk" and "key.Bob \<notin> s_actk" and "k = \<^bold>g [^] z" and "z \<in> set_spmf isample_nat"
  | sil_2c_2c: "S_il (return_spmf ((Some (\<^bold>g [^] x, \<^bold>g [^] y), ()), (True, (EState_Collect, s_act1), EState_Collect, s_act2), key.State_Store k, s_actk))
      (return_spmf ((Some (\<^bold>g [^] z, \<^bold>g [^] (x :: nat), \<^bold>g [^] (y :: nat)), CState_Half 0, CState_Half 0), (auth.State_Collect \<one>, s_act1), auth.State_Collect \<one>, s_act2))"
  if "auth.Alice \<in> s_act1" and "auth.Alice \<in> s_act2" and "auth.Bob \<in> s_act2 \<longleftrightarrow> key.Alice \<in> s_actk" and "auth.Bob \<in> s_act1 \<longleftrightarrow> key.Bob \<in> s_actk" and "k = \<^bold>g [^] z" and "z \<in> set_spmf isample_nat"
  | sil_3c_2c: "S_il (return_spmf ((Some (\<^bold>g [^] x, \<^bold>g [^] y), ()), (True, (EState_Collect, s_act1), EState_Collect, s_act2), key.State_Store k, s_actk))
      (return_spmf ((Some (\<^bold>g [^] (z :: nat), \<^bold>g [^] (x :: nat), \<^bold>g [^] (y :: nat)), CState_Half 0, CState_Full (0, \<one>)), (auth.State_Collected, s_act1), auth.State_Collect \<one>, s_act2))"
  if "auth.Alice \<in> s_act1" and "auth.Alice \<in> s_act2" and "auth.Bob \<in> s_act2 \<longleftrightarrow> key.Alice \<in> s_actk" and "auth.Bob \<in> s_act1" and "key.Bob \<in> s_actk" and "k = \<^bold>g [^] z"
\<comment> \<open>(Auth1 =a)@(Auth2 =3)\<close>
\<comment> \<open>../(Auth1 =a)@(Auth2 =3) \# wl\<close>
  | sil_1_3: "S_il (return_spmf ((None, ()), (True, (EState_Store, s_act1), EState_Collect, s_act2), key.State_Store k, s_actk))
        (map_spmf (\<lambda>xy. ((Some (\<^bold>g [^] (z :: nat), \<^bold>g [^] fst xy, \<^bold>g [^] snd xy), CState_Full (0, \<one>), CState_Half 0), (auth.State_Store \<one>, s_act1), auth.State_Collected, s_act2)) isample_pair_nn)"
  if "auth.Alice \<in> s_act1" and "auth.Alice \<in> s_act2" and "auth.Bob \<in> s_act2" and "key.Alice \<in> s_actk" and "key.Bob \<notin> s_actk" and "k = \<^bold>g [^] z"
  | sil_2_3: "S_il (return_spmf ((None, ()), (True, (EState_Collect, s_act1), EState_Collect, s_act2), key.State_Store k, s_actk))
        (map_spmf (\<lambda>xy. ((Some (\<^bold>g [^] (z :: nat), \<^bold>g [^] fst xy, \<^bold>g [^] snd xy), CState_Full (0, \<one>), CState_Half 0), (auth.State_Collect \<one>, s_act1), auth.State_Collected, s_act2)) isample_pair_nn)"
  if "auth.Alice \<in> s_act1" and "auth.Alice \<in> s_act2" and "auth.Bob \<in> s_act2" and "key.Alice \<in> s_actk" and "auth.Bob \<in> s_act1 \<longleftrightarrow> key.Bob \<in> s_actk" and "k = \<^bold>g [^] z"
  | sil_3_3: "S_il (return_spmf ((None, ()), (True, (EState_Collect, s_act1), EState_Collect, s_act2), key.State_Store k, s_actk))
        (map_spmf (\<lambda>xy. ((Some (\<^bold>g [^] (z :: nat), \<^bold>g [^] fst xy, \<^bold>g [^] snd xy), CState_Full (0, \<one>), CState_Full (0, \<one>)), (auth.State_Collected, s_act1), auth.State_Collected, s_act2)) isample_pair_nn)"
  if "auth.Alice \<in> s_act1" and "auth.Alice \<in> s_act2" and "auth.Bob \<in> s_act2" and "key.Alice \<in> s_actk" and "auth.Bob \<in> s_act1" and "key.Bob \<in> s_actk" and "k = \<^bold>g [^] z"
\<comment> \<open>../(Auth1 =a)@(Auth2 =3) \# look\<close>
  | sil_1c_3c: "S_il (return_spmf ((Some (\<^bold>g [^] x, \<^bold>g [^] y), ()), (True, (EState_Store, s_act1), EState_Collect, s_act2), key.State_Store k, s_actk))
      (return_spmf ((Some (\<^bold>g [^] (z :: nat), \<^bold>g [^] (x :: nat), \<^bold>g [^] (y :: nat)), CState_Full (0, \<one>), CState_Half 0), (auth.State_Store \<one>, s_act1), auth.State_Collected, s_act2))"
  if "auth.Alice \<in> s_act1" and "auth.Alice \<in> s_act2" and "auth.Bob \<in> s_act2" and "key.Alice \<in> s_actk" and "key.Bob \<notin> s_actk" and "k = \<^bold>g [^] z"
  | sil_2c_3c: "S_il (return_spmf ((Some (\<^bold>g [^] x, \<^bold>g [^] y), ()), (True, (EState_Collect, s_act1), EState_Collect, s_act2), key.State_Store k, s_actk))
      (return_spmf ((Some (\<^bold>g [^] (z :: nat), \<^bold>g [^] (x :: nat), \<^bold>g [^] (y :: nat)), CState_Full (0, \<one>), CState_Half 0), (auth.State_Collect \<one>, s_act1), auth.State_Collected, s_act2))"
  if "auth.Alice \<in> s_act1" and "auth.Alice \<in> s_act2" and "auth.Bob \<in> s_act2" and "key.Alice \<in> s_actk" and "auth.Bob \<in> s_act1 \<longleftrightarrow> key.Bob \<in> s_actk" and "k = \<^bold>g [^] z"
  | sil_3c_3c: "S_il (return_spmf ((Some (\<^bold>g [^] x, \<^bold>g [^] y), ()), (True, (EState_Collect, s_act1), EState_Collect, s_act2), key.State_Store k, s_actk))
      (return_spmf ((Some (\<^bold>g [^] (z :: nat), \<^bold>g [^] (x :: nat), \<^bold>g [^] (y :: nat)), CState_Full (0, \<one>), CState_Full (0, \<one>)), (auth.State_Collected, s_act1), auth.State_Collected, s_act2))"
  if "auth.Alice \<in> s_act1" and "auth.Alice \<in> s_act2" and "auth.Bob \<in> s_act2" and "key.Alice \<in> s_actk" and "auth.Bob \<in> s_act1" and "key.Bob \<in> s_actk" and "k = \<^bold>g [^] z"
\<comment> \<open>(Auth1 =a)@(Auth2 =1')\<close>
  | sil_0_1': "S_il (map_spmf (\<lambda>x. ((Some (\<^bold>g [^] x, \<^bold>g [^] y), ()), (False, (EState_Void, s_act1), EState_Store, s_act2), key.PState_Store, {})) isample_nat)
      (map_spmf (\<lambda>xz. ((Some (\<^bold>g [^] snd xz, \<^bold>g [^] fst xz, \<^bold>g [^] (y :: nat)), CState_Void, CState_Half 0), (auth.State_Void, s_act1), auth.State_Store \<one>, s_act2)) isample_pair_nn)"
  if "auth.Alice \<in> s_act2" 
\<comment> \<open>(Auth1 =a)@(Auth2 =2')\<close>
  | sil_0_2': "S_il (map_spmf (\<lambda>xk. ((Some (\<^bold>g [^] fst xk, \<^bold>g [^] y), ()), (True, (EState_Void, s_act1), EState_Collect, s_act2), key.State_Store (snd xk), {})) isample_pair_nk)
      (map_spmf (\<lambda>xz. ((Some (\<^bold>g [^] snd xz, \<^bold>g [^] fst xz, \<^bold>g [^] (y :: nat)), CState_Void, CState_Half 0), (auth.State_Void, s_act1), auth.State_Collect \<one>, s_act2)) isample_pair_nn)"
  if "auth.Alice \<in> s_act2" 
  
private lemma trac_eq_core_il: "trace_core_eq  ideal_core' (lazy_core DH1_sample)
  ((UNIV <+> UNIV) <+> UNIV <+> UNIV) ((UNIV <+> UNIV <+> UNIV) <+> UNIV <+> UNIV <+> UNIV) (UNIV <+> UNIV)     
  (return_spmf ideal_s_core') (return_spmf basic_core_sinit)"
proof -
  have isample_key_conv_nat[simplified map_spmf_conv_bind_spmf]: 
    "map_spmf f isample_key = map_spmf (\<lambda>x. f (\<^bold>g [^] x)) isample_nat" for f
    unfolding sample_uniform_def carrier_conv_generator
    by (simp add: map_spmf_of_set_inj_on[OF inj_on_generator, symmetric] spmf.map_comp o_def)

  have [simp]: "weight_spmf isample_nat = 1"
    by (simp add: finite_carrier order_gt_0_iff_finite)

  have [simp]: "weight_spmf isample_key = 1"
    by (simp add: carrier_not_empty cyclic_group.finite_carrier cyclic_group_axioms)

  have [simp]: "mk_lossless isample_nat = isample_nat"
    by (simp add: mk_lossless_def)

  have [simp]: "mk_lossless isample_pair_nn = isample_pair_nn"
    by (simp add: mk_lossless_def)

  have [simp]: "mk_lossless isample_pair_nk = isample_pair_nk"
    by (simp add: mk_lossless_def)

  note [simp] = basic_core_helper_def basic_core_oracle_usr_def eleak_def DH1_sample_def
    Let_def split_def exec_gpv_bind spmf.map_comp o_def map_bind_spmf bind_map_spmf bind_spmf_const

  show ?thesis
    apply (rule trace_core_eq_simI_upto[where S=S_il])
    subgoal Init_OK
      by (simp add: ideal_s_core'_def einit_def sil_0_0)
    subgoal POut_OK for sl sr query 
      apply (cases query)
      subgoal for e_usrs
        apply (cases e_usrs)
        subgoal for e_alice by (erule S_il.cases) (auto simp add: map_spmf_conv_bind_spmf[symmetric])
        subgoal for e_bob by (erule S_il.cases) (auto simp add: map_spmf_conv_bind_spmf[symmetric])
        done
      subgoal for e_chns
        apply (cases e_chns)
        subgoal for e_chn1
          apply (cases e_chn1)
          subgoal for e_shell
            apply (cases e_shell)
            subgoal a_alice by (erule S_il.cases) (auto simp add: map_spmf_conv_bind_spmf[symmetric])
            subgoal a_bob by (erule S_il.cases) (auto simp add: map_spmf_conv_bind_spmf[symmetric])
            done
          done
        subgoal for e_chn2
          apply (cases e_chn2)
          subgoal for e_shell
            apply (cases e_shell)
            subgoal a_alice by (erule S_il.cases) (auto simp add: map_spmf_conv_bind_spmf[symmetric])
            subgoal a_bob by (erule S_il.cases) (auto simp add: map_spmf_conv_bind_spmf[symmetric])
            done
          done
        done
      done
    subgoal PState_OK for sl sr query
      apply (cases query)
      subgoal for e_usrs
        apply (cases e_usrs)
        subgoal for e_alice
        proof (erule S_il.cases, goal_cases)
          case (26 s_act2 y s_act1)  \<comment> \<open>Corresponds to @{thm [source] sil_0_1'}\<close>
          then show ?case 
            apply (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric])
            apply (simp add: pair_spmf_alt_def map_spmf_conv_bind_spmf)
            apply (rule trace_eq_simcl_bindI)
            by (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: S_il.intros)
        next
          case (27 s_act2 y s_act1)  \<comment> \<open>Corresponds to @{thm [source] sil_0_2'}\<close>
          then show ?case 
            apply (clarsimp simp add: pair_spmf_alt_def isample_key_conv_nat)
            apply (simp add: bind_bind_conv_pair_spmf)
             by (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro!: S_il.intros trace_eq_simcl_map)
        qed (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: S_il.intros trace_eq_simcl.base)
        subgoal for e_bob
        proof (erule S_il.cases, goal_cases)
          case (4 s_act1 x s_act2)  \<comment> \<open>Corresponds to @{thm [source] sil_1'_0}\<close>
          then show ?case
            apply (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric])
            apply (simp add: pair_spmf_alt_def map_spmf_conv_bind_spmf)
            apply (rule trace_eq_simcl_bindI)
            by (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: S_il.intros)
        next
          case (5 s_act1 x s_act2)  \<comment> \<open>Corresponds to @{thm [source] sil_2'_0}\<close>
          then show ?case 
            apply (clarsimp simp add: pair_spmf_alt_def isample_key_conv_nat)
            apply (simp add: bind_bind_conv_pair_spmf)
            by (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro!: S_il.intros trace_eq_simcl_map)
        qed (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: S_il.intros trace_eq_simcl.base)
        done
      subgoal for e_chns
        apply (cases e_chns)
        subgoal for e_auth1
          apply (cases e_auth1)
          subgoal for e_shell
            apply (cases e_shell)
            subgoal a_alice by (erule S_il.cases) (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: S_il.intros trace_eq_simcl.base)
            subgoal a_bob by (erule S_il.cases) (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: S_il.intros trace_eq_simcl.base)
            done
          done
        subgoal for e_auth2
          apply (cases e_auth2)
          subgoal for e_shell
            apply (cases e_shell)
            subgoal a_alice by (erule S_il.cases) (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: S_il.intros trace_eq_simcl.base)
            subgoal a_bob by (erule S_il.cases) (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: S_il.intros trace_eq_simcl.base)
            done
          done
        done
      done
    subgoal AOut_OK for sl sr query
      apply (cases query)
      subgoal for q_auth1
        apply (cases q_auth1)
        subgoal for q_drop by (erule S_il.cases) (auto simp add: map_spmf_conv_bind_spmf[symmetric])
        subgoal for q_lfe
          apply (cases q_lfe)
          subgoal for q_look by (erule S_il.cases) (simp_all del: bind_spmf_const add: pair_spmf_alt_def, clarsimp+)
          subgoal for q_fedit by (erule S_il.cases) (simp_all del: bind_spmf_const add: pair_spmf_alt_def, clarsimp+)
          done
        done
      subgoal for q_auth2
        apply (cases q_auth2)
        subgoal for q_drop by (erule S_il.cases) (auto simp add: map_spmf_conv_bind_spmf[symmetric])
        subgoal for q_lfe
          apply (cases q_lfe)
          subgoal for q_look by (erule S_il.cases) (simp_all del: bind_spmf_const add: pair_spmf_alt_def, clarsimp+)
          subgoal for q_fedit by (erule S_il.cases) (simp_all del: bind_spmf_const add: pair_spmf_alt_def, clarsimp+)
          done
        done
      done
    subgoal AState_OK for sl sr query
      apply (cases query)
      subgoal for q_auth1
        apply (cases q_auth1)
        subgoal for q_drop by (erule S_il.cases) auto
        subgoal for q_lfe
          apply (cases q_lfe)
          subgoal for q_look
          proof (erule S_il.cases, goal_cases)
            case (2 s_act1 s_act2)  \<comment> \<open>Corresponds to @{thm [source] sil_1_0}\<close>
            then show ?case 
              apply simp
              apply (subst (1 2 3) bind_bind_conv_pair_spmf)
              apply (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric])
              apply (subst (1 2) cond_spmf_fst_pair_spmf1[unfolded map_prod_def split_def])
              by (auto intro: trace_eq_simcl_bindI S_il.intros)
          next
            case (7 s_act1 s_act2)  \<comment> \<open>Corresponds to @{thm [source] sil_1_1}\<close>
            then show ?case 
              apply simp
              apply (subst (1 2 3) bind_bind_conv_pair_spmf)
              apply (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric])
              apply (subst (1 2) cond_spmf_fst_pair_spmf1[unfolded map_prod_def split_def])
              apply(subst (1 2) cond_spmf_fst_map_Pair1; simp add: inj_on_def)
              apply (subst (1 2) inv_into_f_f)
                  apply (simp_all add: inj_on_def map_spmf_conv_bind_spmf pair_spmf_alt_def isample_key_conv_nat)
              apply (rule trace_eq_simcl_bindI)
              by (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: S_il.intros)
          next
            case (14 s_act1 s_act2 s_actk)  \<comment> \<open>Corresponds to @{thm [source] sil_1_2}\<close>
            then show ?case 
              apply clarsimp
              apply (subst bind_commute_spmf, subst (2) bind_commute_spmf)
              apply (subst (1 2 3 4) bind_bind_conv_pair_spmf)
              apply (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric])
              apply (subst (1 2) cond_spmf_fst_pair_spmf1[unfolded map_prod_def split_def])
              apply(subst (1 2) cond_spmf_fst_map_Pair1; simp add: inj_on_def)
              apply (subst (1 2) inv_into_f_f)
                  apply (simp_all add: inj_on_def map_spmf_conv_bind_spmf pair_spmf_alt_def isample_key_conv_nat)
              apply (subst (1 2) bind_bind_conv_pair_spmf)
              by (auto intro!: trace_eq_simcl_bindI S_il.intros)
          next
            case (20 s_act1 s_act2 s_actk k z)  \<comment> \<open>Corresponds to @{thm [source] sil_1_3}\<close>
            then show ?case 
              apply simp
              apply (subst bind_bind_conv_pair_spmf)
              apply (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric])
              apply (subst (1 2) cond_spmf_fst_pair_spmf1[unfolded map_prod_def split_def])
              apply(subst (1 2) cond_spmf_fst_map_Pair1; simp add: inj_on_def)
              apply (subst (1 2) inv_into_f_f)
                apply (simp_all add: inj_on_def map_spmf_conv_bind_spmf)
              by (auto intro!: trace_eq_simcl_bindI S_il.intros)
          qed (auto simp add: map_spmf_conv_bind_spmf,
            auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: S_il.intros trace_eq_simcl.base)
          subgoal for q_fedit
          proof (erule S_il.cases, goal_cases)
            case (4 s_act1 x s_act2)  \<comment> \<open>Corresponds to @{thm [source] sil_1'_0}\<close>
            then show ?case 
              apply simp
              apply (subst bind_bind_conv_pair_spmf)
              apply (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric])
              by (auto intro: S_il.intros trace_eq_simcl.base)
          next
            case (10 s_act1 s_act2 x y)  \<comment> \<open>Corresponds to @{thm [source] sil_1c_1c}\<close>
            then show ?case 
              apply (clarsimp simp add: pair_spmf_alt_def isample_key_conv_nat)
              apply (simp add: map_spmf_conv_bind_spmf[symmetric])
              by (auto intro!: trace_eq_simcl_map S_il.intros)
          qed (auto simp add: map_spmf_conv_bind_spmf[symmetric],
              auto intro: S_il.intros trace_eq_simcl.base trace_eq_simcl_map)
          done
        done
      subgoal for q_auth2
        apply (cases q_auth2)
        subgoal for q_drop by (erule S_il.cases) auto
        subgoal for q_lfe
          apply (cases q_lfe)
          subgoal for q_look
          proof (erule S_il.cases, goal_cases)
            case (6 s_act2 s_act1)  \<comment> \<open>Corresponds to @{thm [source] sil_0_1}\<close>
            then show ?case
              apply clarsimp
              apply (subst (1 2) bind_commute_spmf)
              apply (subst (1 3) bind_bind_conv_pair_spmf)
              apply (subst bind_bind_conv_pair_spmf)
              apply (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric])
              apply (subst (1 2) cond_spmf_fst_pair_spmf1[unfolded map_prod_def split_def])
              by (auto intro: trace_eq_simcl_bindI S_il.intros)
          next
            case (7 s_act1 s_act2)  \<comment> \<open>Corresponds to @{thm [source] sil_1_1}\<close>
            then show ?case 
              apply clarsimp
              apply (subst (1 2) bind_commute_spmf)
              apply (subst (1 3) bind_bind_conv_pair_spmf)
              apply (subst bind_bind_conv_pair_spmf)
              apply (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric])
              apply (subst (1 2) cond_spmf_fst_pair_spmf1[unfolded map_prod_def split_def])
              apply(subst (1 2) cond_spmf_fst_map_Pair1; simp add: inj_on_def)
              apply (subst (1 2) inv_into_f_f)
                  apply (simp_all add: inj_on_def map_spmf_conv_bind_spmf)
              apply (subst pair_spmf_alt_def)
              apply (subst bind_spmf_assoc)
              apply (rule trace_eq_simcl_bindI)
              by (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: S_il.intros)
          next
            case (8 s_act1 s_act2 s_actk)  \<comment> \<open>Corresponds to @{thm [source] sil_2_1}\<close>
            then show ?case 
              apply clarsimp
              apply (subst (2) bind_commute_spmf, subst (1 3) bind_commute_spmf)
              apply (subst (2) bind_commute_spmf)
              apply (subst (2 4) bind_bind_conv_pair_spmf)
              apply (clarsimp simp add: bind_bind_conv_pair_spmf)
              apply (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric])
              apply (subst (1 2) cond_spmf_fst_pair_spmf1[unfolded map_prod_def split_def])
              apply(subst (1 2) cond_spmf_fst_map_Pair1; simp add: inj_on_def)
              apply (subst (1 2) inv_into_f_f)
                  apply (simp_all add: inj_on_def map_spmf_conv_bind_spmf)
              apply (simp add: pair_spmf_alt_def isample_key_conv_nat)
              apply (subst (1 2) bind_bind_conv_pair_spmf)
              by (auto intro!: trace_eq_simcl_bindI S_il.intros)
          next
            case (9 s_act1 s_act2 s_actk k z)  \<comment> \<open>Corresponds to @{thm [source] sil_3_1}\<close>
            then show ?case 
              apply (clarsimp simp del: bind_spmf_const simp add: pair_spmf_alt_def)
              apply (subst (1 2) bind_commute_spmf)
              apply (subst (1 2) bind_bind_conv_pair_spmf)
              apply (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric])
              apply (subst (1 2) cond_spmf_fst_pair_spmf1[unfolded map_prod_def split_def])
              apply(subst (1 2) cond_spmf_fst_map_Pair1; simp add: inj_on_def)
              apply (subst (1 2) inv_into_f_f)
                apply (simp_all add: inj_on_def map_spmf_conv_bind_spmf)
              by (auto intro: trace_eq_simcl_bindI S_il.intros)
          qed (auto simp del: bind_spmf_const simp add: map_spmf_conv_bind_spmf, 
              auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: S_il.intros trace_eq_simcl.base)
          subgoal for q_fedit
          proof (erule S_il.cases, goal_cases)
            case (10 s_act1 s_act2 x y)  \<comment> \<open>Corresponds to @{thm [source] sil_1c_1c}\<close>
            then show ?case 
              apply simp
              apply (clarsimp simp add: map_spmf_conv_bind_spmf pair_spmf_alt_def isample_key_conv_nat)
              apply (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric])
              by (auto intro!: S_il.intros trace_eq_simcl_map)
          next
            case (26 s_act2 y s_act1)  \<comment> \<open>Corresponds to @{thm [source] sil_0_1'}\<close>
            then show ?case 
              apply simp
              apply (subst bind_bind_conv_pair_spmf)
              apply (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric])
              by (auto intro: S_il.intros trace_eq_simcl.base)
          qed (auto simp add: map_spmf_conv_bind_spmf[symmetric],
              auto intro: S_il.intros trace_eq_simcl.base trace_eq_simcl_map)
          done
        done
      done
    subgoal UOut_OK for sl sr query
      apply (cases query)
      subgoal for q_alice
        apply (erule S_il.cases)
        by (auto simp add: pair_spmf_alt_def isample_key_conv_nat)
      subgoal for q_bob
        apply (erule S_il.cases)
        by (auto simp add: pair_spmf_alt_def isample_key_conv_nat)
      done
    subgoal UState_OK for sl sr query
      apply (cases query)
      subgoal for q_alice
      proof (erule S_il.cases, goal_cases)
        case (14 s_act1 s_act2 s_actk)  \<comment> \<open>Corresponds to @{thm [source] sil_1_2}\<close>
        then show ?case 
          apply (clarsimp)
          apply (subst (2) bind_commute_spmf, subst bind_commute_spmf)
          apply (subst bind_bind_conv_pair_spmf, subst bind_bind_conv_pair_spmf)
          apply (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric])
          apply (subst cond_spmf_fst_pair_spmf1[unfolded map_prod_def split_def])
          apply(subst (1 2) cond_spmf_fst_map_Pair1; simp add: inj_on_def)
          apply(subst (1 2) inv_into_f_f)
          by (auto simp add: inj_on_def intro: S_il.intros trace_eq_simcl.base)
      next
        case (15 s_act1 s_act2 s_actk)  \<comment> \<open>Corresponds to @{thm [source] sil_2_2}\<close>
        then show ?case 
          apply (clarsimp)
          apply (subst (2) bind_commute_spmf, subst bind_commute_spmf)
          apply (subst bind_bind_conv_pair_spmf, subst bind_bind_conv_pair_spmf)
          apply (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric])
          apply (subst cond_spmf_fst_pair_spmf1[unfolded map_prod_def split_def])
          apply(subst (1 2) cond_spmf_fst_map_Pair1; simp add: inj_on_def)
          apply(subst (1 2) inv_into_f_f)
          by (auto simp add: inj_on_def intro: S_il.intros trace_eq_simcl.base)
      qed (auto simp add: map_spmf_conv_bind_spmf[symmetric],
          auto intro: S_il.intros trace_eq_simcl.base trace_eq_simcl_map)
      subgoal for q_bob
      proof (erule S_il.cases, goal_cases)
        case (8 s_act1 s_act2 s_actk)  \<comment> \<open>Corresponds to @{thm [source] sil_2_1}\<close>
        then show ?case 
          apply clarsimp
          apply (subst (2) bind_commute_spmf, subst bind_commute_spmf)
          apply (subst (2) bind_bind_conv_pair_spmf, subst bind_bind_conv_pair_spmf)
          apply (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric])
          apply (subst cond_spmf_fst_pair_spmf1[unfolded map_prod_def split_def])
          apply (subst (1 2) cond_spmf_fst_map_Pair1; simp add: inj_on_def)
          apply (subst (1 2) inv_into_f_f)
          by (auto simp add: inj_on_def intro: S_il.intros trace_eq_simcl.base)
      next
        case (15 s_act1 s_act2 s_actk)  \<comment> \<open>Corresponds to @{thm [source] sil_2_2}\<close>
        then show ?case 
          apply clarsimp
          apply (subst (2) bind_commute_spmf, subst bind_commute_spmf)
          apply (subst (2) bind_bind_conv_pair_spmf, subst bind_bind_conv_pair_spmf)
          apply (clarsimp simp add: map_spmf_conv_bind_spmf[symmetric])
          apply (subst cond_spmf_fst_pair_spmf1[unfolded map_prod_def split_def])
          apply (subst (1 2) cond_spmf_fst_map_Pair1; simp add: inj_on_def)
          apply (subst (1 2) inv_into_f_f)
          by (auto simp add: inj_on_def intro: S_il.intros trace_eq_simcl.base)
      qed(auto simp add: map_spmf_conv_bind_spmf[symmetric],
          auto intro: S_il.intros trace_eq_simcl.base trace_eq_simcl_map)
      done
    done
qed

lemma connect_ideal: "connect D (obsf_resource ideal_resource) = 
  connect D (obsf_resource (RES (fused_resource.fuse (lazy_core DH1_sample) lazy_rest) (basic_core_sinit, basic_rest_sinit)))"
proof -
  have fact1: "trace_rest_eq ideal_rest' ideal_rest' UNIV UNIV s s" for s
    by (rule rel_rest'_into_trace_rest_eq[where S="(=)" and M="(=)"]) (simp_all add: eq_onp_def rel_rest'_eq)

  have fact2: "\<I>_full \<oplus>\<^sub>\<I> \<I>_full \<turnstile>c callee_of_rest ideal_rest' s \<surd>" for s
    by (rule WT_calleeI) (cases s, case_tac call, rename_tac [!] x, case_tac [!] x,  auto)

  have fact3: "\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<turnstile>c callee_of_core ideal_core' s \<surd>" for s
    by (rule WT_calleeI) (cases s, case_tac call, rename_tac [!] x, case_tac [!] x,  auto)

  have fact4: "\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<turnstile>c callee_of_core (lazy_core xyz) s \<surd>" for xyz s
    by (rule WT_calleeI) (cases s, case_tac call, rename_tac [!] x, case_tac [!] x,  auto)

  show ?thesis
    apply (rule connect_cong_trace[where A="UNIV" and \<I>=\<I>_full])
    apply (rule trace_eq_obsf_resourceI)
    subgoal
      apply (simp add: attach_ideal)
      apply (rule fuse_trace_eq[where \<I>E=\<I>_full and \<I>CA=\<I>_full and \<I>CU=\<I>_full and \<I>RA=\<I>_full and \<I>RU=\<I>_full, simplified])
      by (simp_all add: ideal_s_rest'_def lazy_rest_def trac_eq_core_il[simplified] fact1 fact2 fact3 fact4)
    by (simp_all add: attach_ideal)
qed


end


subsection \<open>Proving the trace-equivalence of simplified Real and Lazy constructions\<close>

context
begin

private abbreviation "rsample_nat \<equiv> sample_uniform (order \<G>)"
private abbreviation "rsample_pair_nn \<equiv> pair_spmf rsample_nat rsample_nat"

private inductive S_rl :: "((unit \<times> 'grp cstate \<times> 'grp cstate) \<times> 'grp auth.state \<times> 'grp auth.state) spmf
  \<Rightarrow> (('grp st_state \<times> 'grp cstate \<times> 'grp cstate) \<times>  'grp auth.state \<times> 'grp auth.state) spmf \<Rightarrow> bool"
  where
\<comment> \<open>(Auth1 =a)@(Auth2 =0)\<close>
    srl_0_0: "S_rl (return_spmf (((), CState_Void, CState_Void), (auth.State_Void, s_act1), auth.State_Void, s_act2))
      (return_spmf ((None, CState_Void, CState_Void), (auth.State_Void, s_act1), (auth.State_Void, s_act2)))"
\<comment> \<open>../(Auth1 =a)@(Auth2 =0) \# wl\<close>
  | srl_1_0: "S_rl (map_spmf (\<lambda>x. (((), CState_Half x, CState_Void), (auth.State_Store (\<^bold>g [^] x), s_act1), auth.State_Void, s_act2)) rsample_nat)
      (return_spmf ((None, CState_Half 0, CState_Void), (auth.State_Store \<one>, s_act1), auth.State_Void, s_act2))"
  | srl_2_0: "S_rl (map_spmf (\<lambda>x. (((), CState_Half x, CState_Void), (auth.State_Collect (\<^bold>g [^] x), s_act1), auth.State_Void, s_act2)) rsample_nat)
      (return_spmf ((None, CState_Half 0, CState_Void), (auth.State_Collect \<one>, s_act1), auth.State_Void, s_act2))"
\<comment> \<open>../(Auth1 =a)@(Auth2 =0) \# look\<close>
  | srl_1'_0: "S_rl (return_spmf (((), CState_Half x, CState_Void), (auth.State_Store (\<^bold>g [^] x), s_act1), auth.State_Void, s_act2))
      (map_spmf (\<lambda>y. ((Some ((\<^bold>g [^] x) [^] y, \<^bold>g [^] x, \<^bold>g [^] y), CState_Half 0, CState_Void), (auth.State_Store \<one>, s_act1), auth.State_Void, s_act2)) rsample_nat)"
  | srl_2'_0: "S_rl (return_spmf (((), CState_Half x, CState_Void), (auth.State_Collect (\<^bold>g [^] x), s_act1), auth.State_Void, s_act2))
      (map_spmf (\<lambda>y. ((Some ((\<^bold>g [^] x) [^] y, \<^bold>g [^] x, \<^bold>g [^] y), CState_Half 0, CState_Void), (auth.State_Collect \<one>, s_act1), auth.State_Void, s_act2)) rsample_nat)"
\<comment> \<open>(Auth1 =a)@(Auth2 =1)\<close>
  | srl_0_1: "S_rl (map_spmf (\<lambda>y. (((), CState_Void, CState_Half y), (auth.State_Void, s_act1), auth.State_Store (\<^bold>g [^] y), s_act2)) rsample_nat)
      (return_spmf ((None, CState_Void, CState_Half 0), (auth.State_Void, s_act1), auth.State_Store \<one>, s_act2))"
\<comment> \<open>../(Auth1 =a)@(Auth2 =1) \# wl\<close>
  | srl_1_1: "S_rl (map_spmf (\<lambda>yx. (((), CState_Half (snd yx), CState_Half (fst yx)), (auth.State_Store (\<^bold>g [^] snd yx), s_act1), auth.State_Store (\<^bold>g [^] fst yx), s_act2)) rsample_pair_nn)
      (return_spmf ((None, CState_Half 0, CState_Half 0), (auth.State_Store \<one>, s_act1), auth.State_Store \<one>, s_act2))"
  | srl_2_1: "S_rl (map_spmf (\<lambda>yx. (((), CState_Half (snd yx), CState_Half (fst yx)), (auth.State_Collect (\<^bold>g [^] snd yx), s_act1), auth.State_Store (\<^bold>g [^] fst yx), s_act2)) rsample_pair_nn)
      (return_spmf ((None, CState_Half 0, CState_Half 0), (auth.State_Collect \<one>, s_act1), auth.State_Store \<one>, s_act2))"
\<comment> \<open>../(Auth1 =a)@(Auth2 =1) \# look\<close>
  | srl_1c_1c: "S_rl (return_spmf (((), CState_Half x, CState_Half y), (auth.State_Store (\<^bold>g [^] x), s_act1), auth.State_Store (\<^bold>g [^] y), s_act2))
      (return_spmf ((Some ((\<^bold>g [^] x) [^] y, \<^bold>g [^] x, \<^bold>g [^] y), CState_Half 0, CState_Half 0), (auth.State_Store \<one>, s_act1), auth.State_Store \<one>, s_act2))"
  | srl_2c_1c: "S_rl (return_spmf (((), CState_Half x, CState_Half y), (auth.State_Collect (\<^bold>g [^] x), s_act1), auth.State_Store (\<^bold>g [^] y), s_act2))
      (return_spmf ((Some ((\<^bold>g [^] x) [^] y, \<^bold>g [^] x, \<^bold>g [^] y), CState_Half 0, CState_Half 0), (auth.State_Collect \<one>, s_act1), auth.State_Store \<one>, s_act2))"
  | srl_3c_1c: "S_rl (return_spmf (((), CState_Half x, CState_Full (y, z)), (auth.State_Collected, s_act1), auth.State_Store (\<^bold>g [^] y), s_act2))
      (return_spmf ((Some (z, \<^bold>g [^] x, \<^bold>g [^] y), CState_Half 0, CState_Full (0, \<one>)), (auth.State_Collected, s_act1), auth.State_Store \<one>, s_act2))"
  if "z = (\<^bold>g [^] x) [^] y"
\<comment> \<open>(Auth1 =a)@(Auth2 =2)\<close>
  | srl_0_2: "S_rl (map_spmf (\<lambda>y. (((), CState_Void, CState_Half y), (auth.State_Void, s_act1), auth.State_Collect (\<^bold>g [^] y), s_act2)) rsample_nat)
      (return_spmf ((None, CState_Void, CState_Half 0), (auth.State_Void, s_act1), auth.State_Collect \<one>, s_act2))"
\<comment> \<open>../(Auth1 =a)@(Auth2 =2) \# wl\<close>
  | srl_1_2: "S_rl (map_spmf (\<lambda>yx. (((), CState_Half (snd yx), CState_Half (fst yx)), (auth.State_Store (\<^bold>g [^] snd yx), s_act1), auth.State_Collect (\<^bold>g [^] fst yx), s_act2)) rsample_pair_nn)
      (return_spmf ((None, CState_Half 0, CState_Half 0), (auth.State_Store \<one>, s_act1), auth.State_Collect \<one>, s_act2))"
  | srl_2_2: "S_rl (map_spmf (\<lambda>yx. (((), CState_Half (snd yx), CState_Half (fst yx)), (auth.State_Collect (\<^bold>g [^] snd yx), s_act1), auth.State_Collect (\<^bold>g [^] fst yx), s_act2)) rsample_pair_nn)
      (return_spmf ((None, CState_Half 0, CState_Half 0), (auth.State_Collect \<one>, s_act1), auth.State_Collect \<one>, s_act2))"
\<comment> \<open>../(Auth1 =a)@(Auth2 =2) \# look\<close>
  | srl_1c_2c: "S_rl (return_spmf (((), CState_Half x, CState_Half y), (auth.State_Store (\<^bold>g [^] x), s_act1), auth.State_Collect (\<^bold>g [^] y), s_act2))
      (return_spmf ((Some ((\<^bold>g [^] x) [^] y, \<^bold>g [^] x, \<^bold>g [^] y), CState_Half 0, CState_Half 0), (auth.State_Store \<one>, s_act1), auth.State_Collect \<one>, s_act2))"
  | srl_2c_2c: "S_rl (return_spmf (((), CState_Half x, CState_Half y), (auth.State_Collect (\<^bold>g [^] x), s_act1), auth.State_Collect (\<^bold>g [^] y), s_act2))
      (return_spmf ((Some ((\<^bold>g [^] x) [^] y, \<^bold>g [^] x, \<^bold>g [^] y), CState_Half 0, CState_Half 0), (auth.State_Collect \<one>, s_act1), auth.State_Collect \<one>, s_act2))"
  | srl_3c_2c: "S_rl (return_spmf (((), CState_Half x, CState_Full (y, z)), (auth.State_Collected, s_act1), auth.State_Collect (\<^bold>g [^] y), s_act2))
      (return_spmf ((Some (z, \<^bold>g [^] x, \<^bold>g [^] y), CState_Half 0, CState_Full (0, \<one>)), (auth.State_Collected, s_act1), auth.State_Collect \<one>, s_act2))"
  if "z = (\<^bold>g [^] x) [^] y"
\<comment> \<open>(Auth1 =a)@(Auth2 =3)\<close>
  | srl_1c_3c: "S_rl (return_spmf (((), CState_Full (x, z), CState_Half y), (auth.State_Store (\<^bold>g [^] x), s_act1), auth.State_Collected, s_act2))
      (return_spmf ((Some (z, \<^bold>g [^] x, \<^bold>g [^] y), CState_Full (0, \<one>), CState_Half 0), (auth.State_Store \<one>, s_act1), auth.State_Collected, s_act2))"
  if "z = (\<^bold>g [^] y) [^] x"
  | srl_2c_3c: "S_rl (return_spmf (((), CState_Full (x, z), CState_Half y), (auth.State_Collect (\<^bold>g [^] x), s_act1), auth.State_Collected, s_act2))
      (return_spmf ((Some (z, \<^bold>g [^] x, \<^bold>g [^] y), CState_Full (0, \<one>), CState_Half 0), (auth.State_Collect \<one>, s_act1), auth.State_Collected, s_act2))"
  if "z = (\<^bold>g [^] y) [^] x"
  | srl_3c_3c: "S_rl (return_spmf (((), CState_Full (x, z), CState_Full (y, z)), (auth.State_Collected, s_act1), auth.State_Collected, s_act2))
      (return_spmf ((Some (z, \<^bold>g [^] x, \<^bold>g [^] y), CState_Full (0, \<one>), CState_Full (0, \<one>)), (auth.State_Collected, s_act1), auth.State_Collected, s_act2))"
  if "z = (\<^bold>g [^] y) [^] x"
\<comment> \<open>(Auth1 =0)@(Auth2 =1')\<close>  
  | srl_0_1': "S_rl (return_spmf (((), CState_Void, CState_Half y), (auth.State_Void, s_act1), auth.State_Store (\<^bold>g [^] y), s_act2))
      (map_spmf (\<lambda>x. ((Some ((\<^bold>g [^] x) [^] y, \<^bold>g [^] x, \<^bold>g [^] y), CState_Void, CState_Half 0), (auth.State_Void, s_act1), auth.State_Store \<one>, s_act2)) rsample_nat)"
\<comment> \<open>(Auth1 =0)@(Auth2 =2')\<close>
  | srl_0_2': "S_rl (return_spmf (((), CState_Void, CState_Half y), (auth.State_Void, s_act1), auth.State_Collect (\<^bold>g [^] y), s_act2))
      (map_spmf (\<lambda>x. ((Some ((\<^bold>g [^] x) [^] y, \<^bold>g [^] x, \<^bold>g [^] y), CState_Void, CState_Half 0), (auth.State_Void, s_act1), auth.State_Collect \<one>, s_act2)) rsample_nat)"


private lemma trac_eq_core_rl: "trace_core_eq real_core' (basic_core DH0_sample)
  (UNIV <+> UNIV) ((UNIV <+> UNIV <+> UNIV) <+> UNIV <+> UNIV <+> UNIV) ((UNIV <+> UNIV) <+> UNIV <+> UNIV) 
  (return_spmf real_s_core') (return_spmf basic_core_sinit)"
proof -
  have power_commute: "(\<^bold>g [^] x) [^] (y :: nat) = (\<^bold>g [^] y) [^] (x :: nat)" for x y
    by (simp add: nat_pow_pow mult.commute)

  have [simp]: "weight_spmf rsample_nat = 1"
    by (simp add: finite_carrier order_gt_0_iff_finite)

  have [simp]: "mk_lossless rsample_nat = rsample_nat"
    by (simp add: mk_lossless_def)

  have [simp]: "mk_lossless rsample_pair_nn = rsample_pair_nn"
    by (simp add: mk_lossless_def)

  note [simp] = basic_core_oracle_usr_def basic_core_helper_def
    exec_gpv_bind spmf.map_comp map_bind_spmf bind_map_spmf bind_spmf_const o_def Let_def split_def

  show ?thesis 
    apply (rule trace_core_eq_simI_upto[where S=S_rl])
    subgoal Init_OK 
      by (simp add: real_s_core'_def srl_0_0)
    subgoal POut_OK for s_l s_r query
      apply (cases query)
      subgoal for e_auth1 by (cases e_auth1; erule S_rl.cases; auto simp add: map_spmf_conv_bind_spmf[symmetric] split!: if_splits)
      subgoal for e_auth2 by (cases e_auth2; erule S_rl.cases; auto simp add: map_spmf_conv_bind_spmf[symmetric] split!: if_splits)
      done
    subgoal PState_OK for s_l s_r query
      apply (cases query)
      subgoal for e_auth1 by(cases e_auth1; erule S_rl.cases; auto simp add: map_spmf_conv_bind_spmf[symmetric] split!: if_splits intro: S_rl.intros trace_eq_simcl.base)
      subgoal for e_auth2 by (cases e_auth2; erule S_rl.cases; auto simp add: map_spmf_conv_bind_spmf[symmetric] split!: if_splits intro: S_rl.intros trace_eq_simcl.base)
      done
    subgoal AOut_OK for sl sr q  
      apply (cases q)
      subgoal for q_auth1
        apply (cases q_auth1)
        subgoal for q_drop by (erule S_rl.cases; simp)
        subgoal for q_lfe
          apply (cases q_lfe)
          subgoal for q_look by(erule S_rl.cases; auto simp add: DH0_sample_def pair_spmf_alt_def)
          subgoal for q_fedit by (cases q_fedit; erule S_rl.cases; auto simp add: DH0_sample_def pair_spmf_alt_def)
          done
        done
      subgoal for q_auth2
        apply (cases q_auth2)
        subgoal for q_drop by (erule S_rl.cases; simp)
        subgoal for q_lfe
          apply (cases q_lfe)
          subgoal for q_look by(erule S_rl.cases; auto simp add: DH0_sample_def pair_spmf_alt_def)
          subgoal for q_fedit by (cases q_fedit; erule S_rl.cases; auto simp add: DH0_sample_def pair_spmf_alt_def)
          done
        done
      done
    subgoal AState_OK for sl sr q s1 s2 s1' s2' oa 
      apply (cases q)
      subgoal for q_auth1
        apply (cases q_auth1)
        subgoal for q_drop by (erule S_rl.cases; simp)
        subgoal for q_lfe
          apply (cases q_lfe)
          subgoal for q_look
          proof (erule S_rl.cases, goal_cases)
            case (2 s_act1 s_act2) \<comment> \<open>Corresponds to @{thm [source] srl_1_0}\<close>
            then show ?case 
              apply(cases s1')
              apply (clarsimp simp add: DH0_sample_def)
              apply(simp add: bind_bind_conv_pair_spmf)
              apply(simp add: map_spmf_conv_bind_spmf[symmetric])
              apply (subst cond_spmf_fst_pair_spmf1[unfolded map_prod_def split_def])
              apply(simp)
              apply(subst (1 2) cond_spmf_fst_map_Pair1; simp add: inj_on_def)
              by(subst (1 2 3 4) inv_into_f_f; simp add: inj_on_def trace_eq_simcl.base S_rl.intros)
          next
            case (4 x s_act1 s_act2) \<comment> \<open>Corresponds to @{thm [source] srl_1'_0}\<close>
            then show ?case 
              by(auto simp add: DH0_sample_def map_spmf_conv_bind_spmf[symmetric] intro!: trace_eq_simcl.base S_rl.intros)
          next
            case (7 s_act1 s_act2) \<comment> \<open>Corresponds to @{thm [source] srl_1_1}\<close>
            then show ?case 
               apply(clarsimp simp add: DH0_sample_def pair_spmf_alt_def)
              apply(subst bind_commute_spmf)
              apply(simp add: bind_bind_conv_pair_spmf)
              apply(simp add: map_spmf_conv_bind_spmf[symmetric])
              apply (subst (1 2) cond_spmf_fst_pair_spmf1[unfolded map_prod_def split_def])
              apply(simp)
              apply(subst (1 2) cond_spmf_fst_map_Pair1; simp add: inj_on_def)
              by (subst (1 2 3 4) inv_into_f_f; simp add: inj_on_def trace_eq_simcl_map S_rl.intros)
          next
            case (13 s_act1 s_act2) \<comment> \<open>Corresponds to @{thm [source] srl_1_2}\<close>
            then show ?case 
              apply(clarsimp simp add: DH0_sample_def pair_spmf_alt_def)
              apply(subst bind_commute_spmf)
              apply(simp add: bind_bind_conv_pair_spmf)
              apply(simp add: map_spmf_conv_bind_spmf[symmetric])
              apply (subst (1 2) cond_spmf_fst_pair_spmf1[unfolded map_prod_def split_def])
              apply(simp)
              apply(subst (1 2) cond_spmf_fst_map_Pair1; simp add: inj_on_def)
              by(subst (1 2 3 4) inv_into_f_f; simp add: inj_on_def trace_eq_simcl_map S_rl.intros)
          qed (auto intro: S_rl.intros)
          subgoal for q_fedit
            apply (cases q_fedit)
            by (erule S_rl.cases, goal_cases) (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro!: trace_eq_simcl.base intro: S_rl.intros)            
          done
        done
      subgoal for q_auth2
        apply (cases q_auth2)
        subgoal for q_drop by (erule S_rl.cases; simp)
        subgoal for q_lfe
          apply (cases q_lfe)
          subgoal for q_look
          proof (erule S_rl.cases, goal_cases)
            case (6 s_act1 s_act2) \<comment> \<open>Corresponds to @{thm [source] srl_0_1}\<close>
            then show ?case 
              apply(clarsimp simp add: DH0_sample_def)
              apply(subst bind_commute_spmf)
              apply(simp add: bind_bind_conv_pair_spmf)
              apply(simp add: map_spmf_conv_bind_spmf[symmetric])
              apply(subst cond_spmf_fst_pair_spmf1[simplified map_prod_def split_def])
              apply(simp)
              apply(subst (1 2) cond_spmf_fst_map_Pair1; simp add: inj_on_def)
              by(subst (1 2 3 4) inv_into_f_f; simp add: inj_on_def trace_eq_simcl.base S_rl.intros)
          next
            case (7 s_act1 s_act2) \<comment> \<open>Corresponds to @{thm [source] srl_1_1}\<close>
            then show ?case
              apply(clarsimp simp add: DH0_sample_def)
              apply(subst bind_commute_spmf)
              apply(simp add: bind_bind_conv_pair_spmf)
              apply(simp add: map_spmf_conv_bind_spmf[symmetric])
              apply(subst (1 2) cond_spmf_fst_pair_spmf1[simplified map_prod_def split_def])
              apply(simp)
              apply(subst (1 2) cond_spmf_fst_map_Pair1; simp add: inj_on_def)
              by(subst (1 2 3 4) inv_into_f_f; simp add: inj_on_def trace_eq_simcl_map S_rl.intros)
          next
            case (8 s_act1 s_act2) \<comment> \<open>Corresponds to @{thm [source] srl_2_1}\<close>
            then show ?case 
              apply(clarsimp simp add: DH0_sample_def)
              apply(subst bind_commute_spmf)
              apply(simp add: bind_bind_conv_pair_spmf)
              apply(simp add: map_spmf_conv_bind_spmf[symmetric])
              apply(subst (1 2) cond_spmf_fst_pair_spmf1[simplified map_prod_def split_def])
              apply(simp)
              apply(subst (1 2) cond_spmf_fst_map_Pair1; simp add: inj_on_def)
              by(subst (1 2 3 4) inv_into_f_f; simp add: inj_on_def trace_eq_simcl_map S_rl.intros)
          next
            case (21 y s_act1 s_act2) \<comment> \<open>Corresponds to @{thm [source] srl_0_1'}\<close>
            then show ?case 
              by(auto simp add: map_spmf_conv_bind_spmf[symmetric] intro!: trace_eq_simcl.base intro: S_rl.intros)
          qed (auto intro: S_rl.intros)
          subgoal for q_fedit
            apply (cases q_fedit)
            by (erule S_rl.cases, goal_cases) (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro!: trace_eq_simcl.base intro: S_rl.intros)
          done
        done
      done
    subgoal UOut_OK for sl sr q  
      apply (cases q)
      subgoal for q_usr
        apply (cases q_usr)
        subgoal for q_alice by (erule S_rl.cases; simp add: DH0_sample_def pair_spmf_alt_def power_commute)
        subgoal for q_bob by (erule S_rl.cases; auto simp add: bind_bind_conv_pair_spmf apfst_def DH0_sample_def power_commute split!: if_split)
        done
      subgoal for q_act
        apply (cases q_act)
        subgoal for q_alice
          by (erule S_rl.cases; auto simp add: left_gpv_bind_gpv exec_gpv_parallel_oracle_left map_gpv_bind_gpv gpv.map_id map_gpv'_bind_gpv map'_lift_spmf intro!: bind_spmf_cong)
        subgoal for q_bob
          by (erule S_rl.cases; auto simp add: right_gpv_bind_gpv exec_gpv_parallel_oracle_right map_gpv_bind_gpv gpv.map_id map_gpv'_bind_gpv map'_lift_spmf intro!: bind_spmf_cong)
        done
      done
    subgoal UState_OK for sl sr q  
      apply (cases q)
      subgoal for q_usr
        apply (cases q_usr)
        subgoal for q_alice
        proof (erule S_rl.cases, goal_cases)
          case (13 s_act1 s_act2) \<comment> \<open>Corresponds to @{thm [source] srl_1_2}\<close>
          then show ?case 
            apply(clarsimp simp add: DH0_sample_def pair_spmf_alt_def)
            apply(subst (1) bind_commute_spmf)
            apply(simp add: bind_bind_conv_pair_spmf)
            apply(subst (1 2) cond_spmf_fst_bind)
            by (auto simp add: power_commute intro!: trace_eq_simcl_bind S_rl.intros)
        next
          case (14 s_act1 s_act2) \<comment> \<open>Corresponds to @{thm [source] srl_2_2}\<close>
          then show ?case 
            apply(clarsimp simp add: DH0_sample_def pair_spmf_alt_def)
            apply(subst (1) bind_commute_spmf)
            apply(simp add: bind_bind_conv_pair_spmf)
            apply(subst (1 2) cond_spmf_fst_bind)
            by (auto simp add: power_commute intro!: trace_eq_simcl_bind S_rl.intros)
        qed (auto intro: S_rl.intros)
        subgoal for q_bob
        proof (erule S_rl.cases, goal_cases)
          case (8 s_act1 s_act2) \<comment> \<open>Corresponds to @{thm [source] srl_2_1}\<close>
          then show ?case 
            apply(clarsimp simp add: DH0_sample_def)
            apply(subst bind_commute_spmf)
            apply(simp add: bind_bind_conv_pair_spmf power_commute)
            apply(subst (1 2) cond_spmf_fst_bind)
            by (auto simp add: power_commute intro!: trace_eq_simcl_bind S_rl.intros)
        next
          case (14 s_act1 s_act2) \<comment> \<open>Corresponds to @{thm [source] srl_2_2}\<close>
          then show ?case 
            apply(clarsimp simp add: DH0_sample_def)
            apply(subst bind_commute_spmf)
            apply(simp add: bind_bind_conv_pair_spmf power_commute)
            apply(subst (1 2) cond_spmf_fst_bind)
            by (auto simp add: power_commute intro!: trace_eq_simcl_bind S_rl.intros)
        qed (auto simp add: power_commute intro: S_rl.intros)
        done
      subgoal for q_act
        apply (cases q_act)
        subgoal for a_alice
        proof (erule S_rl.cases, goal_cases)
          case (1 s_act1 s_act2) \<comment> \<open>Corresponds to @{thm [source] srl_0_0}\<close>
          then show ?case 
            apply (simp add: left_gpv_bind_gpv pair_spmf_alt_def map_gpv_bind_gpv gpv.map_id map_gpv'_bind_gpv map'_lift_spmf split!: if_splits)
            by (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: trace_eq_simcl.base S_rl.intros)
        next
          case (6 s_act1 s_act2) \<comment> \<open>Corresponds to @{thm [source] srl_0_1}\<close>
          then show ?case 
            apply (simp add: left_gpv_bind_gpv pair_spmf_alt_def map_gpv_bind_gpv gpv.map_id map_gpv'_bind_gpv map'_lift_spmf split!: if_splits)
            apply (subst bind_bind_conv_pair_spmf)
            by (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: trace_eq_simcl.base S_rl.intros)
        next
          case (12 s_act1 s_act2) \<comment> \<open>Corresponds to @{thm [source] srl_0_2}\<close>
          then show ?case 
            apply (simp add: left_gpv_bind_gpv pair_spmf_alt_def map_gpv_bind_gpv gpv.map_id map_gpv'_bind_gpv map'_lift_spmf split!: if_splits)
            apply (subst bind_bind_conv_pair_spmf)
            by (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: trace_eq_simcl.base S_rl.intros)
        next
          case (21 y s_act1 s_act2) \<comment> \<open>Corresponds to @{thm [source] srl_0_2'}\<close>
          then show ?case 
            apply (simp add: left_gpv_bind_gpv pair_spmf_alt_def map_gpv_bind_gpv gpv.map_id map_gpv'_bind_gpv map'_lift_spmf split!: if_splits)
            by (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: trace_eq_simcl_map S_rl.intros)
        next
          case (22 y s_act1 s_act2) \<comment> \<open>Corresponds to @{thm [source] srl_0_1'}\<close>
          then show ?case 
            apply (simp add: left_gpv_bind_gpv pair_spmf_alt_def map_gpv_bind_gpv gpv.map_id map_gpv'_bind_gpv map'_lift_spmf split!: if_splits)
            by (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: trace_eq_simcl_map S_rl.intros)
        qed (simp_all split!: if_splits)
        subgoal for a_bob
        proof (erule S_rl.cases, goal_cases)
          case (1 s_act1 s_act2) \<comment> \<open>Corresponds to @{thm [source] srl_0_0}\<close>
          then show ?case  
            apply(clarsimp simp add: right_gpv_bind_gpv pair_spmf_alt_def map_gpv_bind_gpv gpv.map_id map_gpv'_bind_gpv map'_lift_spmf split!: if_splits)
            by (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: trace_eq_simcl.base S_rl.intros)
        next
          case (2 s_act1 s_act2) \<comment> \<open>Corresponds to @{thm [source] srl_1_0}\<close>
          then show ?case 
            apply(clarsimp simp add: right_gpv_bind_gpv pair_spmf_alt_def map_gpv_bind_gpv gpv.map_id map_gpv'_bind_gpv map'_lift_spmf split!: if_splits)
            apply (subst bind_commute_spmf, subst bind_bind_conv_pair_spmf)
            by (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: trace_eq_simcl.base S_rl.intros)
        next
          case (3 s_act1 s_act2) \<comment> \<open>Corresponds to @{thm [source] srl_2_0}\<close>
          then show ?case 
            apply(clarsimp simp add: right_gpv_bind_gpv pair_spmf_alt_def map_gpv_bind_gpv gpv.map_id map_gpv'_bind_gpv map'_lift_spmf split!: if_splits)
            apply (subst bind_commute_spmf, subst bind_bind_conv_pair_spmf)
            by (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: trace_eq_simcl.base S_rl.intros)
        next
          case (4 x s_act1 s_act2) \<comment> \<open>Corresponds to @{thm [source] srl_1'_0}\<close>
          then show ?case  
            apply(clarsimp simp add: right_gpv_bind_gpv pair_spmf_alt_def map_gpv_bind_gpv gpv.map_id map_gpv'_bind_gpv map'_lift_spmf split!: if_splits)
            by (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: trace_eq_simcl_map S_rl.intros)
        next
          case (5 x s_act1 s_act2) \<comment> \<open>Corresponds to @{thm [source] srl_2'_0}\<close>
          then show ?case 
            apply(clarsimp simp add: right_gpv_bind_gpv pair_spmf_alt_def map_gpv_bind_gpv gpv.map_id map_gpv'_bind_gpv map'_lift_spmf split!: if_splits)
            by (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: trace_eq_simcl_map S_rl.intros)
        qed (simp_all split!: if_splits)
        done
      done
    done
qed

lemma trace_eq_fuse_rl: "UNIV \<turnstile>\<^sub>R 1\<^sub>C |\<^sub>= rassocl\<^sub>C \<rhd> RES (fused_resource.fuse real_core' real_rest') (real_s_core', real_s_rest')
  \<approx> RES (fused_resource.fuse (lazy_core DH0_sample) lazy_rest) (basic_core_sinit, basic_rest_sinit)"
proof -
  have fact1: "UNIV \<turnstile>\<^sub>R 1\<^sub>C |\<^sub>= rassocl\<^sub>C \<rhd> RES (fused_resource.fuse (basic_core DH0_sample) basic_rest) (basic_core_sinit, basic_rest_sinit) \<sim> 
    RES (fused_resource.fuse (lazy_core DH0_sample) lazy_rest) (basic_core_sinit, basic_rest_sinit)"
  proof -
    have [simp]: "\<I>_full \<oplus>\<^sub>\<I> ((\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<oplus>\<^sub>\<I> \<I>_full) \<turnstile>res RES (fused_resource.fuse (basic_core DH0_sample) basic_rest) (basic_core_sinit, basic_rest_sinit) \<surd>" for s
      apply (rule WT_resource_of_oracle, rule WT_calleeI)
      by (case_tac call, rename_tac [!] x, case_tac [!] x, rename_tac [!] y, case_tac [!] y)
        (auto simp add: fused_resource.fuse.simps parallel_eoracle_def)

    note [simp] =  exec_gpv_bind spmf.map_comp o_def map_bind_spmf bind_map_spmf bind_spmf_const

    show ?thesis
      apply(subst attach_wiring_resource_of_oracle)
         apply(rule wiring_parallel_converter2 wiring_id_converter[where \<I>=\<I>_full] wiring_rassocl[of \<I>_full \<I>_full \<I>_full])+
        apply simp_all
      apply (rule eq_resource_on_resource_of_oracleI[where S="(=)"])
       apply(simp_all add: eq_on_def relator_eq)
      apply(rule ext)+
      apply(subst fuse_ishift_core_to_rest[where core="basic_core DH0_sample" and rest=basic_rest and core'="lazy_core DH0_sample" and 
            rest'=lazy_rest and fn=basic_core_helper and h_out="map_sum (\<lambda>_. Out_Activation_Alice) (\<lambda>_. Out_Activation_Bob)", simplified])
        apply (simp_all add: lazy_rest_def)
      apply(fold apply_comp_wiring)
      by (simp add: comp_wiring_def parallel2_wiring_def split_def sum.map_comp lassocr\<^sub>w_def rassocl\<^sub>w_def id_def[symmetric] sum.map_id)
  qed

  have fact2: "UNIV \<turnstile>\<^sub>R 1\<^sub>C |\<^sub>= rassocl\<^sub>C \<rhd> RES (fused_resource.fuse real_core' real_rest') (real_s_core', real_s_rest') \<approx>
    1\<^sub>C |\<^sub>= rassocl\<^sub>C \<rhd> RES (fused_resource.fuse (basic_core DH0_sample) basic_rest) (basic_core_sinit, basic_rest_sinit)" 
  (is "_ \<turnstile>\<^sub>R _ \<rhd> RES ?L ?s_l \<approx> _ \<rhd> RES ?R ?s_r") proof -
    have [simp]: "trace_rest_eq basic_rest basic_rest UNIV UNIV s s" for s
      by (rule rel_rest'_into_trace_rest_eq[where S="(=)" and M="(=)"]) (simp_all add: eq_onp_def rel_rest'_eq)
    have [simp]: "\<I>_full \<oplus>\<^sub>\<I> \<I>_full \<turnstile>c callee_of_rest basic_rest s \<surd>" for s
      unfolding callee_of_core_def by (rule WT_calleeI) (cases s, case_tac call, rename_tac [!] x, case_tac [!] x,  auto)
    have [simp]: "\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<turnstile>c  callee_of_core (basic_core DH0_sample) s \<surd>" for s
      unfolding callee_of_core_def by (rule WT_calleeI) (cases s, case_tac call, rename_tac [!] x, case_tac [!] x,  auto)
    have [simp]: "\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<turnstile>c  callee_of_core real_core' s \<surd>" for s
      unfolding callee_of_core_def by (rule WT_calleeI) (cases s, case_tac call, rename_tac [!] x, case_tac [!] x,  auto)

    have loc[simplified]: "((UNIV <+> UNIV) <+> UNIV <+> UNIV) \<turnstile>\<^sub>C ?L(?s_l) \<approx> ?R(?s_r)"
      by (rule fuse_trace_eq[where \<I>E=\<I>_full and \<I>CA=\<I>_full and  \<I>CU=\<I>_full and \<I>RA=\<I>_full and \<I>RU=\<I>_full, simplified outs_plus_\<I> outs_\<I>_full])
        (simp_all add: real_rest'_def real_s_rest'_def trac_eq_core_rl[simplified])

    show ?thesis
      apply (rule attach_trace_eq'[where \<I>=\<I>_full and \<I>'=\<I>_full, simplified outs_plus_\<I> outs_\<I>_full]) 
      apply (subst trace_eq'_resource_of_oracle, rule loc[simplified])
      by (simp_all add: WT_converter_\<I>_full)
  qed

  show ?thesis using fact2[simplified eq_resource_on_UNIV_D[OF fact1]] by blast
qed

lemma connect_real: "connect D (obsf_resource real_resource) = connect D (obsf_resource (RES (fused_resource.fuse (lazy_core DH0_sample) lazy_rest) (basic_core_sinit, basic_rest_sinit)))"
proof -
  have [simp]: "\<I>_full \<turnstile>res real_resource \<surd>"
  proof -
    have [simp]: "\<I>_full \<oplus>\<^sub>\<I> ((\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<oplus>\<^sub>\<I> \<I>_full) \<turnstile>res RES (fused_resource.fuse real_core' real_rest') (real_s_core', real_s_rest') \<surd>"
      apply (rule WT_resource_of_oracle)
      apply (rule WT_calleeI)
      subgoal for s q
        apply (cases s, cases q, rename_tac [!] x, case_tac [!] x)
           prefer 3
        subgoal for s_cnv_core _ _ _ _ y
          apply (cases s_cnv_core, rename_tac s_cnvs s_auth1 s_kern2 s_shell2)
          apply (case_tac s_auth1, rename_tac s_kern1 s_shell1)
          apply (case_tac s_cnvs, rename_tac su s_cnv1 s_cnv2)
          apply (cases y, rename_tac [!] z, case_tac [!] z, rename_tac [!] query)
             apply (auto simp add: fused_resource.fuse.simps split_def apfst_def)
             apply(case_tac "(s_cnv1, Inl query)" rule: alice_callee.cases; auto split!: sum.splits auth.ousr_bob.splits simp add: Let_def o_def)
            apply(case_tac "(s_cnv2, Inl query)" rule: bob_callee.cases; auto split!: sum.splits auth.ousr_bob.splits simp add: Let_def o_def)
           apply(case_tac "(s_cnv1, Inr query)" rule: alice_callee.cases; auto split!: sum.splits 
              simp add: Let_def o_def map_gpv_bind_gpv left_gpv_bind_gpv map_gpv'_bind_gpv exec_gpv_bind)
          apply(case_tac "(s_cnv2, Inr query)" rule: bob_callee.cases; auto split!: sum.splits 
              simp add: Let_def o_def map_gpv_bind_gpv right_gpv_bind_gpv map_gpv'_bind_gpv exec_gpv_bind)
          done
        by (auto simp add: fused_resource.fuse.simps)
      done

    show ?thesis
      unfolding attach_real
      apply (rule WT_resource_attach[where \<I>'="\<I>_full \<oplus>\<^sub>\<I> ((\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<oplus>\<^sub>\<I> \<I>_full)"])
       apply (rule WT_converter_mono[of "\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_full))" "\<I>_full \<oplus>\<^sub>\<I> ((\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<oplus>\<^sub>\<I> \<I>_full)"])
         apply (rule WT_converter_parallel_converter2)
          apply (rule WT_intro)+
      by (simp_all add: \<I>_full_le_plus_\<I>)
  qed

  show ?thesis
    using trace_eq_obsf_resourceI[OF trace_eq_fuse_rl, folded attach_real]
    by (rule connect_cong_trace[where A="UNIV" and \<I>=\<I>_full])
      (auto intro!: WT_obsf_resource[where \<I>=\<I>_full, simplified exception_\<I>_full])
qed

end

end

end

subsection \<open>Concrete security\<close>

context diffie_hellman begin

context 
  fixes 
    auth1_rest :: "('auth1_s_rest, auth.event, 'auth1_iadv_rest, 'auth1_iusr_rest, 'auth1_oadv_rest, 'auth1_ousr_rest) rest_wstate" and 
    auth2_rest :: "('auth2_s_rest, auth.event, 'auth2_iadv_rest, 'auth2_iusr_rest, 'auth2_oadv_rest, 'auth2_ousr_rest) rest_wstate" and
    \<I>_adv_rest1 and \<I>_adv_rest2 and \<I>_usr_rest1 and \<I>_usr_rest2 and I_auth1_rest and I_auth2_rest
  assumes
    WT_auth1_rest [WT_intro]: "WT_rest \<I>_adv_rest1 \<I>_usr_rest1 I_auth1_rest auth1_rest" and
    WT_auth2_rest [WT_intro]: "WT_rest \<I>_adv_rest2 \<I>_usr_rest2 I_auth2_rest auth2_rest"
begin

theorem secure:
  defines "\<I>_real \<equiv> ((\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_uniform (auth.Inp_Fedit ` (carrier \<G>)) UNIV)) \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_uniform (auth.Inp_Fedit ` (carrier \<G>)) UNIV))) \<oplus>\<^sub>\<I> (\<I>_adv_rest1 \<oplus>\<^sub>\<I> \<I>_adv_rest2)"
      and "\<I>_common \<equiv> (\<I>_uniform UNIV (key.Out_Alice ` carrier \<G>) \<oplus>\<^sub>\<I> \<I>_uniform UNIV (key.Out_Bob ` carrier \<G>)) \<oplus>\<^sub>\<I> ((\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<oplus>\<^sub>\<I> (\<I>_usr_rest1 \<oplus>\<^sub>\<I> \<I>_usr_rest2))"
      and "\<I>_ideal \<equiv> \<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> (\<I>_adv_rest1 \<oplus>\<^sub>\<I> \<I>_adv_rest2))"
    shows "constructive_security_obsf 
      (real_resource TYPE(_) TYPE(_) auth1_rest auth2_rest)
      (key.resource (ideal_rest auth1_rest auth2_rest))
      (let sim = CNV sim_callee None in ((sim |\<^sub>= 1\<^sub>C ) \<odot> lassocr\<^sub>C))
      \<I>_real \<I>_ideal \<I>_common \<A> 
      (ddh.advantage \<G> (DH_adversary TYPE(_) TYPE(_) auth1_rest auth2_rest \<A>))"
proof
  let ?sim = "(let sim = CNV sim_callee None in ((sim |\<^sub>= 1\<^sub>C ) \<odot> lassocr\<^sub>C))"

  have *[WT_intro]: "(\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_uniform (auth.Inp_Fedit ` carrier \<G>) UNIV)) \<oplus>\<^sub>\<I>
    (\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_uniform (auth.Inp_Fedit ` carrier \<G>) UNIV)), \<I>_full \<oplus>\<^sub>\<I> \<I>_full \<turnstile>\<^sub>C CNV sim_callee s \<surd>" for s
      apply (rule WT_converter_of_callee, simp_all)
      apply (rename_tac s q r s', case_tac "(s, q)" rule: sim_callee.cases)
    by (auto split: if_splits option.splits)

  show "\<I>_real \<oplus>\<^sub>\<I> \<I>_common \<turnstile>res real_resource TYPE(_) TYPE(_) auth1_rest auth2_rest \<surd>"
  proof -
    have [WT_intro]: "\<I>_uniform UNIV (key.Out_Alice ` carrier \<G>) \<oplus>\<^sub>\<I> \<I>_full, \<I>_uniform (auth.Inp_Send ` carrier \<G>) UNIV \<oplus>\<^sub>\<I> \<I>_uniform UNIV (auth.Out_Recv ` carrier \<G>) \<turnstile>\<^sub>C  CNV alice_callee CState_Void \<surd>"
      apply (rule WT_converter_of_callee_invar[where I="pred_cstate (\<lambda>x. x \<in> carrier \<G>)"])
      subgoal for s q  by (cases "(s, q)" rule: alice_callee.cases) (auto simp add: Let_def split: auth.ousr_bob.splits)
      subgoal for s q  by (cases "(s, q)" rule: alice_callee.cases) (auto split: if_split_asm auth.ousr_bob.splits simp add: Let_def)
      subgoal by simp
      done

    have [WT_intro]: "\<I>_uniform UNIV (key.Out_Bob ` carrier \<G>) \<oplus>\<^sub>\<I> \<I>_full, \<I>_uniform UNIV (auth.Out_Recv ` carrier \<G>) \<oplus>\<^sub>\<I> \<I>_uniform (auth.Inp_Send ` carrier \<G>) UNIV \<turnstile>\<^sub>C  CNV bob_callee CState_Void \<surd>"
      apply (rule WT_converter_of_callee_invar[where I="pred_cstate (\<lambda>x. x \<in> carrier \<G>)"])
      subgoal for s q  by (cases "(s, q)" rule: bob_callee.cases) (auto simp add: Let_def split: auth.ousr_bob.splits)
      subgoal for s q  by (cases "(s, q)" rule: bob_callee.cases) (auto simp add: Let_def split: auth.ousr_bob.splits)
      subgoal by simp
      done

    show ?thesis
      unfolding \<I>_real_def \<I>_common_def real_resource_def Let_def fused_wiring_def
      by (rule WT_intro)+
  qed

  show "\<I>_ideal \<oplus>\<^sub>\<I> \<I>_common \<turnstile>res key.resource (ideal_rest auth1_rest auth2_rest) \<surd>"
    unfolding \<I>_ideal_def \<I>_common_def key.resource_def
    apply(rule callee_invariant_on.WT_resource_of_oracle[where I="\<lambda>((kernel, _), _, s12). key.set_s_kernel kernel \<subseteq> carrier \<G> \<and> pred_prod I_auth1_rest I_auth2_rest s12"]; (simp add: WT_restD[OF WT_auth1_rest] WT_restD[OF WT_auth2_rest])?)
    apply unfold_locales
    subgoal for s q
      apply (cases "(ideal_rest auth1_rest auth2_rest, s, q)" rule: key.fuse.cases; clarsimp split: if_split_asm)
         apply (auto simp add: translate_eoracle_def parallel_eoracle_def plus_eoracle_def)
                apply(auto dest: WT_restD_rfunc_adv[OF WT_auth1_rest] WT_restD_rfunc_adv[OF WT_auth2_rest]
          WT_restD_rfunc_usr[OF WT_auth1_rest] WT_restD_rfunc_usr[OF WT_auth2_rest] key.foldl_poke_invar)
            apply(auto dest!: key.foldl_poke_invar split: plus_oracle_split_asm)
      done
    subgoal for s
      apply(rule WT_calleeI)
      subgoal for x y s'
      apply(auto simp add: translate_eoracle_def parallel_eoracle_def plus_eoracle_def)
      apply(auto dest: WT_restD_rfunc_adv[OF WT_auth1_rest] WT_restD_rfunc_adv[OF WT_auth2_rest]
          WT_restD_rfunc_usr[OF WT_auth1_rest] WT_restD_rfunc_usr[OF WT_auth2_rest] split: if_split_asm)
        apply(case_tac xa)
         apply auto
        done
      done
    done

  show "\<I>_real, \<I>_ideal \<turnstile>\<^sub>C ?sim \<surd>"
    unfolding \<I>_real_def \<I>_ideal_def Let_def
    by(rule WT_intro)+

  show "pfinite_converter \<I>_real \<I>_ideal ?sim"
  proof -
    have [pfinite_intro]:"pfinite_converter ((\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_uniform (auth.Inp_Fedit ` carrier \<G>) UNIV)) \<oplus>\<^sub>\<I>
      (\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_uniform (auth.Inp_Fedit ` carrier \<G>) UNIV))) (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) (CNV sim_callee s)" for s
      apply(rule raw_converter_invariant.pfinite_converter_of_callee[where I="\<lambda>_. True"], simp_all)
      subgoal 
        apply (unfold_locales, simp_all)
        subgoal for s1 s2
          apply (case_tac "(s1, s2)" rule: sim_callee.cases)
          by (auto simp add: id_def split!: sum.splits if_splits option.splits)
        done
      subgoal for s2 s1  by (case_tac "(s1, s2)" rule: sim_callee.cases) auto
      done

    show ?thesis
      unfolding \<I>_real_def \<I>_ideal_def Let_def
      by (rule pfinite_intro | rule WT_intro)+
  qed

  show "0 \<le> ddh.advantage \<G> (diffie_hellman.DH_adversary \<G> auth1_rest auth2_rest \<A>)" 
    by(simp add: ddh.advantage_def)

  assume WT [WT_intro]: "exception_\<I> (\<I>_real \<oplus>\<^sub>\<I> \<I>_common) \<turnstile>g \<A> \<surd>"
  show "advantage \<A> (obsf_resource (?sim |\<^sub>= 1\<^sub>C \<rhd> key.resource (ideal_rest auth1_rest auth2_rest))) (obsf_resource (real_resource TYPE(_) TYPE(_) auth1_rest auth2_rest)) \<le> ddh.advantage \<G> (diffie_hellman.DH_adversary \<G> auth1_rest auth2_rest \<A>)"
  proof -
    have id_split[unfolded Let_def]: "connect \<A> (obsf_resource (?sim |\<^sub>= 1\<^sub>C \<rhd> key.resource (ideal_rest auth1_rest auth2_rest))) = 
      connect \<A> (obsf_resource (?sim |\<^sub>= (1\<^sub>C |\<^sub>= 1\<^sub>C) \<rhd> key.resource (ideal_rest auth1_rest auth2_rest)))"  (is "connect _ ?L = connect _ ?R")
    proof -
      note [unfolded \<I>_ideal_def, WT_intro] = \<open>\<I>_real, \<I>_ideal \<turnstile>\<^sub>C ?sim \<surd>\<close> 
      note [unfolded \<I>_ideal_def, WT_intro] = \<open>\<I>_ideal \<oplus>\<^sub>\<I> \<I>_common \<turnstile>res key.resource (ideal_rest auth1_rest auth2_rest) \<surd>\<close>

      have [WT_intro]: "WT_rest (\<I>_full \<oplus>\<^sub>\<I> (\<I>_adv_rest1 \<oplus>\<^sub>\<I> \<I>_adv_rest2)) (\<I>_full \<oplus>\<^sub>\<I> (\<I>_usr_rest1 \<oplus>\<^sub>\<I> \<I>_usr_rest2)) (\<lambda>(_, s12). pred_prod I_auth1_rest I_auth2_rest s12)
       (ideal_rest auth1_rest auth2_rest)"
        apply (rule WT_rest.intros; simp)
        subgoal for s q
          apply (cases s, case_tac q, rename_tac [2] x, case_tac [2] x)
            apply (auto simp add: translate_eoracle_def parallel_eoracle_def)
          using  WT_restD_rfunc_adv[OF WT_auth1_rest] WT_restD_rfunc_adv[OF WT_auth2_rest] by fastforce+
        subgoal for s q
          apply (cases s, case_tac q, rename_tac [2] x, case_tac [2] x)
            apply (auto simp add: translate_eoracle_def parallel_eoracle_def plus_eoracle_def)
          using  WT_restD_rfunc_usr[OF WT_auth1_rest] WT_restD_rfunc_usr[OF WT_auth2_rest] by fastforce+
        subgoal by(simp add: WT_restD[OF WT_auth1_rest] WT_restD[OF WT_auth2_rest])
        done

      have *: "outs_\<I> (exception_\<I> (\<I>_real \<oplus>\<^sub>\<I> \<I>_common)) \<turnstile>\<^sub>R ?L \<sim> ?R"        
        apply (rule obsf_resource_eq_\<I>_cong)
        apply (rule eq_\<I>_attach_on')
          apply (rule WT_intro | simp)+
         apply(rule parallel_converter2_eq_\<I>_cong)
          apply(rule eq_\<I>_converter_reflI)
          apply (rule \<open>\<I>_real, \<I>_ideal \<turnstile>\<^sub>C ?sim \<surd>\<close>[unfolded assms Let_def])
         apply (rule eq_\<I>_converter_sym)
          apply (rule parallel_converter2_id_id)
        by (auto simp add: \<I>_real_def \<I>_common_def)  

      show ?thesis
        by (rule * connect_eq_resource_cong WT_intro)+
    qed

    show ?thesis
      unfolding advantage_def Let_def id_split
      unfolding Let_def connect_real connect_ideal[unfolded ideal_resource_def Let_def] reduction[unfolded advantage_def] ..
  qed
qed

end

end

subsection \<open>Asymptotic security\<close>

locale diffie_hellman' = 
  fixes \<G> :: "security \<Rightarrow> 'grp cyclic_group"
  assumes diffie_hellman [locale_witness]: "\<And>\<eta>. diffie_hellman (\<G> \<eta>)"
begin

sublocale diffie_hellman "\<G> \<eta>" for \<eta> ..

definition real_resource' where "real_resource' rest1 rest2 \<eta> = real_resource TYPE(_) TYPE(_) \<eta> (rest1 \<eta>) (rest2 \<eta>)"
definition ideal_resource' where "ideal_resource' rest1 rest2 \<eta> = key.resource \<eta> (ideal_rest (rest1 \<eta>) (rest2 \<eta>))"
definition sim' where "sim' \<eta> = (let sim = CNV (sim_callee \<eta>) None in ((sim |\<^sub>= 1\<^sub>C ) \<odot> lassocr\<^sub>C))"

context 
  fixes 
    auth1_rest :: "nat \<Rightarrow> ('auth1_s_rest, auth.event, 'auth1_iadv_rest, 'auth1_iusr_rest, 'auth1_oadv_rest, 'auth1_ousr_rest) rest_wstate" and 
    auth2_rest :: "nat \<Rightarrow> ('auth2_s_rest, auth.event, 'auth2_iadv_rest, 'auth2_iusr_rest, 'auth2_oadv_rest, 'auth2_ousr_rest) rest_wstate" and
    \<I>_adv_rest1 and \<I>_adv_rest2 and \<I>_usr_rest1 and \<I>_usr_rest2 and I_auth1_rest and I_auth2_rest
  assumes
    WT_auth1_rest: "\<And>\<eta>. WT_rest (\<I>_adv_rest1 \<eta>) (\<I>_usr_rest1 \<eta>) (I_auth1_rest \<eta>) (auth1_rest \<eta>)" and
    WT_auth2_rest: "\<And>\<eta>. WT_rest (\<I>_adv_rest2 \<eta>) (\<I>_usr_rest2 \<eta>) (I_auth2_rest \<eta>) (auth2_rest \<eta>)"
begin

theorem secure:
  defines "\<I>_real \<equiv> \<lambda>\<eta>. ((\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_uniform (auth.Inp_Fedit ` (carrier (\<G> \<eta>))) UNIV)) \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_uniform (auth.Inp_Fedit ` (carrier (\<G> \<eta>))) UNIV))) \<oplus>\<^sub>\<I> (\<I>_adv_rest1 \<eta> \<oplus>\<^sub>\<I> \<I>_adv_rest2 \<eta>)"
      and "\<I>_common \<equiv> \<lambda>\<eta>. (\<I>_uniform UNIV (key.Out_Alice ` carrier (\<G> \<eta>)) \<oplus>\<^sub>\<I> \<I>_uniform UNIV (key.Out_Bob ` carrier (\<G> \<eta>))) \<oplus>\<^sub>\<I> ((\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<oplus>\<^sub>\<I> (\<I>_usr_rest1 \<eta> \<oplus>\<^sub>\<I> \<I>_usr_rest2 \<eta>))"
      and "\<I>_ideal \<equiv> \<lambda>\<eta>. \<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> (\<I>_adv_rest1 \<eta> \<oplus>\<^sub>\<I> \<I>_adv_rest2 \<eta>))"
assumes DDH: "negligible (\<lambda>\<eta>. ddh.advantage (\<G> \<eta>) (DH_adversary TYPE(_) TYPE(_) \<eta> (auth1_rest \<eta>) (auth2_rest \<eta>) (\<A> \<eta>)))"
    shows "constructive_security_obsf' (real_resource' auth1_rest auth2_rest) (ideal_resource' auth1_rest auth2_rest) sim' \<I>_real \<I>_ideal \<I>_common \<A>"
proof(rule constructive_security_obsf'I)
  show "constructive_security_obsf (real_resource' auth1_rest auth2_rest \<eta>)
          (ideal_resource' auth1_rest auth2_rest \<eta>) (sim' \<eta>) (\<I>_real \<eta>) (\<I>_ideal \<eta>) (\<I>_common \<eta>)
          (\<A> \<eta>) (ddh.advantage (\<G> \<eta>) (DH_adversary TYPE(_) TYPE(_) \<eta> (auth1_rest \<eta>) (auth2_rest \<eta>) (\<A> \<eta>)))" for \<eta>
    unfolding real_resource'_def ideal_resource'_def sim'_def \<I>_real_def \<I>_common_def \<I>_ideal_def
    by(rule secure)(rule WT_auth1_rest WT_auth2_rest)+
qed(rule DDH)

end

end

end