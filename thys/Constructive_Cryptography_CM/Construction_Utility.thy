theory Construction_Utility
  imports
    Fused_Resource
    State_Isomorphism
begin

\<comment> \<open>Dummy converters that return a constant value on their external interface\<close>

primcorec 
  ldummy_converter :: "('a \<Rightarrow> 'b) \<Rightarrow> ('i_cnv, 'o_cnv, 'i_res, 'o_res) converter \<Rightarrow> 
    ('a + 'i_cnv, 'b + 'o_cnv, 'i_res, 'o_res) converter"
  where
    "run_converter (ldummy_converter f conv) = (\<lambda>inp. case inp of
      Inl x \<Rightarrow> map_gpv (map_prod Inl (\<lambda>_. ldummy_converter f conv)) id (Done (f x, ()))
    | Inr x \<Rightarrow> map_gpv (map_prod Inr (\<lambda>c. ldummy_converter f c)) id (run_converter conv x))"

primcorec 
  rdummy_converter :: "('a \<Rightarrow> 'b) \<Rightarrow> ('i_cnv, 'o_cnv, 'i_res, 'o_res) converter \<Rightarrow> 
    ('i_cnv + 'a, 'o_cnv + 'b, 'i_res, 'o_res) converter"
  where
    "run_converter (rdummy_converter f conv) = (\<lambda>inp. case inp of
      Inl x \<Rightarrow> map_gpv (map_prod Inl (\<lambda>c. rdummy_converter f c)) id (run_converter conv x)
    | Inr x \<Rightarrow> map_gpv (map_prod Inr (\<lambda>_. rdummy_converter f conv)) id (Done (f x, ())))"

lemma ldummy_converter_of_callee: 
  "ldummy_converter f (converter_of_callee callee state) = 
    converter_of_callee (\<lambda>s q. case_sum (\<lambda>ql. Done (Inl (f ql), s)) (\<lambda>qr. map_gpv (map_prod Inr id) id (callee s qr))  q)  state"
  apply (coinduction arbitrary: callee state)
  apply(clarsimp intro!:rel_funI split!:sum.splits)
  subgoal by blast
  apply (simp add: gpv.rel_map map_prod_def split_def)
  by (rule gpv.rel_mono_strong0[of "(=)" "(=)"]) (auto simp add: gpv.rel_eq)

lemma rdummy_converter_of_callee: 
  "rdummy_converter f (converter_of_callee callee state) = 
    converter_of_callee (\<lambda>s q. case_sum (\<lambda>ql. map_gpv (map_prod Inl id) id (callee s ql)) (\<lambda>qr. Done (Inr (f qr), s))  q) state"
  apply (coinduction arbitrary: callee state)
  apply(clarsimp intro!:rel_funI split!:sum.splits)
  defer
  subgoal by blast
  apply (simp add: gpv.rel_map map_prod_def split_def)
  by (rule gpv.rel_mono_strong0[of "(=)" "(=)"]) (auto simp add: gpv.rel_eq)



\<comment> \<open>Commonly used wirings\<close>

context
  fixes
    cnv1 :: "('icnv_usr1, 'ocnv_usr1, 'iusr1_res1 + 'iusr1_res2, 'ousr1_res1 + 'ousr1_res2) converter" and
    cnv2 :: "('icnv_usr2, 'ocnv_usr2, 'iusr2_res1 + 'iusr2_res2, 'ousr2_res1 + 'ousr2_res2) converter" 
begin

\<comment> \<open>c1r22: a converter that has 1 interface and sends queries to two resources,
   where the first and second resources have 2 and 2 interfaces respectively\<close>
  
definition 
  wiring_c1r22_c1r22 :: "('icnv_usr1 + 'icnv_usr2, 'ocnv_usr1 + 'ocnv_usr2, 
    ('iusr1_res1 + 'iusr2_res1) + 'iusr1_res2 + 'iusr2_res2, 
    ('ousr1_res1 + 'ousr2_res1) + 'ousr1_res2 + 'ousr2_res2) converter"
  where 
    "wiring_c1r22_c1r22  \<equiv> (cnv1 |\<^sub>= cnv2) \<odot> parallel_wiring"

end


\<comment> \<open>Special wiring converters used for the parallel composition of Fused resources\<close>

definition 
  fused_wiring :: "
    ((('iadv_core1 + 'iadv_core2) + ('iadv_rest1 + 'iadv_rest2)) + 
      (('iusr_core1 + 'iusr_core2) + ('iusr_rest1 + 'iusr_rest2)), 
    (('oadv_core1 + 'oadv_core2) + ('oadv_rest1 + 'oadv_rest2)) +
      (('ousr_core1 + 'ousr_core2) + ('ousr_rest1 + 'ousr_rest2)),
    (('iadv_core1 + 'iadv_rest1) + ('iusr_core1 + 'iusr_rest1)) + 
      (('iadv_core2 + 'iadv_rest2) + ('iusr_core2 + 'iusr_rest2)),
    (('oadv_core1 + 'oadv_rest1) + ('ousr_core1 + 'ousr_rest1)) + 
      (('oadv_core2 + 'oadv_rest2) + ('ousr_core2 + 'ousr_rest2))) converter"
  where
    "fused_wiring \<equiv> (parallel_wiring |\<^sub>= parallel_wiring) \<odot> parallel_wiring"

definition 
  fused_wiring\<^sub>w 
  where
    "fused_wiring\<^sub>w \<equiv> (parallel_wiring\<^sub>w |\<^sub>w parallel_wiring\<^sub>w) \<circ>\<^sub>w parallel_wiring\<^sub>w"

schematic_goal 
  wiring_fused_wiring[wiring_intro]: "wiring ?\<I>1 ?\<I>2 fused_wiring fused_wiring\<^sub>w"
  unfolding fused_wiring_def fused_wiring\<^sub>w_def
  by(rule wiring_intro)+

schematic_goal WT_fused_wiring [WT_intro]: "?\<I>1, ?\<I>2 \<turnstile>\<^sub>C fused_wiring \<surd>"
  unfolding fused_wiring_def
  by(rule WT_intro)+



\<comment> \<open>Commonlu used attachments\<close>

context
  fixes
    cnv1 :: "('icnv_usr1, 'ocnv_usr1, 'iusr1_core1 + 'iusr1_core2, 'ousr1_core1 + 'ousr1_core2) converter" and
    cnv2 :: "('icnv_usr2, 'ocnv_usr2, 'iusr2_core1 + 'iusr2_core2, 'ousr2_core1 + 'ousr2_core2) converter" and
    res1 :: "(('iadv_core1 + 'iadv_rest1) + ('iusr1_core1 + 'iusr2_core1) + 'iusr_rest1,
      ('oadv_core1 + 'oadv_rest1) + ('ousr1_core1 + 'ousr2_core1) + 'ousr_rest1) resource" and
    res2 :: "(('iadv_core2 + 'iadv_rest2) + ('iusr1_core2 + 'iusr2_core2) + 'iusr_rest2,
      ('oadv_core2 + 'oadv_rest2) + ('ousr1_core2 + 'ousr2_core2) + 'ousr_rest2) resource"
begin

\<comment> \<open>Attachement of two c1f22 ('f' instead of 'r' to indicate Fused Resources) converters 
  to two 2-interface Fused Resources, the results will be a new 2-interface Fused Resource\<close>

definition 
  attach_c1f22_c1f22 :: "((('iadv_core1 + 'iadv_core2) + 'iadv_rest1 + 'iadv_rest2) + ('icnv_usr1 + 'icnv_usr2) + 'iusr_rest1 + 'iusr_rest2,
    (('oadv_core1 + 'oadv_core2) + 'oadv_rest1 + 'oadv_rest2) + ('ocnv_usr1 + 'ocnv_usr2) + 'ousr_rest1 + 'ousr_rest2) resource"
  where
    "attach_c1f22_c1f22 = (((1\<^sub>C |\<^sub>= 1\<^sub>C) |\<^sub>= ((wiring_c1r22_c1r22 cnv1 cnv2) |\<^sub>= 1\<^sub>C)) \<odot> fused_wiring) \<rhd> (res1 \<parallel> res2)"
end


\<comment> \<open>Properties of Converters attaching to Fused resources\<close>
context
  fixes
    core1 :: "('s_core1, 'e1, 'iadv_core1, 'iusr_core1, 'oadv_core1, 'ousr_core1) core" and
    core2 :: "('s_core2, 'e2, 'iadv_core2, 'iusr_core2, 'oadv_core2, 'ousr_core2) core" and
    rest1 :: "('s_rest1, 'e1, 'iadv_rest1, 'iusr_rest1, 'oadv_rest1, 'ousr_rest1, 'm1) rest_scheme" and
    rest2 :: "('s_rest2, 'e2, 'iadv_rest2, 'iusr_rest2, 'oadv_rest2, 'ousr_rest2, 'm2) rest_scheme"
begin

lemma parallel_oracle_fuse:
  "apply_wiring fused_wiring\<^sub>w (parallel_oracle (fused_resource.fuse core1 rest1) (fused_resource.fuse core2 rest2)) =
    apply_state_iso parallel_state_iso (fused_resource.fuse (parallel_core core1 core2) (parallel_rest rest1 rest2))"
  supply fused_resource.fuse.simps[simp]
  apply(rule ext)+
  apply(clarsimp simp add: fused_wiring\<^sub>w_def apply_state_iso_def parallel_state_iso_def parallel_wiring\<^sub>w_def)
  apply(simp add: apply_wiring_def comp_wiring_def parallel2_wiring_def lassocr\<^sub>w_def swap_lassocr\<^sub>w_def rassocl\<^sub>w_def swap\<^sub>w_def)
  subgoal for s_core1 s_rest1 s_core2 s_rest2 i
    apply(cases "(parallel_rest rest1 rest2, ((s_core1, s_core2), (s_rest1, s_rest2)), i)" rule: fused_resource.fuse.cases)
       apply(auto split!: sum.splits)
    subgoal for iadv_core
      by (cases iadv_core) (auto simp add: map_spmf_bind_spmf bind_map_spmf intro!: bind_spmf_cong split!: sum.splits)
    subgoal for iadv_rest
      by (cases iadv_rest) (auto simp add: parallel_handler_left parallel_handler_right foldl_spmf_pair_left 
        parallel_eoracle_def foldl_spmf_pair_right split_beta o_def map_spmf_bind_spmf bind_map_spmf)
    subgoal for iusr_core
      by (cases iusr_core) (auto simp add: map_spmf_bind_spmf bind_map_spmf intro!: bind_spmf_cong split!: sum.splits)
    subgoal for iusr_rest
      by (cases iusr_rest) (auto simp add: parallel_handler_left parallel_handler_right foldl_spmf_pair_left 
        parallel_eoracle_def foldl_spmf_pair_right split_beta o_def map_spmf_bind_spmf bind_map_spmf)
    done
  done
end

lemma attach_callee_fuse:
  "attach_callee ((cnv_adv_core \<ddagger>\<^sub>I cnv_adv_rest) \<ddagger>\<^sub>I cnv_usr_core \<ddagger>\<^sub>I cnv_usr_rest) (fused_resource.fuse core rest) =
   apply_state_iso iso_trisplit (fused_resource.fuse (attach_core cnv_adv_core cnv_usr_core core) (attach_rest cnv_adv_rest cnv_usr_rest f_init rest))"
  (is "?lhs = ?rhs")
proof(intro ext; clarify)
  note fused_resource.fuse.simps [simp]
  let ?tri = "\<lambda>(((s11, s12), s13), (s21, s22), s23). (((s11, s21), s12, s22), s13, s23)"
  fix q :: "('g + 'h) + 'i + 'j"
  consider (ACore) qac where "q = Inl (Inl qac)"
    | (ARest) qar where "q = Inl (Inr qar)"
    | (UCore) quc where "q = Inr (Inl quc)"
    | (URest) qur where "q = Inr (Inr qur)"
    using fuse_callee.cases by blast
  then show "?lhs (((sac, sar), (suc, sur)), (sc, sr)) q = ?rhs (((sac, sar), (suc, sur)), (sc, sr)) q"
    for sac sar suc sur sc sr
  proof cases
    case ACore
    have "map_spmf rprodl (exec_gpv (fused_resource.fuse core rest)
       (left_gpv (map_gpv (map_prod Inl (\<lambda>s1'. (s1', suc, sur))) id (left_gpv (map_gpv (map_prod Inl (\<lambda>s1'. (s1', sar))) id (cnv_adv_core sac qac)))))
       (sc, sr)) =
     (map_spmf (map_prod (Inl \<circ> Inl) (?tri \<circ> prod.swap \<circ> Pair ((sar, sur), sr)))
       (map_spmf (\<lambda>((oadv, s_adv'), s_core'). (oadv, (s_adv', suc), s_core'))
         (exec_gpv (cfunc_adv core) (cnv_adv_core sac qac) sc)))" 
    proof(induction arbitrary: sc cnv_adv_core rule: exec_gpv_fixp_parallel_induct)
      case adm show ?case by simp
      case bottom show ?case by simp
      case (step execl execr)
      show ?case
        apply(clarsimp simp add: gpv.map_sel map_bind_spmf bind_map_spmf intro!: bind_spmf_cong[OF refl] split!: generat.split)
        apply(subst step.IH[unfolded id_def])
        apply(simp add: spmf.map_comp o_def)
        done
    qed
    then show ?thesis using ACore
      by(simp add: apply_state_iso_def iso_trisplit_def map_spmf_conv_bind_spmf[symmetric] spmf.map_comp o_def split_def)
  next
    case ARest
    have "bind_spmf (foldl_spmf (cpoke core) (return_spmf sc) es) (\<lambda>sc'.
      map_spmf rprodl (exec_gpv (fused_resource.fuse core rest)
        (left_gpv (map_gpv (map_prod Inl (\<lambda>s1'. (s1', suc, sur))) id (right_gpv (map_gpv (map_prod Inr (Pair sac)) id (cnv_adv_rest sar qar)))))
        (sc', sr))) =
      bind_spmf
        (exec_gpv (\<lambda>(s, es) q. map_spmf (\<lambda>((out, e), s'). (out, s', es @ e)) (rfunc_adv rest s q)) (cnv_adv_rest sar qar) (sr, es))
        (map_spmf (map_prod id ?tri) \<circ>
          ((\<lambda>((o_rfunc, e_lst), s_rfunc). map_spmf (\<lambda>s_notify. (Inl (Inr o_rfunc), s_notify, s_rfunc))
            (map_spmf (Pair (sac, suc)) (foldl_spmf (cpoke core) (return_spmf sc) e_lst))) \<circ>
          (\<lambda>((oadv, s_adv'), s_rest', es). ((oadv, es), (s_adv', sur), s_rest'))))"
      for es
    proof(induction arbitrary: sc sr es cnv_adv_rest rule: exec_gpv_fixp_parallel_induct)
      case adm then show ?case by simp
      case bottom then show ?case by simp
      case (step execl execr)
      show ?case 
        apply(clarsimp simp add: gpv.map_sel map_bind_spmf bind_map_spmf)
        apply(subst bind_commute_spmf)
        apply(clarsimp simp add: gpv.map_sel map_bind_spmf bind_map_spmf spmf.map_comp o_def map_spmf_conv_bind_spmf[symmetric] intro!: bind_spmf_cong[OF refl] split!: generat.split)
        apply(subst bind_commute_spmf)
        apply(clarsimp simp add: gpv.map_sel map_bind_spmf bind_map_spmf spmf.map_comp o_def map_spmf_conv_bind_spmf[symmetric] intro!: bind_spmf_cong[OF refl] split!: generat.split)
        apply(simp add: bind_spmf_assoc[symmetric] bind_foldl_spmf_return foldl_spmf_append[symmetric] del: bind_spmf_assoc )
        apply(subst step.IH[unfolded id_def])
        apply(simp add: split_def o_def spmf.map_comp)
        done
    qed
    from this[of "[]"]
    show ?thesis using ARest
      by(simp add: apply_state_iso_def iso_trisplit_def map_bind_spmf bind_map_spmf map_spmf_conv_bind_spmf[symmetric] foldl_spmf_pair_right)
  next
    case UCore
    have "map_spmf rprodl (exec_gpv (fused_resource.fuse core rest)
       (right_gpv (map_gpv (map_prod Inr (Pair (sac, sar))) id (left_gpv (map_gpv (map_prod Inl (\<lambda>s1'. (s1', sur))) id (cnv_usr_core suc quc)))))
       (sc, sr)) =
     (map_spmf (map_prod (Inr \<circ> Inl) (?tri \<circ> prod.swap \<circ> Pair ((sar, sur), sr)))
       (map_spmf (\<lambda>((ousr, s_usr'), s_core'). (ousr, (sac, s_usr'), s_core'))
         (exec_gpv (cfunc_usr core) (cnv_usr_core suc quc) sc)))"
    proof(induction arbitrary: sc cnv_usr_core rule: exec_gpv_fixp_parallel_induct)
      case adm show ?case by simp
      case bottom show ?case by simp
      case (step execl execr)
      show ?case
        apply(clarsimp simp add: gpv.map_sel map_bind_spmf bind_map_spmf intro!: bind_spmf_cong[OF refl] split!: generat.split)
        apply(subst step.IH[unfolded id_def])
        apply(simp add: spmf.map_comp o_def)
        done
    qed
    then show ?thesis using UCore
      by(simp add: apply_state_iso_def iso_trisplit_def map_spmf_conv_bind_spmf[symmetric] spmf.map_comp o_def split_def)
  next
    case URest
    have "bind_spmf (foldl_spmf (cpoke core) (return_spmf sc) es) (\<lambda>sc'.
      map_spmf rprodl (exec_gpv (fused_resource.fuse core rest)
        (right_gpv (map_gpv (map_prod Inr (Pair (sac, sar))) id (right_gpv (map_gpv (map_prod Inr (Pair suc)) id (cnv_usr_rest sur qur)))))
        (sc', sr))) =
      bind_spmf
        (exec_gpv (\<lambda>(s, es) q. map_spmf (\<lambda>((out, e), s'). (out, s', es @ e)) (rfunc_usr rest s q)) (cnv_usr_rest sur qur) (sr, es))
        (map_spmf (map_prod id ?tri) \<circ>
           ((\<lambda>((o_rfunc, e_lst), s_rfunc). map_spmf (\<lambda>s_notify. (Inr (Inr o_rfunc), s_notify, s_rfunc))
              (map_spmf (Pair (sac, suc)) (foldl_spmf (cpoke core) (return_spmf sc) e_lst))) \<circ>
           (\<lambda>((ousr, s_usr'), s_rest', es). ((ousr, es), (sar, s_usr'), s_rest'))))"
      for es
    proof(induction arbitrary: sc sr es cnv_usr_rest rule: exec_gpv_fixp_parallel_induct)
      case adm then show ?case by simp
      case bottom then show ?case by simp
      case (step execl execr)
      show ?case 
        apply(clarsimp simp add: gpv.map_sel map_bind_spmf bind_map_spmf)
        apply(subst bind_commute_spmf)
        apply(clarsimp simp add: gpv.map_sel map_bind_spmf bind_map_spmf spmf.map_comp o_def map_spmf_conv_bind_spmf[symmetric] intro!: bind_spmf_cong[OF refl] split!: generat.split)
        apply(subst bind_commute_spmf)
        apply(clarsimp simp add: gpv.map_sel map_bind_spmf bind_map_spmf spmf.map_comp o_def map_spmf_conv_bind_spmf[symmetric] intro!: bind_spmf_cong[OF refl] split!: generat.split)
        apply(simp add: bind_spmf_assoc[symmetric] bind_foldl_spmf_return foldl_spmf_append[symmetric] del: bind_spmf_assoc )
        apply(subst step.IH[unfolded id_def])
        apply(simp add: split_def o_def spmf.map_comp)
        done
    qed
    from this[of "[]"] show ?thesis using URest
      by(simp add: apply_state_iso_def iso_trisplit_def map_bind_spmf bind_map_spmf map_spmf_conv_bind_spmf[symmetric] foldl_spmf_pair_right)
  qed
qed

lemma attach_parallel_fuse':
  "(CNV cnv_adv_core s_a_c |\<^sub>= CNV cnv_adv_rest s_a_r) |\<^sub>= (CNV cnv_usr_core s_u_c |\<^sub>= CNV cnv_usr_rest s_u_r) \<rhd> 
   RES (fused_resource.fuse core rest) (s_r_c, s_r_r) = 
   RES (fused_resource.fuse (attach_core cnv_adv_core cnv_usr_core core) (attach_rest cnv_adv_rest cnv_usr_rest f_init rest)) (((s_a_c, s_u_c), s_r_c), ((s_a_r, s_u_r), s_r_r))"
  apply(fold conv_callee_parallel)
  apply(unfold attach_CNV_RES)
  apply(subst attach_callee_fuse)
  apply(subst resource_of_oracle_state_iso)
   apply simp
  apply(simp add: iso_trisplit_def)
  done


\<comment> \<open>Moving event translators from rest to the core\<close>

context
  fixes
    einit :: 's_event and
    etran :: "('s_event, 'ievent, 'oevent list) oracle'" and
    rest :: "('s_rest, 'ievent, 'iadv_rest, 'iusr_rest, 'oadv_rest, 'ousr_rest) rest_wstate" and
    core :: "('s_core, 'oevent, 'iadv_core, 'iusr_core, 'oadv_core, 'ousr_core) core"
begin

primcorec
  translate_rest :: "('s_event \<times> 's_rest, 'oevent, 'iadv_rest, 'iusr_rest, 'oadv_rest, 'ousr_rest) rest_wstate"
  where
    "rinit translate_rest = (einit, rinit rest)"
  | "rfunc_adv translate_rest = translate_eoracle etran (extend_state_oracle (rfunc_adv rest))"
  | "rfunc_usr translate_rest = translate_eoracle etran (extend_state_oracle (rfunc_usr rest))"

primcorec
  translate_core :: "('s_event \<times> 's_core, 'ievent, 'iadv_core, 'iusr_core, 'oadv_core, 'ousr_core) core"
  where
    "cpoke translate_core = (\<lambda>(s_event, s_core) event. 
      bind_spmf (etran s_event event) (\<lambda>(events, s_event'). 
        map_spmf (\<lambda>s_core'. (s_event', s_core')) (foldl_spmf (cpoke core) (return_spmf s_core) events)))"
  | "cfunc_adv translate_core = extend_state_oracle (cfunc_adv core)"
  | "cfunc_usr translate_core = extend_state_oracle (cfunc_usr core)"


lemma WT_translate_rest [WT_intro]: 
  assumes "WT_rest \<I>_adv \<I>_usr I_rest rest"
  shows "WT_rest \<I>_adv \<I>_usr (pred_prod (\<lambda>_. True) I_rest) translate_rest"
  by(rule WT_rest.intros)(auto simp add: translate_eoracle_def simp add: WT_restD_rinit[OF assms] dest!: WT_restD(1,2)[OF assms])


lemma fused_resource_move_translate:
  "fused_resource.fuse core translate_rest = apply_state_iso iso_swapar (fused_resource.fuse translate_core rest)"
proof -
  note [simp] = exec_gpv_bind spmf.map_comp o_def map_bind_spmf bind_map_spmf bind_spmf_const

  show ?thesis
    apply (rule ext)
    apply (rule ext)
    subgoal for s query
      apply (cases s)
      subgoal for s_core s_event s_rest
        apply (cases query)
        subgoal for q_adv
          apply (cases q_adv)
          subgoal for q_acore
            by (simp add: apply_state_iso_def iso_swapar_def fused_resource.fuse.simps split_def map_prod_def)
          subgoal for q_arest
            apply (simp add: apply_state_iso_def iso_swapar_def fused_resource.fuse.simps)
            apply (simp add: translate_eoracle_def split_def)
            apply(rule bind_spmf_cong[OF refl])
            apply(subst foldl_spmf_chain[simplified split_def])
            by simp
          done
        subgoal for q_usr
          apply (cases q_usr)
          subgoal for q_ucore
            by (simp add: apply_state_iso_def iso_swapar_def fused_resource.fuse.simps split_def map_prod_def)
          subgoal for q_urest
            apply (simp add: apply_state_iso_def iso_swapar_def fused_resource.fuse.simps)
            apply (simp add: translate_eoracle_def split_def)
            apply(rule bind_spmf_cong[OF refl])
            apply(subst foldl_spmf_chain[simplified split_def])
            by simp
          done
        done
      done
    done
qed



end


\<comment> \<open>Moving interfaces between rest and core\<close>

lemma
  fuse_ishift_core_to_rest:
  assumes "cpoke core' = (\<lambda>s. case_sum (\<lambda>q. fn s q) (cpoke core s))"
      and "cfunc_adv core = cfunc_adv core'"
      and "cfunc_usr core = cfunc_usr core' \<oplus>\<^sub>O (\<lambda>s i. map_spmf (Pair (h_out i)) (fn s i))"
      and "rfunc_adv rest' = (\<lambda>s q. map_spmf (apfst (apsnd (map Inr))) (rfunc_adv rest s q))"
      and "rfunc_usr rest' = plus_eoracle (\<lambda>s i. return_spmf ((h_out i, [i]), s)) (rfunc_usr rest)"
    shows "fused_resource.fuse core rest = apply_wiring (1\<^sub>w |\<^sub>w lassocr\<^sub>w) (fused_resource.fuse core' rest')" (is "?L = ?R")
proof -
  note [simp] = fused_resource.fuse.simps apply_wiring_def lassocr\<^sub>w_def parallel2_wiring_def 
    plus_eoracle_def map_spmf_conv_bind_spmf map_prod_def map_fun_def split_def o_def

  have "?L s q = ?R s q" for s q
    apply (cases q; cases s)
    subgoal for q_adv
      by (cases q_adv) (simp_all add: assms(1, 2, 4))
    subgoal for q_usr
      apply (cases q_usr)
      subgoal for q_usr_core
        apply (cases q_usr_core)
        subgoal for q_nrm
          by (simp add: assms(3))
        by (simp add: assms(1, 3, 5))
      by (simp add: assms(1, 5))
    done

  then show ?thesis
    by blast
qed


lemma move_simulator_interface:
  defines "x_ifunc \<equiv> (\<lambda>ifunc core (se, sc) q. do {
      ((out, es), se') \<leftarrow> ifunc se q;
      sc' \<leftarrow> foldl_spmf (cpoke core) (return_spmf sc) es;
      return_spmf (out, se', sc')   })"
  assumes "cpoke core' = cpoke (translate_core etran core)"
      and "cfunc_adv core' = \<dagger>(cfunc_adv core) \<oplus>\<^sub>O x_ifunc ifunc core"
      and "cfunc_usr core' = cfunc_usr (translate_core etran core)"
      and "rinit rest = (einit, rinit rest')"
      and "rfunc_adv rest = (\<lambda>s q. case q of 
        Inl ql \<Rightarrow> map_spmf (apfst (map_prod Inl id)) ((ifunc\<dagger>) s ql)
      | Inr qr \<Rightarrow> map_spmf (apfst (map_prod Inr id)) ((translate_eoracle etran (\<dagger>(rfunc_adv rest'))) s qr))"
      and "rfunc_usr rest = translate_eoracle etran (\<dagger>(rfunc_usr rest'))"
  shows "fused_resource.fuse core rest =  apply_wiring (rassocl\<^sub>w |\<^sub>w (id, id))
       (apply_state_iso (rprodl o (apfst prod.swap), (apfst prod.swap) o lprodr)
         (fused_resource.fuse core' rest'))"
    (is "?L = ?R")
proof -
  note [simp] = fused_resource.fuse.simps apply_wiring_def rassocl\<^sub>w_def parallel2_wiring_def apply_state_iso_def
    exec_gpv_bind spmf.map_comp map_bind_spmf bind_map_spmf bind_spmf_const o_def split_def

  have "?L (sc, st, sr) q = ?R (sc, st, sr) q" for sc st sr q
  apply (simp add: map_fun_def map_prod_def prod.swap_def apfst_def lprodr_def rprodl_def id_def)
    using assms apply (cases q)
    subgoal for q_adv
      apply (cases q_adv)
      subgoal for q_adv_core
        by (simp add: map_prod_def)
      subgoal for q_adv_rest
        apply (cases q_adv_rest)
        subgoal for q_adv_rest_ifunc
          by simp
        subgoal for q_adv_rest_etran
          apply (simp add: translate_eoracle_def)
          apply(rule bind_spmf_cong[OF refl])
          apply(subst foldl_spmf_chain[simplified split_def])
          by simp
        done
      done
    subgoal for q_usr
      apply (cases q_usr)
      subgoal for q_usr_core
        by (simp add: map_prod_def)
      subgoal for q_usr_rest
        apply (simp add: translate_eoracle_def extend_state_oracle_def)
        apply(rule bind_spmf_cong[OF refl])
            apply(subst foldl_spmf_chain[simplified split_def])
          by simp
      done
    done

  then show ?thesis
    by force
qed


end
