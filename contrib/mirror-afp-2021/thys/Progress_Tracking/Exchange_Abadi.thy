section \<open>Clocks Protocol\label{sec:clocks}\<close>

(*<*)
theory Exchange_Abadi
  imports
    Auxiliary
begin
(*>*)

type_synonym 't count_vec = "'t multiset"
type_synonym 't delta_vec = "'t zmultiset"

definition vacant_upto :: "'t delta_vec \<Rightarrow> 't :: order \<Rightarrow> bool" where
  "vacant_upto a t = (\<forall>s. s \<le> t \<longrightarrow> zcount a s = 0)"

abbreviation nonpos_upto :: "'t delta_vec \<Rightarrow> 't :: order \<Rightarrow> bool" where
  "nonpos_upto a t \<equiv> \<forall>s. s \<le> t \<longrightarrow> zcount a s \<le> 0"

definition supported_strong :: "'t delta_vec \<Rightarrow> 't :: order \<Rightarrow> bool" where
  "supported_strong a t = (\<exists>s. s < t \<and> zcount a s < 0 \<and> nonpos_upto a s)"

definition supported :: "'t delta_vec \<Rightarrow> 't :: order \<Rightarrow> bool" where
  "supported a t = (\<exists>s. s < t \<and> zcount a s < 0)"

definition upright :: "'t :: order delta_vec \<Rightarrow> bool" where
  "upright a = (\<forall>t. zcount a t > 0 \<longrightarrow> supported a t)"

lemma upright_alt:  "upright a \<longleftrightarrow> (\<forall>t. zcount a t > 0 \<longrightarrow> supported_strong a t)"
  unfolding upright_def supported_def supported_strong_def
  by (rule iffI) (meson order.strict_trans2 order.strict_trans1 order_zmset_exists_foundation')+

definition beta_upright :: "'t :: order delta_vec \<Rightarrow> 't :: order delta_vec \<Rightarrow> bool" where
  "beta_upright va vb = (\<forall>t. zcount va t > 0 \<longrightarrow> (\<exists>s. s < t \<and> (zcount va s < 0 \<or> zcount vb s < 0)))"

lemma beta_upright_alt:
  "beta_upright va vb = (\<forall>t. zcount va t > 0 \<longrightarrow> (\<exists>s. s < t \<and> (zcount va s < 0 \<or> zcount vb s < 0) \<and> nonpos_upto va s))"
  unfolding beta_upright_def
  apply (rule iffI)
   apply clarsimp
   apply (drule order_zmset_exists_foundation)
   apply (metis le_less_linear less_le_trans order.strict_trans1)
  apply blast
  done

(* count_vec: nrec, the occupancy vector
   ('p \<Rightarrow> delta_vec): temp, the local change in the occupancy vector due to ops performed at given processor
   ('p \<Rightarrow> 'p \<Rightarrow> delta_vec list): msg, queue of updates from one processor to another
   ('p \<Rightarrow> delta_vec): glob, given processors (delayed) view of the occupancy vector *)
record ('p, 't) configuration =
  c_records :: "'t delta_vec"
  c_temp :: "'p \<Rightarrow> 't delta_vec"
  c_msg :: "'p \<Rightarrow> 'p \<Rightarrow> 't delta_vec list"
  c_glob :: "'p \<Rightarrow> 't delta_vec"

type_synonym ('p, 't) computation = "('p, 't) configuration stream"

definition init_config :: "('p :: finite, 't :: order) configuration \<Rightarrow> bool" where
  "init_config c =
     ((\<forall>p. c_temp c p = {#}\<^sub>z) \<and>
      (\<forall>p1 p2. c_msg c p1 p2 = []) \<and>
      (\<forall>p. c_glob c p = c_records c) \<and>
      (\<forall>t. 0 \<le> zcount (c_records c) t))"

definition next_performop' :: "('p, 't :: order) configuration \<Rightarrow> ('p, 't) configuration \<Rightarrow> 'p \<Rightarrow> 't count_vec \<Rightarrow> 't count_vec \<Rightarrow> bool" where
  "next_performop' c0 c1 p c r =
   (let \<Delta> = zmset_of r - zmset_of c in
      (\<forall>t. int (count c t) \<le> zcount (c_records c0) t)
    \<and> upright \<Delta>
    \<and> c1 = c0\<lparr>c_records := c_records c0 + \<Delta>,
              c_temp := (c_temp c0)(p := c_temp c0 p + \<Delta>)\<rparr>)"

abbreviation next_performop where
  "next_performop s \<equiv> (\<exists>p (c :: 't :: order count_vec) (r::'t count_vec). next_performop' (shd s) (shd (stl s)) p c r)"

definition next_sendupd' where
  "next_sendupd' c0 c1 p tt =
   (let \<gamma> = {#t \<in>#\<^sub>z c_temp c0 p. t \<in> tt#} in
      \<gamma> \<noteq> 0
    \<and> upright (c_temp c0 p - \<gamma>)
    \<and> c1 = c0\<lparr>c_msg := (c_msg c0)(p := \<lambda>q. c_msg c0 p q @ [\<gamma>]),
              c_temp := (c_temp c0)(p := c_temp c0 p - \<gamma>)\<rparr>)"

abbreviation next_sendupd where
  "next_sendupd s \<equiv> (\<exists>p tt. next_sendupd' (shd s) (shd (stl s)) p tt)"

definition next_recvupd' where
  "next_recvupd' c0 c1 p q =
   (c_msg c0 p q \<noteq> []
    \<and> c1 = c0\<lparr>c_msg := (c_msg c0)(p := (c_msg c0 p)(q := tl (c_msg c0 p q))),
              c_glob := (c_glob c0)(q := c_glob c0 q + hd (c_msg c0 p q))\<rparr>)"

abbreviation next_recvupd where
  "next_recvupd s \<equiv> (\<exists>p q. next_recvupd' (shd s) (shd (stl s)) p q)"

definition "next" where
  "next s = (next_performop s \<or> next_sendupd s \<or> next_recvupd s \<or> (shd (stl s) = shd s))"

definition spec :: "('p :: finite, 't :: order) computation \<Rightarrow> bool" where
  "spec s = (holds init_config s \<and> alw next s)"

abbreviation GlobVacantUpto where
  "GlobVacantUpto c q t \<equiv> vacant_upto (c_glob c q) t"

abbreviation NrecVacantUpto where
  "NrecVacantUpto c t \<equiv> vacant_upto (c_records c) t"

(* This is the main safety property (safe) *)
definition SafeGlobVacantUptoImpliesStickyNrec :: "('p :: finite, 't :: order) computation \<Rightarrow> bool" where
  "SafeGlobVacantUptoImpliesStickyNrec s =
     (let c = shd s in \<forall>t q. GlobVacantUpto c q t \<longrightarrow> alw (holds (\<lambda>c. NrecVacantUpto c t)) s)"

(* This is safe2 *)
definition SafeStickyNrecVacantUpto :: "('p :: finite, 't :: order) computation \<Rightarrow> bool" where
  "SafeStickyNrecVacantUpto s =
     (let c = shd s in \<forall>t. NrecVacantUpto c t \<longrightarrow> alw (holds (\<lambda>c. NrecVacantUpto c t)) s)"

(* This is inv1 *)
definition InvGlobVacantUptoImpliesNrec :: "('p :: finite, 't :: order) configuration \<Rightarrow> bool" where
  "InvGlobVacantUptoImpliesNrec c =
     (\<forall>t q. vacant_upto (c_glob c q) t \<longrightarrow> vacant_upto (c_records c) t)"

definition InvTempUpright where
  "InvTempUpright c = (\<forall>p. upright (c_temp c p))"

lemma init_InvTempUpright: "init_config c \<Longrightarrow> InvTempUpright c"
  by (simp add: InvTempUpright_def init_config_def upright_def)

lemma upright_obtain_support:
  assumes "upright a"
    and "zcount a t > 0"
  obtains s where "s < t" "zcount a s < 0" "nonpos_upto a s"
  using assms unfolding upright_alt supported_strong_def
  apply atomize_elim
  using order.strict_implies_order apply blast
  done

lemma upright_vec_add:
  assumes "upright v1"
    and   "upright v2"
  shows   "upright (v1 + v2)"
proof -
  let ?v0 = "v1 + v2"
  { fix t
    assume upr1: "upright v1"
    assume upr2: "upright v2"
    assume zcnt: "0 < zcount ?v0 t"
    { fix va vb :: "'a zmultiset"
      fix t
      assume upra: "upright va"
      assume uprb: "upright vb"
      assume zcnt: "0 < zcount va t"
      from upra zcnt obtain x where x: "x < t" "zcount va x < 0" "nonpos_upto va x"
        using upright_obtain_support by blast
      with uprb have "supported_strong (va+vb) t"
        apply (cases "\<exists>s. s \<le> x \<and> 0 < zcount vb s")
         apply (clarsimp simp: upright_alt supported_strong_def)
         apply (meson add_nonpos_neg less_imp_le order.strict_trans2 order.trans add_nonpos_nonpos)
        apply simp
        apply (force simp: supported_strong_def intro!: exI[of _ x])
        done
    }
    with upr1 upr2 zcnt have "supported_strong ?v0 t" unfolding supported_strong_def
      apply (cases "0 < zcount v1 t"; cases "0 < zcount v2 t")
         apply auto [2]
       apply (subst (1 2) add.commute)
       apply auto
      done
  }
  with assms show ?thesis
    by (simp add: upright_alt)
qed

lemma next_InvTempUpright: "holds InvTempUpright s \<Longrightarrow> next s \<Longrightarrow> nxt (holds InvTempUpright) s"
  unfolding next_def apply simp
  apply (elim disjE)
  subgoal
    unfolding InvTempUpright_def next_performop'_def
    by (auto simp: Let_def upright_vec_add)
  subgoal
    unfolding InvTempUpright_def next_sendupd'_def
    by (auto simp: Let_def upright_vec_add)
  subgoal
    unfolding InvTempUpright_def next_recvupd'_def
    by (auto simp: upright_vec_add)
  subgoal by simp
  done

lemma alw_InvTempUpright: "spec s \<Longrightarrow> alw (holds InvTempUpright) s"
  apply (rule alw_invar)
   apply (simp add: spec_def init_InvTempUpright)
  apply (metis (no_types, lifting) alw_iff_sdrop next_InvTempUpright spec_def)
  done

definition IncomingInfo where
  "IncomingInfo c k p q = (sum_list (drop k (c_msg c p q)) + c_temp c p)"

definition InvIncomingInfoUpright where
  "InvIncomingInfoUpright c = (\<forall>k p q. upright (IncomingInfo c k p q))"

lemma upright_0: "upright 0"
  by (simp add: upright_def)

lemma init_InvIncomingInfoUpright: "init_config c \<Longrightarrow> InvIncomingInfoUpright c"
  by (simp add: upright_0 upright_vec_add init_config_def InvIncomingInfoUpright_def IncomingInfo_def)

lemma next_InvIncomingInfoUpright: "holds InvIncomingInfoUpright s \<Longrightarrow> next s \<Longrightarrow> nxt (holds InvIncomingInfoUpright) s"
  unfolding next_def
  apply simp
  apply (elim disjE)
  subgoal
    by (auto simp: add.assoc[symmetric] upright_vec_add next_performop'_def Let_def InvIncomingInfoUpright_def IncomingInfo_def)
  subgoal
    unfolding next_sendupd'_def Let_def InvIncomingInfoUpright_def IncomingInfo_def
    apply clarsimp
    subgoal for p tt k q
      apply (cases "k \<le> length (c_msg (shd s) p q)")
       apply auto
      done
    done
  subgoal
    unfolding next_recvupd'_def Let_def InvIncomingInfoUpright_def IncomingInfo_def
    apply (clarsimp simp: drop_Suc[symmetric])
    done
  subgoal
    by simp
  done

lemma alw_InvIncomingInfoUpright: "spec s \<Longrightarrow> alw (holds InvIncomingInfoUpright) s"
  by (metis (mono_tags, lifting) alw_iff_sdrop alw_invar holds.elims(2) holds.elims(3) init_InvIncomingInfoUpright next_InvIncomingInfoUpright spec_def)

definition GlobalIncomingInfo :: "('p :: finite, 't) configuration \<Rightarrow> nat \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 't delta_vec" where
  "GlobalIncomingInfo c k p q = (\<Sum>p' \<in> UNIV. IncomingInfo c (if p' = p then k else 0) p' q)"

(* (GlobalIncomingInfo c 0 q q) sums up all info incoming at q *)
abbreviation GlobalIncomingInfoAt where
  "GlobalIncomingInfoAt c q \<equiv> GlobalIncomingInfo c 0 q q"

definition InvGlobalRecordCount where
  "InvGlobalRecordCount c = (\<forall>q. c_records c = GlobalIncomingInfoAt c q + c_glob c q)"

lemma init_InvGlobalRecordCount: "holds init_config s \<Longrightarrow> holds InvGlobalRecordCount s"
  by (simp add: InvGlobalRecordCount_def init_config_def GlobalIncomingInfo_def IncomingInfo_def)

lemma if_eq_same: "(if a = b then f b else f a) = f a"
  by auto

lemma next_InvGlobalRecordCount: "holds InvGlobalRecordCount s \<Longrightarrow> next s \<Longrightarrow> nxt (holds InvGlobalRecordCount) s"
  unfolding InvGlobalRecordCount_def init_config_def GlobalIncomingInfo_def IncomingInfo_def next_def
  apply (elim disjE)
  subgoal
    apply (clarsimp simp: next_performop'_def Let_def)
    subgoal for p c q r
      apply (simp add: sum.distrib)
      apply (subst sum_if_distrib_add)
        apply (simp_all add: add.assoc)
      done
    done
  subgoal
    apply (clarsimp simp: next_sendupd'_def Let_def)
    subgoal for p tt q
      apply (simp add: if_distrib[of "\<lambda>f. f _"])
      apply (simp add: if_distrib[of sum_list])
      apply (subst sum_list_append)
      apply (simp add: sum.distrib)
      apply (subst sum_if_distrib_add)
        apply simp
       apply simp
      apply (subst diff_conv_add_uminus)
      apply (subst sum_if_distrib_add)
        apply (auto simp: sum_if_distrib_add)
      done
    done
  subgoal
    apply (clarsimp simp: next_recvupd'_def Let_def fun_upd_def)
    subgoal for p q q'
      apply (simp add: if_distrib[of "\<lambda>f. f _"])
      apply safe
       apply (simp add: if_distrib[of sum_list])
       apply (subst sum_list_hd_tl)
        apply simp
       apply (subst add.commute)
       apply (simp add: sum.distrib)
       apply (subst sum_if_distrib_add)
         apply simp
        apply simp
       apply (simp add: add.assoc)
      apply (subst if_eq_same)
      apply simp
      done
    done
  subgoal
    by simp
  done

(* This is inv2 in the short paper *)
lemma alw_InvGlobalRecordCount: "spec s \<Longrightarrow> alw (holds InvGlobalRecordCount) s"
  by (metis (no_types, lifting) alw_iff_sdrop alw_invar init_InvGlobalRecordCount next_InvGlobalRecordCount spec_def)

definition InvGlobalIncomingInfoUpright where
  "InvGlobalIncomingInfoUpright c = (\<forall>k p q. upright (GlobalIncomingInfo c k p q))"

lemma upright_sum_upright: "finite X \<Longrightarrow> \<forall>x. upright (A x) \<Longrightarrow> upright (\<Sum>x\<in>X. A x)"
  by (induct X rule: finite_induct) (auto simp: upright_0 upright_vec_add)

lemma InvIncomingInfoUpright_imp_InvGlobalIncomingInfoUpright: "holds InvIncomingInfoUpright s \<Longrightarrow> holds InvGlobalIncomingInfoUpright s"
  by (simp add: InvIncomingInfoUpright_def InvGlobalIncomingInfoUpright_def GlobalIncomingInfo_def upright_sum_upright)

(* This is inv6 in the short paper *)
lemma alw_InvGlobalIncomingInfoUpright: "spec s \<Longrightarrow> alw (holds InvGlobalIncomingInfoUpright) s"
  using InvIncomingInfoUpright_imp_InvGlobalIncomingInfoUpright alw_InvIncomingInfoUpright alw_mono by blast

abbreviation nrec_pos where
  "nrec_pos c \<equiv> \<forall>t. zcount (c_records c) t \<ge> 0"

lemma init_nrec_pos: "holds init_config s \<Longrightarrow> holds nrec_pos s"
  by (simp add: init_config_def)

lemma next_nrec_pos: "holds nrec_pos s \<Longrightarrow> next s \<Longrightarrow> nxt (holds nrec_pos) s"
  unfolding next_def
  apply simp
  apply clarify
  apply (elim disjE)
  subgoal for t
    unfolding next_performop'_def Let_def
    apply clarify
    subgoal for p c r
      apply (simp add: add_diff_eq add.commute add_increasing)
      done
    done
  subgoal for t
    by (auto simp: next_sendupd'_def Let_def)
  subgoal for t
    by (auto simp: next_recvupd'_def Let_def)
  subgoal
    by simp
  done

lemma alw_nrec_pos: "spec s \<Longrightarrow> alw (holds nrec_pos) s"
  by (metis (mono_tags, lifting) alw_iff_sdrop alw_invar init_nrec_pos next_nrec_pos spec_def)

lemma next_performop_vacant:
  "vacant_upto (c_records (shd s)) t \<Longrightarrow> next_performop s \<Longrightarrow> vacant_upto (c_records (shd (stl s))) t"
  unfolding next_performop'_def Let_def vacant_upto_def
  apply clarsimp
  subgoal for p c u r
    apply (clarsimp simp: upright_def supported_def)
    apply (metis (no_types, hide_lams) gr_implies_not_zero of_nat_le_0_iff order.strict_implies_order order_trans zero_less_iff_neq_zero)
    done
  done

lemma next_sendupd_vacant:
  "vacant_upto (c_records (shd s)) t \<Longrightarrow> next_sendupd s \<Longrightarrow> vacant_upto (c_records (shd (stl s))) t"
  by (auto simp add: next_sendupd'_def Let_def)

lemma next_recvupd_vacant:
  "vacant_upto (c_records (shd s)) t \<Longrightarrow> next_recvupd s \<Longrightarrow> vacant_upto (c_records (shd (stl s))) t"
  by (auto simp add: next_recvupd'_def Let_def)

lemma spec_imp_SafeStickyNrecVacantUpto_aux: "alw next s \<Longrightarrow> alw SafeStickyNrecVacantUpto s"
  apply (coinduction arbitrary: s)
  subgoal for s
    unfolding spec_def next_def SafeStickyNrecVacantUpto_def Let_def
    apply (rule exI[of _ s])
    apply safe
    subgoal for t
      apply (coinduction arbitrary: s rule: alw.coinduct)
      apply clarsimp
      apply (rule conjI)
       apply blast
      apply (erule alw.cases)
      apply clarsimp
      apply (elim disjE)
         apply (simp_all add: next_performop_vacant next_sendupd_vacant next_recvupd_vacant)
      done
    by blast
  done

lemma spec_imp_SafeStickyNrecVacantUpto: "spec s \<Longrightarrow> alw SafeStickyNrecVacantUpto s"
  unfolding spec_def
  by (blast intro: spec_imp_SafeStickyNrecVacantUpto_aux)

lemma invs_imp_InvGlobVacantUptoImpliesNrec:
  assumes "holds InvGlobalIncomingInfoUpright s"
  assumes "holds InvGlobalRecordCount s"
  assumes "holds nrec_pos s"
  shows "holds InvGlobVacantUptoImpliesNrec s"
  using assms unfolding InvGlobVacantUptoImpliesNrec_def
  apply simp
  apply clarify
  apply (rule ccontr)
  apply (simp add: vacant_upto_def)
  apply clarify
  subgoal for t q u
  proof -
    assume globvut: "\<forall>sa\<le>t. zcount (c_glob (shd s) q) sa = 0"
    assume uleqt: "u \<le> t"
    assume "u \<in>#\<^sub>z c_records (shd s)"
    with assms(3) have "0 < zcount (c_records (shd s)) u"
      by (simp add: order.not_eq_order_implies_strict)
    with assms(2) globvut uleqt have *: "0 < zcount (GlobalIncomingInfoAt (shd s) q) u"
      unfolding InvGlobalRecordCount_def
      by (auto dest: spec[of _ q])
    from assms(1)[unfolded InvGlobalIncomingInfoUpright_def] have "upright (GlobalIncomingInfoAt (shd s) q)"
      by simp
    with * obtain v where **: "v \<le> u" "zcount (GlobalIncomingInfoAt (shd s) q) v < 0"
      by (meson order.strict_iff_order upright_def supported_def)
    with assms(2) have "zcount (c_records (shd s)) v < 0"
      by (metis (no_types, hide_lams) InvGlobalRecordCount_def add.right_neutral order.trans globvut holds.elims(2) uleqt zcount_union)
    with assms(3) show "False"
      using atLeastatMost_empty by auto
  qed
  done

lemma spec_imp_inv1: "spec s \<Longrightarrow> alw (holds InvGlobVacantUptoImpliesNrec) s"
  by (metis (mono_tags, lifting) alw_iff_sdrop invs_imp_InvGlobVacantUptoImpliesNrec alw_InvGlobalIncomingInfoUpright alw_InvGlobalRecordCount alw_nrec_pos)

lemma safe2_inv1_imp_safe: "SafeStickyNrecVacantUpto s \<Longrightarrow> holds InvGlobVacantUptoImpliesNrec s \<Longrightarrow> SafeGlobVacantUptoImpliesStickyNrec s"
  by (simp add: InvGlobVacantUptoImpliesNrec_def SafeStickyNrecVacantUpto_def SafeGlobVacantUptoImpliesStickyNrec_def)

lemma spec_imp_safe: "spec s \<Longrightarrow> alw SafeGlobVacantUptoImpliesStickyNrec s"
  by (meson alw_iff_sdrop safe2_inv1_imp_safe spec_imp_SafeStickyNrecVacantUpto spec_imp_inv1)



(* Second safety property from here on (glob stays vacant) *)

lemma beta_upright_0: "beta_upright 0 vb"
  unfolding beta_upright_def
  by auto

definition PositiveImplies where
  "PositiveImplies v w = (\<forall>t. zcount v t > 0 \<longrightarrow> zcount w t > 0)"

lemma betaupright_PositiveImplies: "upright (va + vb) \<Longrightarrow> PositiveImplies va (va + vb) \<Longrightarrow> beta_upright va vb"
  unfolding beta_upright_def PositiveImplies_def
  apply clarify
  subgoal for t
    apply (erule upright_obtain_support[of _ t])
     apply simp
    subgoal for s
      apply (rule exI[of _ s])
      apply simp
      apply (simp add: add_less_zeroD)
      done
    done
  done

lemma betaupright_obtain_support:
  assumes "beta_upright va vb"
    "zcount va t > 0"
  obtains s where "s < t" "zcount va s < 0 \<or> zcount vb s < 0" "nonpos_upto va s"
  using assms by (auto simp: beta_upright_alt)

lemma betaupright_upright_vut:
  assumes "beta_upright va vb"
    and     "upright vb"
    and     "vacant_upto (va + vb) t"
  shows   "vacant_upto va t"
proof -
  { fix s
    assume s: "s \<le> t" "zcount va s > 0"
    with assms obtain x where x: "x < s" "zcount va x < 0 \<or> zcount vb x < 0" "nonpos_upto va x"
      using betaupright_obtain_support by blast
    then have False
    proof (cases "zcount va x < 0")
      case True
      with assms(2,3) s x(1,3) show ?thesis
        unfolding vacant_upto_def
        apply clarsimp
        apply (erule upright_obtain_support[of vb x])
         apply (metis add_less_same_cancel2 order.trans order.strict_implies_order)
        apply (metis add_less_same_cancel1 add_neg_neg order.order_iff_strict order.trans less_irrefl)
        done
    next
      case False
      with assms s x have "x \<le> t" "zcount va x > 0"
         apply -
         apply simp
        apply (metis (no_types, hide_lams) add.left_neutral order.order_iff_strict order.trans vacant_upto_def zcount_union)
        done
      with assms(2,3) s x show ?thesis
        by force
    qed
  }
  note r = this
  from assms(2,3) show ?thesis
    unfolding vacant_upto_def
    apply clarsimp
    apply (metis (no_types, hide_lams) r add_cancel_right_left order.order_iff_strict order.trans le_less_linear less_add_same_cancel2 upright_obtain_support)
    done
qed

lemma beta_upright_add:
  assumes "upright vb"
    and     "upright vc"
    and     "beta_upright va vb"
  shows   "beta_upright va (vb + vc)"
proof -
  { fix t
    assume "0 < zcount va t"
    assume assm: "\<not>(\<exists>s<t. (zcount va s < 0 \<or> zcount vb s + zcount vc s < 0) \<and> \<not>(\<exists>u \<le> s. zcount va u > 0))"
    from \<open>0 < zcount va t\<close> assms(3) obtain x where x: "x < t \<and> (zcount va x < 0 \<or> zcount vb x < 0) \<and> nonpos_upto va x"
      using betaupright_obtain_support by blast
    then have "\<not> zcount va x < 0"
      using assm by force
    with x have "zcount vb x < 0"
      by blast
    from assm x have "\<not> zcount vb x + zcount vc x < 0"
      using not_le by blast
    with \<open>zcount vb x < 0\<close> have "zcount vc x > 0"
      by clarsimp
    with assms(2) obtain y where y: "y < x \<and> zcount vc y < 0 \<and> nonpos_upto vc y"
      using upright_obtain_support by blast
    with x have "y < t"
      using order.strict_trans by blast
    from assm x y have "\<not> zcount vb y + zcount vc y < 0"
      by (metis order.strict_implies_order order.strict_trans1 not_less)
    with y have "zcount vb y > 0"
      by linarith
    with assms(1) obtain z where z: "z < y \<and> zcount vb z < 0"
      by (auto simp: upright_def supported_def)
    with \<open>y < t\<close> have "z < t"
      using order.strict_trans by blast
    with x y z have "\<not> zcount vb z + zcount vc z < 0"
      by (metis assm less_imp_le not_less order.strict_trans order.strict_trans1)
    with z have "zcount vc z > 0"
      by linarith
    with y z have "False"
      using order.strict_implies_order not_less by blast
  }
  then show ?thesis
    using beta_upright_def zcount_union by fastforce
qed

definition InfoAt where
  "InfoAt c k p q = (if 0 \<le> k \<and> k < length (c_msg c p q) then (c_msg c p q) ! k else 0)"

definition InvInfoAtBetaUpright where
  "InvInfoAtBetaUpright c = (\<forall>k p q. beta_upright (InfoAt c k p q) (IncomingInfo c (k+1) p q))"

lemma init_InvInfoAtBetaUpright: "init_config c \<Longrightarrow> InvInfoAtBetaUpright c"
  unfolding init_config_def InvInfoAtBetaUpright_def beta_upright_def IncomingInfo_def InfoAt_def
  by simp

lemma next_inv[consumes 1, case_names next_performop next_sendupd next_recvupd stutter]:
  assumes "next s"
    and     "next_performop s \<Longrightarrow> P"
    and     "next_sendupd s \<Longrightarrow> P"
    and     "next_recvupd s \<Longrightarrow> P"
    and     "shd (stl s) = shd s \<Longrightarrow> P"
  shows   "P"
  using assms unfolding next_def by blast


lemma next_InvInfoAtBetaUpright:
  assumes a1: "next s"
    and     a2: "InvInfoAtBetaUpright (shd s)"
    and     a3: "InvIncomingInfoUpright (shd s)"
    and     a4: "InvTempUpright (shd s)"
  shows   "InvInfoAtBetaUpright (shd (stl s))"
  using assms
proof (cases rule: next_inv)
  case next_performop
  then show ?thesis
    unfolding next_performop'_def Let_def InvInfoAtBetaUpright_def
    apply clarify
    subgoal for p c r k' p' q'
    proof (cases "p=p'")
      let ?\<Delta> = "zmset_of r - zmset_of c"
      assume upright_\<Delta>: "upright ?\<Delta>"
      assume conf: "shd (stl s) = shd s\<lparr>c_records := c_records (shd s) + (zmset_of r - zmset_of c),
        c_temp := (c_temp (shd s))(p := c_temp (shd s) p + (zmset_of r - zmset_of c))\<rparr>"
      case True
      then have iid: "IncomingInfo (shd (stl s)) (k'+1) p' q' = IncomingInfo (shd s) (k'+1) p' q' + ?\<Delta>"
        by (simp add: IncomingInfo_def conf)
      from a2 have bu: "beta_upright (InfoAt (shd s) k' p' q') (IncomingInfo (shd s) (k'+1) p' q')"
        using InvInfoAtBetaUpright_def by fastforce
      show ?thesis
        unfolding iid
        apply (rule beta_upright_add)
          apply (meson InvIncomingInfoUpright_def a3)
         apply (rule upright_\<Delta>)
        using bu unfolding conf InfoAt_def
        apply auto
        done
    next
      let ?\<Delta> = "zmset_of r - zmset_of c"
      assume conf: "shd (stl s) = shd s\<lparr>c_records := c_records (shd s) + (zmset_of r - zmset_of c),
        c_temp := (c_temp (shd s))(p := c_temp (shd s) p + (zmset_of r - zmset_of c))\<rparr>"
      from a2 have bu: "beta_upright (InfoAt (shd s) k p q) (IncomingInfo (shd s) (k + 1) p q)" for k p q
        using InvInfoAtBetaUpright_def by fastforce
      case False
      then have ii: "IncomingInfo (shd (stl s)) (k'+1) p' q' = IncomingInfo (shd s) (k'+1) p' q'"
        unfolding IncomingInfo_def by (simp add: conf)
      with bu[of k' p' q'] show ?thesis unfolding conf InfoAt_def
        by auto
    qed
    done
next
  case next_sendupd
  then show ?thesis
    unfolding next_sendupd'_def Let_def InvInfoAtBetaUpright_def
    apply clarify
    subgoal for p tt k' p' q'
    proof (cases "p=p'")
      let ?\<gamma> = "{#t \<in>#\<^sub>z c_temp (shd s) p. t \<in> tt#}"
      assume conf: "shd (stl s) = (shd s)\<lparr>c_msg := (c_msg (shd s))(p := \<lambda>q. c_msg (shd s) p q @ [?\<gamma>]),
              c_temp := (c_temp (shd s))(p := c_temp (shd s) p - ?\<gamma>)\<rparr>"
      from a2 have buia: "beta_upright (InfoAt (shd s) k' p' q') (IncomingInfo (shd s) (k'+1) p' q')"
        using InvInfoAtBetaUpright_def by force
      from a4 have tu: "upright (c_temp (shd s) p)"
        by (simp add: InvTempUpright_def)
      case True
      then show ?thesis
      proof (cases k' rule: linorder_cases[where y = "length (c_msg (shd s) p' q')"])
        case greater
        then have "InfoAt (shd (stl s)) k' p' q' = 0"
          by (auto simp: conf InfoAt_def)
        then show ?thesis
          by (simp add: beta_upright_0)
      next
        case equal
        with True conf have "InfoAt (shd (stl s)) k' p' q' = ?\<gamma>"
          by (simp add: InfoAt_def)
        then have pi: "PositiveImplies (InfoAt (shd (stl s)) k' p' q') (c_temp (shd s) p)"
          by (simp add: PositiveImplies_def)
        from conf have "c_temp (shd s) p = c_temp (shd (stl s)) p + ?\<gamma>"
          by simp
        with equal True conf tu pi have butemp: "beta_upright (InfoAt (shd (stl s)) k' p' q') (c_temp (shd (stl s)) p)"
          apply -
          apply (rule betaupright_PositiveImplies)
           apply (auto simp add: InfoAt_def)
          done
        with True equal conf have "IncomingInfo (shd (stl s)) (k'+1) p' q' = c_temp (shd (stl s)) p"
          by (simp add: IncomingInfo_def)
        with butemp show ?thesis
          by simp
      next
        case less
        with conf have unch_ia: "InfoAt (shd (stl s)) k' p' q' = InfoAt (shd s) k' p' q'"
          by (auto simp: nth_append InfoAt_def)
        from conf less have "IncomingInfo (shd (stl s)) (k'+1) p' q' = IncomingInfo (shd s) (k'+1) p' q'"
          by (auto simp: IncomingInfo_def)
        with buia unch_ia show ?thesis by simp
      qed
    next
      let ?\<gamma> = "{#t \<in>#\<^sub>z c_temp (shd s) p. t \<in> tt#}"
      assume conf: "shd (stl s) = (shd s)\<lparr>c_msg := (c_msg (shd s))(p := \<lambda>q. c_msg (shd s) p q @ [?\<gamma>]),
              c_temp := (c_temp (shd s))(p := c_temp (shd s) p - ?\<gamma>)\<rparr>"
      from a2 have buia: "beta_upright (InfoAt (shd s) k' p' q') (IncomingInfo (shd s) (k'+1) p' q')"
        using InvInfoAtBetaUpright_def by force
      case False
      with conf have unchia: "InfoAt (shd (stl s)) k' p' q' = InfoAt (shd s) k' p' q'"
        by (simp add: InfoAt_def)
      from False conf have unchii: "IncomingInfo (shd (stl s)) (k'+1) p' q' = IncomingInfo (shd s) (k'+1) p' q'"
        by (simp add: IncomingInfo_def)
      from unchia unchii buia show ?thesis
        by simp
    qed
    done
next
  case next_recvupd
  then show ?thesis
    unfolding next_recvupd'_def Let_def InvInfoAtBetaUpright_def
    apply clarify
    subgoal for p q k' p' q'
    proof (cases "p = p' \<and> q = q'")
      assume conf: "shd (stl s) = (shd s)\<lparr>c_msg := (c_msg (shd s))(p := (c_msg (shd s) p)(q := tl (c_msg (shd s) p q))),
              c_glob := (c_glob (shd s))(q := c_glob (shd s) q + hd (c_msg (shd s) p q))\<rparr>"
      case True
      with conf have iisuc: "IncomingInfo (shd (stl s)) (k'+1) p' q' = IncomingInfo (shd s) (k'+2) p' q'"
        by (simp add: drop_Suc IncomingInfo_def)
      with True conf have iasuc: "InfoAt (shd (stl s)) k' p' q' = InfoAt (shd s) (k'+1) p' q'"
        by (simp add: less_diff_conv nth_tl InfoAt_def)
      from a2 have "beta_upright (InfoAt (shd s) (k'+1) p' q') (IncomingInfo (shd s) (k'+2) p' q')"
        using InvInfoAtBetaUpright_def by fastforce
      with iisuc iasuc show ?thesis
        by simp
    next
      assume conf: "shd (stl s) = (shd s)\<lparr>c_msg := (c_msg (shd s))(p := (c_msg (shd s) p)(q := tl (c_msg (shd s) p q))),
              c_glob := (c_glob (shd s))(q := c_glob (shd s) q + hd (c_msg (shd s) p q))\<rparr>"
      from a2 have buia: "beta_upright (InfoAt (shd s) k' p' q') (IncomingInfo (shd s) (k'+1) p' q')"
        by (simp add: InvInfoAtBetaUpright_def)
      case False
      with conf have unchii: "IncomingInfo (shd (stl s)) (k'+1) p' q' = IncomingInfo (shd s) (k'+1) p' q'"
        by (auto simp: IncomingInfo_def)
      from False conf have unchia: "InfoAt (shd (stl s)) k' p' q' = InfoAt (shd s) k' p' q'"
        by (auto simp: InfoAt_def)
      from unchii unchia buia show ?thesis
        by simp
    qed
    done
qed simp

lemma alw_InvInfoAtBetaUpright_aux: "alw (holds InvTempUpright) s \<Longrightarrow> alw (holds InvIncomingInfoUpright) s \<Longrightarrow> holds InvInfoAtBetaUpright s \<Longrightarrow> alw next s \<Longrightarrow> alw (holds InvInfoAtBetaUpright) s"
  by (coinduction arbitrary: s rule: alw.coinduct) (auto intro!: next_InvInfoAtBetaUpright)

lemma alw_InvInfoAtBetaUpright: "spec s \<Longrightarrow> alw (holds InvInfoAtBetaUpright) s"
  by (simp add: alw_InvTempUpright alw_InvIncomingInfoUpright alw_InvInfoAtBetaUpright_aux init_InvInfoAtBetaUpright spec_def)

definition InvGlobalInfoAtBetaUpright where
  "InvGlobalInfoAtBetaUpright c = (\<forall>k p q. beta_upright (InfoAt c k p q) (GlobalIncomingInfo c (k+1) p q))"

lemma finite_induct_select [consumes 1, case_names empty select]:
  assumes "finite S"
    and empty: "P {}"
    and select: "\<And>T. finite T \<Longrightarrow> T \<subset> S \<Longrightarrow> P T \<Longrightarrow> \<exists>s\<in>S - T. P (insert s T)"
  shows "P S"
proof -
  from assms(1) have "P S \<and> finite S"
    by (induct S rule: finite_induct_select) (auto intro: empty select)
  then show ?thesis by blast
qed

lemma predicate_sum_decompose:
  fixes f :: "'a \<Rightarrow> ('b :: ab_group_add)"
  assumes "finite X"
    and     "x\<in>X"
    and     "A (f x)"
    and     "\<forall>Z. B (sum f Z)"
    and     "\<And>x Z. A (f x) \<Longrightarrow> B (sum f Z) \<Longrightarrow> A (f x + sum f Z)"
    and     "\<And>x Z. B (f x) \<Longrightarrow> A (sum f Z) \<Longrightarrow> A (f x + sum f Z)"
  shows "A (\<Sum>x\<in>X. f x)"
  using assms(1,2,3)
  apply (induct X rule: finite_induct_select)
   apply simp
  apply (simp only: sum.insert_remove)
  subgoal for T
    apply (cases "x \<in> T"; simp add: assms(3))
     apply (drule psubset_imp_ex_mem)
     apply clarsimp
    subgoal for z
      apply (rule bexI[of _ z])
       apply (rule assms(6)[of z T])
        apply (rule assms(4)[THEN spec, of "{z}", simplified])
       apply simp
      apply simp
      done
    apply clarsimp
    apply (drule bspec[of _ _ x])
     apply safe
     apply (rule assms(2))
    using assms(4,5) apply blast
    done
  done

lemma invs_imp_InvGlobalInfoAtBetaUpright:
  assumes "holds InvInfoAtBetaUpright s"
    and     "holds InvGlobalIncomingInfoUpright s"
    and     "holds InvIncomingInfoUpright s"
  shows   "holds InvGlobalInfoAtBetaUpright s"
proof -
  have uii: "\<forall>k p q. upright (IncomingInfo (shd s) k p q)"
    by (rule assms(3)[unfolded InvIncomingInfoUpright_def, simplified])
  have ugii: "\<forall>k p q. upright (GlobalIncomingInfo (shd s) k p q)"
    by (rule assms(2)[unfolded InvGlobalIncomingInfoUpright_def, simplified])
  have buia: "\<forall>k p q. beta_upright (InfoAt (shd s) k p q) (IncomingInfo (shd s) (Suc k) p q)"
    by (rule assms(1)[unfolded InvInfoAtBetaUpright_def, simplified])
  from uii ugii buia have "\<forall>k p q. beta_upright (InfoAt (shd s) k p q) (GlobalIncomingInfo (shd s) (Suc k) p q)"
    unfolding GlobalIncomingInfo_def
    apply -
    apply (rule allI)+
    subgoal for k p q
      apply (rule predicate_sum_decompose[of UNIV p "\<lambda>v. beta_upright (InfoAt (shd s) k p q) v" "\<lambda>p'. IncomingInfo (shd s) (if p' = p then Suc k else 0) p' q" upright])
           apply simp
          apply simp
         apply simp
        apply (simp add: upright_sum_upright)
      subgoal for p' X
        apply (rule beta_upright_add)
          apply simp
         apply simp
        apply simp
        done
      subgoal for p' X
        apply (subst add.commute)
        apply (rule beta_upright_add)
          apply simp
          apply (simp add: upright_sum_upright)
         apply clarsimp
        apply simp
        done
      done
    done
  then show ?thesis
    by (simp add: InvGlobalInfoAtBetaUpright_def)
qed

lemma alw_InvGlobalInfoAtBetaUpright: "spec s \<Longrightarrow> alw (holds InvGlobalInfoAtBetaUpright) s"
  by (meson alw_InvGlobalIncomingInfoUpright alw_InvIncomingInfoUpright alw_InvInfoAtBetaUpright alw_iff_sdrop invs_imp_InvGlobalInfoAtBetaUpright)

definition SafeStickyGlobVacantUpto :: "('p :: finite, 't :: order) computation \<Rightarrow> bool" where
  "SafeStickyGlobVacantUpto s = (\<forall>q t. GlobVacantUpto (shd s) q t \<longrightarrow> alw (holds (\<lambda>c. GlobVacantUpto c q t)) s)"

lemma gvut1:
  "GlobVacantUpto (shd s) q t \<Longrightarrow> next_performop s \<Longrightarrow> GlobVacantUpto (shd (stl s)) q t"
  by (auto simp add: next_performop'_def Let_def vacant_upto_def upright_def)

lemma gvut2:
  "GlobVacantUpto (shd s) q t \<Longrightarrow> next_sendupd s \<Longrightarrow> GlobVacantUpto (shd (stl s)) q t"
  by (auto simp add: next_sendupd'_def Let_def)

lemma gvut3:
  assumes
    gvu: "GlobVacantUpto (shd s) q t" and
    igvuin: "InvGlobVacantUptoImpliesNrec (shd s)" and
    igrc: "InvGlobalRecordCount (shd s)" and
    igiiu: "InvGlobalIncomingInfoUpright (shd s)" and
    igiabu: "InvGlobalInfoAtBetaUpright (shd s)" and
    "next": "next_recvupd s"
  shows "GlobVacantUpto (shd (stl s)) q t"
proof -
  { fix p
    let ?GII0 = "GlobalIncomingInfo (shd s) 0 p q"
    let ?GII1 = "GlobalIncomingInfo (shd s) 1 p q"
    let ?\<kappa> = "hd (c_msg (shd s) p q)"
    from igiiu have uGII1: "upright ?GII1"
      unfolding InvGlobalIncomingInfoUpright_def by simp
    assume globk: "c_glob (shd (stl s)) q = c_glob (shd s) q + ?\<kappa>"
    assume nonempty: "c_msg (shd s) p q \<noteq> []"
    then have sumGIIsk: "?GII0 = ?GII1 + ?\<kappa>"
      unfolding GlobalIncomingInfo_def IncomingInfo_def
      by (auto simp: sum.remove ac_simps neq_Nil_conv)
    from nonempty have IA0k: "?\<kappa> = InfoAt (shd s) 0 p q"
      by (simp add: InfoAt_def hd_conv_nth)
    from igiabu nonempty have bukGII1: "beta_upright ?\<kappa> ?GII1"
    proof -
      note igiabu
      then have "beta_upright (InfoAt (shd s) 0 p q) (GlobalIncomingInfo (shd s) 1 p q)"
        by (simp add: InvGlobalInfoAtBetaUpright_def)
      with IA0k show ?thesis
        by simp
    qed
    from igvuin gvu have nvu: "NrecVacantUpto (shd s) t"
      unfolding InvGlobVacantUptoImpliesNrec_def by blast
    with igrc have "c_records (shd s) = c_glob (shd s) q + ?GII0"
      unfolding GlobalIncomingInfo_def IncomingInfo_def InvGlobalRecordCount_def
      by (simp add: add.commute)
    with gvu nvu have vuGII0: "vacant_upto ?GII0 t"
      by (simp add: vacant_upto_def)
    from bukGII1 uGII1 have "vacant_upto ?\<kappa> t"
      by (rule betaupright_upright_vut[of ?\<kappa> ?GII1]) (metis vuGII0 add.commute sumGIIsk)
    with gvu have "GlobVacantUpto (shd (stl s)) q t"
      by (simp add: globk vacant_upto_def)
  }
  then show ?thesis
    using assms unfolding next_recvupd'_def
    by auto
qed

lemma spec_imp_SafeStickyGlobVacantUpto_aux:
  assumes
    "alw (holds (\<lambda>c. InvGlobVacantUptoImpliesNrec c)) s" and
    "alw (holds (\<lambda>c. InvGlobalRecordCount c)) s" and
    "alw (holds (\<lambda>c. InvGlobalIncomingInfoUpright c)) s" and
    "alw (holds (\<lambda>c. InvGlobalInfoAtBetaUpright c)) s" and
    "alw next s"
  shows "alw SafeStickyGlobVacantUpto s"
  using assms apply (coinduction arbitrary: s)
  subgoal for s
    unfolding spec_def next_def SafeStickyGlobVacantUpto_def Let_def
    apply (rule exI[of _ s])
    apply safe
    subgoal for q t
      apply (coinduction arbitrary: s rule: alw.coinduct)
      apply clarsimp
      apply (rule conjI)
       apply blast
    proof -
      fix sb :: "('a, 'b) configuration stream"
      assume a1: "alw (holds InvGlobVacantUptoImpliesNrec) sb"
      assume a2: "alw (holds InvGlobalRecordCount) sb"
      assume a3: "alw (holds InvGlobalIncomingInfoUpright) sb"
      assume a4: "alw (holds InvGlobalInfoAtBetaUpright) sb"
      assume a5: "alw (\<lambda>s. next_performop s \<or> next_sendupd s \<or> next_recvupd s \<or> shd (stl s) = shd s) sb"
      assume a6: "GlobVacantUpto (shd sb) q t"
      have "next_performop sb \<or> next_sendupd sb \<or> next_recvupd sb \<or> shd (stl sb) = shd sb"
        using a5 by blast
      then have "GlobVacantUpto (shd (stl sb)) q t"
        using a6 a4 a3 a2 a1 by (metis (no_types) alwD gvut1 gvut2 gvut3 holds.elims(2))
      then show "alw (holds InvGlobalRecordCount) (stl sb) \<and> alw (holds InvGlobalIncomingInfoUpright) (stl sb) \<and> alw (holds InvGlobalInfoAtBetaUpright) (stl sb) \<and> alw (\<lambda>s. next_performop s \<or> next_sendupd s \<or> next_recvupd s \<or> shd (stl s) = shd s) (stl sb) \<and> GlobVacantUpto (shd (stl sb)) q t"
        using a5 a4 a3 a2 by blast
    qed
    apply blast
    done
  done

lemma spec_imp_SafeStickyGlobVacantUpto: "spec s \<Longrightarrow> alw SafeStickyGlobVacantUpto s"
  apply (rule spec_imp_SafeStickyGlobVacantUpto_aux)
      apply (simp add: spec_imp_inv1)
     apply (simp add: alw_InvGlobalRecordCount)
    apply (simp add: alw_InvGlobalIncomingInfoUpright)
   apply (simp add: alw_InvGlobalInfoAtBetaUpright)
  apply (simp add: spec_def)
  done

definition SafeGlobMono where
  "SafeGlobMono c0 c1 = (\<forall>p t. GlobVacantUpto c0 p t \<longrightarrow> GlobVacantUpto c1 p t)"

lemma alw_SafeGlobMono: "spec s \<Longrightarrow> alw (relates SafeGlobMono) s"
  apply (drule spec_imp_SafeStickyGlobVacantUpto)
  apply (erule alw_mono)
  apply (fastforce simp: SafeStickyGlobVacantUpto_def SafeGlobMono_def relates_def)
  done

(*<*)
end
(*>*)
