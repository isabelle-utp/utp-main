theory Erdos_Milner
  imports Partitions

begin

subsection \<open>Erdős-Milner theorem\<close>

text \<open>P. Erdős and E. C. Milner, A Theorem in the Partition Calculus.
Canadian Math. Bull. 15:4 (1972), 501-505.
Corrigendum, Canadian Math. Bull. 17:2 (1974), 305.\<close>

text \<open>The paper defines strong types as satisfying the criteria below.
      It remarks that ordinals satisfy those criteria. Here is a (too complicated) proof.\<close>
proposition strong_ordertype_eq:
  assumes D: "D \<subseteq> elts \<beta>" and "Ord \<beta>"
  obtains L where "\<Union>(List.set L) = D" "\<And>X. X \<in> List.set L \<Longrightarrow> indecomposable (tp X)"
    and "\<And>M. \<lbrakk>M \<subseteq> D; \<And>X. X \<in> List.set L \<Longrightarrow> tp (M \<inter> X) \<ge> tp X\<rbrakk> \<Longrightarrow> tp M = tp D"
proof -
  define \<phi> where "\<phi> \<equiv> inv_into D (ordermap D VWF)"
  then have bij_\<phi>: "bij_betw \<phi> (elts (tp D)) D"
    using D bij_betw_inv_into down ordermap_bij by blast
  have \<phi>_cancel_left: "\<And>d. d \<in> D \<Longrightarrow> \<phi> (ordermap D VWF d) = d"
    by (metis D \<phi>_def bij_betw_inv_into_left down_raw ordermap_bij small_iff_range total_on_VWF wf_VWF)
  have \<phi>_cancel_right: "\<And>\<gamma>. \<gamma> \<in> elts (tp D) \<Longrightarrow> ordermap D VWF (\<phi> \<gamma>) = \<gamma>"
    by (metis \<phi>_def f_inv_into_f ordermap_surj subsetD)
  have "small D" "D \<subseteq> ON"
    using assms down elts_subset_ON [of \<beta>] by auto
  then have \<phi>_less_iff: "\<And>\<gamma> \<delta>. \<lbrakk>\<gamma> \<in> elts (tp D); \<delta> \<in> elts (tp D)\<rbrakk> \<Longrightarrow> \<phi> \<gamma> < \<phi> \<delta> \<longleftrightarrow> \<gamma> < \<delta>"
    using ordermap_mono_less [of _ _ VWF D] bij_betw_apply [OF bij_\<phi>] VWF_iff_Ord_less \<phi>_cancel_right trans_VWF wf_VWF
    by (metis ON_imp_Ord Ord_linear2 less_V_def order.asym)
  obtain \<alpha>s where "List.set \<alpha>s \<subseteq> ON" and "\<omega>_dec \<alpha>s" and tpD_eq: "tp D = \<omega>_sum \<alpha>s"
    using Ord_ordertype \<omega>_nf_exists by blast                \<comment> \<open>Cantor normal form of the ordertype\<close>
  have ord [simp]: "Ord (\<alpha>s ! k)" "Ord (\<omega>_sum (take k \<alpha>s))" if "k < length \<alpha>s" for k
    using that \<open>list.set \<alpha>s \<subseteq> ON\<close>
    by (auto simp: dual_order.trans set_take_subset elim: ON_imp_Ord)
  define E where "E \<equiv> \<lambda>k. lift (\<omega>_sum (take k \<alpha>s)) (\<omega>\<up>(\<alpha>s!k))"
  define L where "L \<equiv> map (\<lambda>k. \<phi> ` (elts (E k))) [0..<length \<alpha>s]"
  have [simp]: "length L = length \<alpha>s"
    by (simp add: L_def)
  have in_elts_E_less: "x' < x"
    if "x' \<in> elts (E k')" "x \<in> elts (E k)" "k'<k" "k < length \<alpha>s" for k k' x' x
                                      \<comment> \<open>The ordinals have been partitioned into disjoint intervals\<close>
  proof -
    have ord\<omega>: "Ord (\<omega> \<up> \<alpha>s ! k')"
      using that by auto
    from that id_take_nth_drop [of k' "take k \<alpha>s"]
    obtain l where "take k \<alpha>s = take k' \<alpha>s @ (\<alpha>s!k') # l"
      by (simp add: min_def)
    then show ?thesis
      using that  by (auto simp: E_def lift_def add.assoc dest!: OrdmemD [OF ord\<omega>] intro: less_le_trans)
  qed
  have elts_E: "elts (E k) \<subseteq> elts (\<omega>_sum \<alpha>s)"
    if "k < length \<alpha>s" for k
  proof -
    have "\<omega> \<up> (\<alpha>s!k) \<le> \<omega>_sum (drop k \<alpha>s)"
      by (metis that Cons_nth_drop_Suc \<omega>_sum_Cons add_le_cancel_left0)
    then have "(+) (\<omega>_sum (take k \<alpha>s)) ` elts (\<omega> \<up> (\<alpha>s!k)) \<subseteq> elts (\<omega>_sum (take k \<alpha>s) + \<omega>_sum (drop k \<alpha>s))"
      by blast
    also have "\<dots> = elts (\<omega>_sum \<alpha>s)"
      using \<omega>_sum_take_drop by auto
    finally show ?thesis
      by (simp add: lift_def E_def)
  qed
  have \<omega>_sum_in_tpD: "\<omega>_sum (take k \<alpha>s) + \<gamma> \<in> elts (tp D)"
    if "\<gamma> \<in> elts (\<omega> \<up> \<alpha>s!k)" "k < length \<alpha>s" for \<gamma> k
    using elts_E lift_def that tpD_eq by (auto simp: E_def)
  have Ord_\<phi>: "Ord (\<phi> (\<omega>_sum (take k \<alpha>s) + \<gamma>))"
    if "\<gamma> \<in> elts (\<omega> \<up> \<alpha>s!k)" "k < length \<alpha>s" for \<gamma> k
    using \<omega>_sum_in_tpD \<open>D \<subseteq> ON\<close> bij_\<phi> bij_betw_imp_surj_on that by fastforce
  define \<pi> where "\<pi> \<equiv> \<lambda>k. ((\<lambda>y. odiff y (\<omega>_sum (take k \<alpha>s))) \<circ> ordermap D VWF)"
      \<comment> \<open>mapping the segments of @{term D} into some power of @{term \<omega>}\<close>
  have bij_\<pi>: "bij_betw (\<pi> k) (\<phi> ` elts (E k)) (elts (\<omega> \<up> (\<alpha>s!k)))"
    if "k < length \<alpha>s" for k
    using that by (auto simp: bij_betw_def \<pi>_def E_def inj_on_def lift_def image_comp \<omega>_sum_in_tpD \<phi>_cancel_right that)
  have \<pi>_iff: "\<pi> k x < \<pi> k y \<longleftrightarrow> (x,y) \<in> VWF"
    if "x \<in> \<phi> ` elts (E k)" "y \<in> \<phi> ` elts (E k)" "k < length \<alpha>s" for k x y
    using that
    by (auto simp: \<pi>_def E_def lift_def \<omega>_sum_in_tpD \<phi>_cancel_right Ord_\<phi> \<phi>_less_iff)
  have tp_E_eq [simp]: "tp (\<phi> ` elts (E k)) = \<omega>\<up>(\<alpha>s!k)"
    if k: "k < length \<alpha>s" for k
    using ordertype_eq_iff \<pi>_iff bij_\<pi> that
    by (meson Ord_\<omega> Ord_oexp ord(1) ordertype_VWF_eq_iff replacement small_elts)
  have tp_L_eq [simp]: "tp (L!k) = \<omega>\<up>(\<alpha>s!k)"
    if "k < length \<alpha>s" for k
    by (simp add: L_def that)
  have UL_eq_D: "\<Union> (list.set L) = D"
  proof (rule antisym)
    show "\<Union> (list.set L) \<subseteq> D"
      by (force simp: L_def tpD_eq bij_betw_apply [OF bij_\<phi>] dest: elts_E)
    show "D \<subseteq> \<Union> (list.set L)"
    proof
      fix \<delta>
      assume "\<delta> \<in> D"
      then have "ordermap D VWF \<delta> \<in> elts (\<omega>_sum \<alpha>s)"
        by (metis \<open>small D\<close> ordermap_in_ordertype tpD_eq)
      then show "\<delta> \<in> \<Union> (list.set L)"
        using \<open>\<delta> \<in> D\<close> \<phi>_cancel_left in_elts_\<omega>_sum
        by (fastforce simp: L_def E_def image_iff lift_def)
    qed
  qed
  show thesis
  proof
    show "indecomposable (tp X)" if "X \<in> list.set L" for X
      using that by (auto simp: L_def indecomposable_\<omega>_power)
  next
    fix M
    assume "M \<subseteq> D" and *: "\<And>X. X \<in> list.set L \<Longrightarrow> tp X \<le> tp (M \<inter> X)"
    show "tp M = tp D"
    proof (rule antisym)
      show "tp M \<le> tp D"
        by (simp add: \<open>M \<subseteq> D\<close> \<open>small D\<close> ordertype_VWF_mono)
      define \<sigma> where "\<sigma> \<equiv> \<lambda>X. inv_into (M \<inter> X) (ordermap (M \<inter> X) VWF)"
                              \<comment> \<open>The bijection from an @{term \<omega>}-power into the appropriate segment of @{term M}\<close>
      have bij_\<sigma>: "bij_betw (\<sigma> X) (elts (tp (M \<inter> X))) (M \<inter> X)" for X
        unfolding \<sigma>_def
        by (metis (no_types) \<open>M \<subseteq> D\<close> \<open>small D\<close> bij_betw_inv_into inf_le1 ordermap_bij subset_iff_less_eq_V total_on_VWF wf_VWF)
      have Ord_\<sigma>: "Ord (\<sigma> X \<alpha>)" if "\<alpha> \<in> elts (tp (M \<inter> X))" for \<alpha> X
        using \<open>D \<subseteq> ON\<close> \<open>M \<subseteq> D\<close> bij_betw_apply [OF bij_\<sigma>] that by blast
      have \<sigma>_cancel_right: "\<And>\<gamma> X. \<gamma> \<in> elts (tp (M \<inter> X)) \<Longrightarrow> ordermap (M \<inter> X) VWF (\<sigma> X \<gamma>) = \<gamma>"
        by (metis \<sigma>_def f_inv_into_f ordermap_surj subsetD)
      have smM: "small (M \<inter> X)" for X
        by (meson \<open>M \<subseteq> D\<close> \<open>small D\<close> inf_le1 subset_iff_less_eq_V)
      then have \<sigma>_less: "\<And>X \<gamma> \<delta>. \<lbrakk>\<gamma> < \<delta>; \<gamma> \<in> elts (tp (M \<inter> X)); \<delta> \<in> elts (tp (M \<inter> X))\<rbrakk>
                          \<Longrightarrow> \<sigma> X \<gamma> < \<sigma> X \<delta>"
        using ordermap_mono_less bij_betw_apply [OF bij_\<sigma>] VWF_iff_Ord_less \<sigma>_cancel_right trans_VWF wf_VWF
        by (metis Ord_\<sigma> Ord_linear_lt less_imp_not_less ordermap_mono_less)
      have "\<exists>k < length \<alpha>s. \<gamma> \<in> elts (E k)" if \<gamma>: "\<gamma> \<in> elts (tp D)" for \<gamma>
      proof -
        obtain X where "X \<in> set L" and X: "\<phi> \<gamma> \<in> X"
          by (metis UL_eq_D \<gamma> Union_iff \<phi>_def in_mono inv_into_into ordermap_surj)
        then have "\<exists>k < length \<alpha>s. \<gamma> \<in> elts (E k) \<and> X = \<phi> ` elts (E k)"
          apply (clarsimp simp: L_def)
          by (metis \<gamma> \<phi>_cancel_right elts_E in_mono tpD_eq)
        then show ?thesis
          by blast
      qed
      then obtain K where K: "\<And>\<gamma>. \<gamma> \<in> elts (tp D) \<Longrightarrow> K \<gamma> < length \<alpha>s \<and> \<gamma> \<in> elts (E (K \<gamma>))"
        by metis  \<comment> \<open>The index from @{term "tp D"} to the appropriate segment number\<close>
      define \<psi> where "\<psi> \<equiv> \<lambda>d. \<sigma> (L ! K (ordermap D VWF d)) (\<pi> (K (ordermap D VWF d)) d)"
      show "tp D \<le> tp M"
      proof (rule ordertype_inc_le)
        show "small D" "small M"
          using \<open>M \<subseteq> D\<close> \<open>small D\<close> subset_iff_less_eq_V by auto
      next
        fix d' d
        assume xy: "d' \<in> D" "d \<in> D" and "(d',d) \<in> VWF"
        then have "d' < d"
          using ON_imp_Ord \<open>D \<subseteq> ON\<close> by auto
        define \<gamma>' where "\<gamma>' \<equiv> ordermap D VWF d'"
        define \<gamma> where "\<gamma> \<equiv> ordermap D VWF d"
        have len': "K \<gamma>' < length \<alpha>s" and elts': "\<gamma>' \<in> elts (E (K \<gamma>'))"
            and len: "K \<gamma> < length \<alpha>s" and elts: "\<gamma> \<in> elts (E (K \<gamma>))"
          using K \<open>d' \<in> D\<close> \<open>d \<in> D\<close> by (auto simp: \<gamma>'_def \<gamma>_def \<open>small D\<close> ordermap_in_ordertype)
        have **: "\<And>X w. \<lbrakk>X \<in> list.set L; w \<in> elts (tp X)\<rbrakk> \<Longrightarrow> w \<in> elts (tp (M \<inter> X))"
          using "*" by blast
        have Ord_\<sigma>L: "Ord (\<sigma> (L!k) (\<pi> k d))" if "d \<in> \<phi> ` elts (E k)" "k < length \<alpha>s" for k d
          by (metis "**" Ord_\<sigma> \<open>length L = length \<alpha>s\<close> bij_\<pi> bij_betw_imp_surj_on imageI nth_mem that tp_L_eq)
        have "\<gamma>' < \<gamma>"
          by (metis \<gamma>'_def \<gamma>_def \<open>d' < d\<close> \<open>small D\<close> \<phi>_cancel_left \<phi>_less_iff ordermap_in_ordertype xy)
        then have "K \<gamma>' \<le> K \<gamma>"
          using elts' elts by (meson in_elts_E_less leI len' less_asym)
        then consider (less) "K \<gamma>' < K \<gamma>" | (equal) "K \<gamma>' = K \<gamma>"
          by linarith
        then have "\<sigma> (L ! K \<gamma>') (\<pi> (K \<gamma>') d') < \<sigma> (L ! K \<gamma>) (\<pi> (K \<gamma>) d)"
        proof cases
          case less
          obtain \<dagger>: "\<sigma> (L ! K \<gamma>') (\<pi> (K \<gamma>') d') \<in> M \<inter> L ! K \<gamma>'" "\<sigma> (L ! K \<gamma>) (\<pi> (K \<gamma>) d) \<in> M \<inter> L ! K \<gamma>"
            using elts' elts len' len
            unfolding \<gamma>'_def \<gamma>_def
            by (metis "**" \<open>length L = length \<alpha>s\<close> \<phi>_cancel_left bij_\<pi> bij_\<sigma> bij_betw_imp_surj_on imageI nth_mem tp_L_eq xy)
          then have "ordermap D VWF (\<sigma> (L ! K \<gamma>') (\<pi> (K \<gamma>') d')) \<in> elts (E (K \<gamma>'))" "ordermap D VWF (\<sigma> (L ! K \<gamma>) (\<pi> (K \<gamma>) d)) \<in> elts (E (K \<gamma>))"
            using len' len elts_E tpD_eq
            by (fastforce simp: L_def \<gamma>'_def \<gamma>_def \<phi>_cancel_right)+
          then have "ordermap D VWF (\<sigma> (L ! K \<gamma>') (\<pi> (K \<gamma>') d')) < ordermap D VWF (\<sigma> (L ! K \<gamma>) (\<pi> (K \<gamma>) d))"
            using in_elts_E_less len less by blast
          moreover have "\<sigma> (L ! K \<gamma>') (\<pi> (K \<gamma>') d') \<in> D" "\<sigma> (L ! K \<gamma>) (\<pi> (K \<gamma>) d) \<in> D"
            using \<open>M \<subseteq> D\<close> \<dagger> by auto
          ultimately show ?thesis
            by (metis \<open>small D\<close> \<phi>_cancel_left \<phi>_less_iff ordermap_in_ordertype)
        next
          case equal
          show ?thesis
            unfolding equal
          proof (rule \<sigma>_less)
            show "\<pi> (K \<gamma>) d' < \<pi> (K \<gamma>) d"
              by (metis equal \<gamma>'_def \<gamma>_def \<open>(d', d) \<in> VWF\<close> \<phi>_cancel_left \<pi>_iff elts elts' imageI len xy)
            have "\<pi> (K \<gamma>) d' \<in> elts (tp (L ! K \<gamma>))" "\<pi> (K \<gamma>) d \<in> elts (tp (L ! K \<gamma>))"
              using equal \<phi>_cancel_left \<gamma>'_def elts' len' \<gamma>_def elts len xy
              by (force intro: bij_betw_apply [OF bij_\<pi>])+
            then show "\<pi> (K \<gamma>) d' \<in> elts (tp (M \<inter> L ! K \<gamma>))" "\<pi> (K \<gamma>) d \<in> elts (tp (M \<inter> L ! K \<gamma>))"
              by (simp_all add: "**" len)
          qed
        qed
        moreover have "Ord (\<sigma> (L ! K \<gamma>') (\<pi> (K \<gamma>') d'))"
          using Ord_\<sigma>L \<gamma>'_def \<phi>_cancel_left elts' len' xy(1) by fastforce
        moreover have "Ord (\<sigma> (L ! K \<gamma>) (\<pi> (K \<gamma>) d))"
          using Ord_\<sigma>L \<gamma>_def \<phi>_cancel_left elts len xy by fastforce
        ultimately show "(\<psi> d', \<psi> d) \<in> VWF"
          by (simp add: \<psi>_def \<gamma>'_def \<gamma>_def)
      next
        show "\<psi> ` D \<subseteq> M"
        proof (clarsimp simp: \<psi>_def)
          fix d
          assume "d \<in> D"
          define \<gamma> where "\<gamma> \<equiv> ordermap D VWF d"
          have len: "K \<gamma> < length \<alpha>s" and elts: "\<gamma> \<in> elts (E (K \<gamma>))"
            using K \<open>d \<in> D\<close> by (auto simp: \<gamma>_def \<open>small D\<close> ordermap_in_ordertype)
          have "\<pi> (K \<gamma>) d \<in> elts (tp (L! (K \<gamma>)))"
            using bij_\<pi> [OF len] \<open>d \<in> D\<close>
            apply (simp add: L_def len)
            by (metis \<gamma>_def \<phi>_cancel_left bij_betw_imp_surj_on elts imageI)
          then have "\<sigma> (L! (K \<gamma>)) (\<pi> (K \<gamma>) d) \<in> M \<inter> (L! (K \<gamma>))"
            using smM bij_betw_imp_surj_on [OF ordermap_bij] \<open>length L = length \<alpha>s\<close>
            unfolding \<sigma>_def
            by (metis (no_types) "*" inv_into_into len nth_mem vsubsetD total_on_VWF wf_VWF)
          then show "\<sigma> (L ! K (ordermap D VWF d)) (\<pi> (K (ordermap D VWF d)) d) \<in> M"
            using \<gamma>_def by blast
        qed
      qed auto
    qed
  qed (simp add: UL_eq_D)
qed


text \<open>The ``remark'' of Erdős and E. C. Milner, Canad. Math. Bull. Vol. 17 (2), 1974\<close>

proposition indecomposable_imp_Ex_less_sets:
  assumes indec: "indecomposable \<alpha>" and "\<alpha> > 1" and A: "tp A = \<alpha>" "small A" "A \<subseteq> ON"
    and "x \<in> A" and A1: "tp A1 = \<alpha>" "A1 \<subseteq> A"
  obtains A2 where "tp A2 = \<alpha>" "A2 \<subseteq> A1" "less_sets {x} A2"
proof -
  have "Ord \<alpha>"
    using indec indecomposable_imp_Ord by blast
  have "Limit \<alpha>"
    by (simp add: assms indecomposable_imp_Limit)
  define \<phi> where "\<phi> \<equiv> inv_into A (ordermap A VWF)"
  then have bij_\<phi>: "bij_betw \<phi> (elts \<alpha>) A"
    using A bij_betw_inv_into down ordermap_bij by blast
  have bij_om: "bij_betw (ordermap A VWF) A (elts \<alpha>)"
    using A down ordermap_bij by blast
  define \<gamma> where "\<gamma> \<equiv> ordermap A VWF x"
  have \<gamma>: "\<gamma> \<in> elts \<alpha>"
    unfolding \<gamma>_def using A \<open>x \<in> A\<close> down by auto
  then have "Ord \<gamma>"
    using Ord_in_Ord \<open>Ord \<alpha>\<close> by blast
  define B where "B \<equiv> \<phi> ` (elts (succ \<gamma>))"
  show thesis
  proof
    have "small A1"
      by (meson \<open>small A\<close> A1 smaller_than_small)
    then have "tp (A1 - B) \<le> tp A1"
      unfolding B_def by (auto intro!: ordertype_VWF_mono del: vsubsetI)
    moreover have "tp (A1 - B) \<ge> \<alpha>"
    proof -
      have "\<not> (\<alpha> \<le> tp B)"
        unfolding B_def
      proof (subst ordertype_VWF_inc_eq)
        show "elts (succ  \<gamma>) \<subseteq> ON"
          by (auto simp: \<gamma>_def ordertype_VWF_inc_eq intro: Ord_in_Ord)
        have sub: "elts (succ  \<gamma>) \<subseteq> elts \<alpha>"
          using Ord_trans \<gamma> \<open>Ord \<alpha>\<close> by auto
        then show "\<phi> ` elts (succ  \<gamma>) \<subseteq> ON"
          using \<open>A \<subseteq> ON\<close> bij_\<phi> bij_betw_imp_surj_on by blast
        have "succ \<gamma> \<in> elts \<alpha>"
          using \<gamma> Limit_def \<open>Limit \<alpha>\<close> by blast
        with A sub show "\<phi> u < \<phi> v"
          if "u \<in> elts (succ  \<gamma>)" and "v \<in> elts (succ  \<gamma>)" and "u < v" for u v
          by (metis ON_imp_Ord Ord_not_le \<open>A \<subseteq> ON\<close> \<open>small A\<close> \<phi>_def bij_\<phi> bij_betw_apply inv_ordermap_VWF_mono_le leD subsetD that)
        show "\<not> \<alpha> \<le> tp (elts (succ  \<gamma>))"
          by (metis Limit_def Ord_succ \<gamma> \<open>Limit \<alpha>\<close> \<open>Ord \<gamma>\<close> mem_not_refl ordertype_eq_Ord vsubsetD)
      qed auto
      then show ?thesis
        using indecomposable_ordertype_ge [OF indec, of A1 B] \<open>small A1\<close> A1
        by (auto simp: B_def)
    qed
    ultimately show "tp (A1 - B) = \<alpha>"
      using A1 by blast
    show "less_sets {x} (A1 - B)"
    proof (clarsimp simp: less_sets_def B_def simp del: elts_succ)
      fix y
      assume "y \<in> A1" and y: "y \<notin> \<phi> ` elts (succ \<gamma>)"
      obtain "Ord x" "Ord y"
        using \<open>A \<subseteq> ON\<close> \<open>x \<in> A\<close> \<open>y \<in> A1\<close> A1 by auto
      have "y \<in> \<phi> ` elts (succ \<gamma>)" if "y \<in> elts (succ x)"
      proof -
        have "ordermap A VWF y \<in> elts (ZFC_in_HOL.succ (ordermap A VWF x))"
          using A1
          by (metis insert_iff ordermap_mono subset_iff that wf_VWF OrdmemD VWF_iff_Ord_less \<open>Ord x\<close> \<open>Ord y\<close> \<open>small A\<close> \<open>y \<in> A1\<close> elts_succ)
        then show ?thesis
          using that A1 unfolding \<gamma>_def
          by (metis \<open>y \<in> A1\<close> \<phi>_def bij_betw_inv_into_left bij_om imageI subsetD)
      qed
      then show "x < y"
        by (meson Ord_linear2 Ord_mem_iff_lt Ord_succ \<open>Ord x\<close> \<open>Ord y\<close> y succ_le_iff)
    qed
  qed auto
qed


text \<open>the main theorem, from which they derive the headline result\<close>
theorem Erdos_Milner_aux:
  assumes part: "partn_lst_VWF \<alpha> [ord_of_nat k, \<gamma>] 2"
    and indec: "indecomposable \<alpha>" and "k > 1" "Ord \<gamma>" and \<beta>: "\<beta> \<in> elts \<omega>1"
  shows "partn_lst_VWF (\<alpha>*\<beta>) [ord_of_nat (2*k), min \<gamma> (\<omega>*\<beta>)] 2"
proof (cases "\<alpha>=1 \<or> \<beta>=0")
  case True
  show ?thesis
  proof (cases "\<beta>=0")
    case True
    moreover have "min \<gamma> 0 = 0"
      by (simp add: min_def)
    ultimately show ?thesis
      by (simp add: partn_lst_triv0 [where i=1])
  next
    case False
    then obtain "\<alpha>=1" "Ord \<beta>"
      by (meson ON_imp_Ord Ord_\<omega>1 True \<beta> elts_subset_ON)
    then obtain i where "i < Suc (Suc 0)" "[ord_of_nat k, \<gamma>] ! i \<le> \<alpha>"
      using partn_lst_VWF_nontriv [OF part] by auto
    then have "\<gamma> \<le> 1"
      using \<open>\<alpha>=1\<close> \<open>k > 1\<close> by (fastforce simp: less_Suc_eq)
    then have "min \<gamma> (\<omega>*\<beta>) \<le> 1"
      by (metis Ord_1 Ord_\<omega> Ord_linear_le Ord_mult \<open>Ord \<beta>\<close> min_def order_trans)
    moreover have "elts \<beta> \<noteq> {}"
      using False by auto
    ultimately show ?thesis
      by (auto simp: True \<open>Ord \<beta>\<close> \<open>\<beta>\<noteq>0\<close> \<open>\<alpha>=1\<close> intro!: partn_lst_triv1 [where i=1])
  qed
next
  case False
  then have "\<alpha> \<noteq> 1" "\<beta> \<noteq> 0"
    by auto
  then have "0 \<in> elts \<beta>"
    using Ord_\<omega>1 Ord_in_Ord \<beta> mem_0_Ord by blast
  show ?thesis
  proof (cases "\<alpha>=0")
    case True
    have \<dagger>: "[ord_of_nat (2 * k), 0] ! 1 = 0"
      by simp
    show ?thesis
      using True assms
      by (force simp: partn_lst_def nsets_empty_iff simp flip: numeral_2_eq_2 dest!: less_2_cases intro: \<dagger>)
  next
    case False
    then have "\<alpha> \<ge> \<omega>"
      using indec \<open>\<alpha> \<noteq> 1\<close>
      by (metis Ord_\<omega> indecomposable_is_\<omega>_power le_oexp oexp_0_right)
    then have "\<alpha> > 1"
      using \<omega>_gt1 dual_order.strict_trans1 by blast
    show ?thesis
      unfolding partn_lst_def
    proof clarsimp
      fix f
      assume "f \<in> [elts (\<alpha>*\<beta>)]\<^bsup>2\<^esup> \<rightarrow> {..<Suc (Suc 0)}"
      then have f: "f \<in> [elts (\<alpha>*\<beta>)]\<^bsup>2\<^esup> \<rightarrow> {..<2::nat}"
        by (simp add: eval_nat_numeral)
      obtain ord [iff]: "Ord \<alpha>" "Ord \<beta>" "Ord (\<alpha>*\<beta>)"
        using Ord_\<omega>1 Ord_in_Ord \<beta> indec indecomposable_imp_Ord Ord_mult by blast
      have *: False
          if i [rule_format]: "\<forall>H. tp H = ord_of_nat (2*k) \<longrightarrow> H \<subseteq> elts (\<alpha>*\<beta>) \<longrightarrow> \<not> f ` [H]\<^bsup>2\<^esup> \<subseteq> {0}"
          and ii [rule_format]: "\<forall>H. tp H = \<gamma> \<longrightarrow> H \<subseteq> elts (\<alpha>*\<beta>) \<longrightarrow> \<not> f ` [H]\<^bsup>2\<^esup> \<subseteq> {1}"
          and iii [rule_format]: "\<forall>H. tp H = (\<omega>*\<beta>) \<longrightarrow> H \<subseteq> elts (\<alpha>*\<beta>) \<longrightarrow> \<not> f ` [H]\<^bsup>2\<^esup> \<subseteq> {1}"
      proof -
        have Ak0: "\<exists>X \<in> [A]\<^bsup>k\<^esup>. f ` [X]\<^bsup>2\<^esup> \<subseteq> {0}" \<comment>\<open>remark (8) about @{term"A \<subseteq> S"}\<close>
          if A_\<alpha>\<beta>: "A \<subseteq> elts (\<alpha>*\<beta>)" and ot: "tp A \<ge> \<alpha>" for A
        proof -
          let ?g = "inv_into A (ordermap A VWF)"
          have "small A"
            using down that by auto
          then have inj_g: "inj_on ?g (elts \<alpha>)"
            by (meson inj_on_inv_into less_eq_V_def ordermap_surj ot subset_trans)
          have Aless: "\<And>x y. \<lbrakk>x \<in> A; y \<in> A; x < y\<rbrakk> \<Longrightarrow> (x,y) \<in> VWF"
            by (meson Ord_in_Ord VWF_iff_Ord_less \<open>Ord(\<alpha>*\<beta>)\<close> subsetD that(1))
          then have om_A_less: "\<And>x y. \<lbrakk>x \<in> A; y \<in> A; x < y\<rbrakk> \<Longrightarrow> ordermap A VWF x < ordermap A VWF y"
            by (auto simp: \<open>small A\<close> ordermap_mono_less)
          have \<alpha>_sub: "elts \<alpha> \<subseteq> ordermap A VWF ` A"
            by (metis \<open>small A\<close> elts_of_set less_eq_V_def ordertype_def ot replacement)
          have g: "?g \<in> elts \<alpha> \<rightarrow> elts (\<alpha> * \<beta>)"
            by (meson A_\<alpha>\<beta> Pi_I' \<alpha>_sub inv_into_into subset_eq)
          then have fg: "f \<circ> (\<lambda>X. ?g ` X) \<in> [elts \<alpha>]\<^bsup>2\<^esup> \<rightarrow> {..<2}"
            by (rule nsets_compose_image_funcset [OF f _ inj_g])
          have g_less: "?g x < ?g y" if "x < y" "x \<in> elts \<alpha>" "y \<in> elts \<alpha>" for x y
            using Pi_mem [OF g]
            by (meson A_\<alpha>\<beta> Ord_in_Ord Ord_not_le ord \<open>small A\<close> dual_order.trans elts_subset_ON inv_ordermap_VWF_mono_le ot that vsubsetD)
          obtain i H where "i < 2" "H \<subseteq> elts \<alpha>"
            and ot_eq: "tp H = [k,\<gamma>]!i" "(f \<circ> (\<lambda>X. ?g ` X)) ` (nsets H 2) \<subseteq> {i}"
            using ii partn_lst_E [OF part fg] by (auto simp: eval_nat_numeral)
          then consider (0) "i=0" | (1) "i=1"
            by linarith
          then show ?thesis
          proof cases
            case 0
            then have "f ` [inv_into A (ordermap A VWF) ` H]\<^bsup>2\<^esup> \<subseteq> {0}"
              using ot_eq \<open>H \<subseteq> elts \<alpha>\<close> \<alpha>_sub by (auto simp: nsets_def [of _ k] inj_on_inv_into elim!: nset_image_obtains)
            moreover have "finite H \<and> card H = k"
              using 0 ot_eq \<open>H \<subseteq> elts \<alpha>\<close> down by (simp add: finite_ordertype_eq_card)
            then have "inv_into A (ordermap A VWF) ` H \<in> [A]\<^bsup>k\<^esup>"
              using \<open>H \<subseteq> elts \<alpha>\<close> \<alpha>_sub by (auto simp: nsets_def [of _ k] card_image inj_on_inv_into inv_into_into)
            ultimately show ?thesis
              by blast
          next
            case 1
            have gH: "?g ` H \<subseteq> elts (\<alpha> * \<beta>)"
              by (metis A_\<alpha>\<beta> \<alpha>_sub \<open>H \<subseteq> elts \<alpha>\<close> image_subsetI inv_into_into subset_eq)
            have [simp]: "tp (?g ` H) = tp H"
              by (meson \<open>H \<subseteq> elts \<alpha>\<close> ord down dual_order.trans elts_subset_ON gH g_less ordertype_VWF_inc_eq subsetD)
            show ?thesis
              using ii [of "?g ` H"] ot_eq 1
              apply (auto simp: gH elim!: nset_image_obtains)
              apply (meson \<open>H \<subseteq> elts \<alpha>\<close> inj_g bij_betw_def inj_on_subset)
              done
          qed
        qed
        define K where "K \<equiv> \<lambda>i x. {y \<in> elts (\<alpha>*\<beta>). x \<noteq> y \<and> f{x,y} = i}"
        have small_K: "small (K i x)" for i x
          by (simp add: K_def)
        define KI where "KI \<equiv> \<lambda>i X. (\<Inter>x\<in>X. K i x)"
        have KI_disj_self: "X \<inter> KI i X = {}" for i X
          by (auto simp: KI_def K_def)
        define M where "M \<equiv> \<lambda>D \<AA> x. {\<nu>::V. \<nu> \<in> D \<and> tp (K 1 x \<inter> \<AA> \<nu>) \<ge> \<alpha>}"
        have M_sub_D: "M D \<AA> x \<subseteq> D" for D \<AA> x
          by (auto simp: M_def)
        have small_M [simp]: "small (M D \<AA> x)" if "small D" for D \<AA> x
          by (simp add: M_def that)
        have 9: "tp {x \<in> A. tp (M D \<AA> x) \<ge> tp D} \<ge> \<alpha>" (is "ordertype ?AD _ \<ge> \<alpha>")
          if inD: "indecomposable (tp D)" and D: "D \<subseteq> elts \<beta>" and A: "A \<subseteq> elts (\<alpha>*\<beta>)" and tpA: "tp A = \<alpha>"
            and \<AA>: "\<AA> \<in> D \<rightarrow> {X. X \<subseteq> elts (\<alpha>*\<beta>) \<and> tp X = \<alpha>}"  for D A \<AA>
            \<comment>\<open>remark (9), assuming an indecomposable order type\<close>
        proof (rule ccontr)
          define A' where "A' \<equiv> {x \<in> A. \<not> tp (M D \<AA> x) \<ge> tp D}"
          have small [iff]: "small A" "small D"
            using A D down by (auto simp: M_def)
          have small_\<AA>: "small (\<AA> \<delta>)" if "\<delta> \<in> D" for \<delta>
            using that \<AA> by (auto simp: Pi_iff subset_iff_less_eq_V)
          assume not_\<alpha>_le: "\<not> \<alpha> \<le> tp {x \<in> A. tp (M D \<AA> x) \<ge> tp D}"
          moreover
          obtain "small A" "small A'" "A' \<subseteq> A" and A'_sub: "A' \<subseteq> elts (\<alpha> * \<beta>)"
            using A'_def A down by auto
          moreover have "A' = A - ?AD"
            by (force simp: A'_def)
          ultimately have A'_ge: "tp A' \<ge> \<alpha>"
            by (metis (no_types, lifting) dual_order.refl indec indecomposable_ordertype_eq mem_Collect_eq subsetI tpA)
          obtain X where "X \<subseteq> A'" "finite X" "card X = k" and fX0: "f ` [X]\<^bsup>2\<^esup> \<subseteq> {0}"
            using Ak0 [OF A'_sub A'_ge] by (auto simp: nsets_def [of _ k])
          then have \<ddagger>: "\<not> tp (M D \<AA> x) \<ge> tp D" if "x \<in> X" for x
            using that by (auto simp: A'_def)
          obtain x where "x \<in> X"
            using \<open>card X = k\<close> \<open>k>1\<close> by fastforce
          have "\<not> D \<subseteq> (\<Union> x\<in>X. M D \<AA> x)"
          proof
            assume not: "D \<subseteq> (\<Union>x\<in>X. M D \<AA> x)"
            have "\<exists>X\<in>M D \<AA> ` X. tp D \<le> tp X"
            proof (rule indecomposable_ordertype_finite_ge [OF inD])
              show "M D \<AA> ` X \<noteq> {}"
                using A'_def A'_ge not not_\<alpha>_le by auto
              show "small (\<Union> (M D \<AA> ` X))"
                using \<open>finite X\<close> by (simp add: finite_imp_small)
            qed (use \<open>finite X\<close> not in auto)
            then show False
              by (simp add: \<ddagger>)
          qed
          then obtain \<nu> where "\<nu> \<in> D" and \<nu>: "\<nu> \<notin> (\<Union> x\<in>X. M D \<AA> x)"
            by blast
          define \<A> where "\<A> \<equiv> {KI 0 X \<inter> \<AA> \<nu>, \<Union>x\<in>X. K 1 x \<inter> \<AA> \<nu>, X \<inter> \<AA> \<nu>}"
          have \<alpha>\<beta>: "X \<subseteq> elts (\<alpha>*\<beta>)" "\<AA> \<nu> \<subseteq> elts (\<alpha>*\<beta>)"
            using A'_sub \<open>X \<subseteq> A'\<close> \<AA> \<open>\<nu> \<in> D\<close> by auto
          then have "KI 0 X \<union> (\<Union>x\<in>X. K 1 x) \<union> X = elts (\<alpha>*\<beta>)"
            using \<open>x \<in> X\<close> f by (force simp: K_def KI_def Pi_iff less_2_cases_iff)
          with \<alpha>\<beta> have \<AA>\<nu>_\<A>: "finite \<A>" "\<AA> \<nu> \<subseteq> \<Union>\<A>"
            by (auto simp: \<A>_def)
          then have "\<not> tp (K 1 x \<inter> \<AA> \<nu>) \<ge> \<alpha>" if "x \<in> X" for x
            using that \<open>\<nu> \<in> D\<close> \<nu> \<open>k > 1\<close> \<open>card X = k\<close> by (fastforce simp: M_def)
          moreover have sm_K1: "small (\<Union>x\<in>X. K 1 x \<inter> \<AA> \<nu>)"
            by (meson Finite_V Int_lower2 \<open>\<nu> \<in> D\<close> \<open>finite X\<close> small_\<AA> small_UN smaller_than_small)
          ultimately have not1: "\<not> tp (\<Union>x\<in>X. K 1 x \<inter> \<AA> \<nu>) \<ge> \<alpha>"
            using \<open>finite X\<close> \<open>x \<in> X\<close> indecomposable_ordertype_finite_ge [OF indec, of "(\<lambda>x. K 1 x \<inter> \<AA> \<nu>) ` X"] by blast
          moreover have "\<not> tp (X \<inter> \<AA> \<nu>) \<ge> \<alpha>"
            using \<open>finite X\<close> \<open>\<alpha> \<ge> \<omega>\<close>
            by (meson finite_Int mem_not_refl ordertype_VWF_\<omega> vsubsetD)
          moreover have "\<alpha> \<le> tp (\<AA> \<nu>)"
            using \<AA> \<open>\<nu> \<in> D\<close> small_\<AA> by fastforce+
          moreover have "small (\<Union> \<A>)"
            using \<open>\<nu> \<in> D\<close> small_\<AA> by (fastforce simp: \<A>_def intro: smaller_than_small sm_K1)
          ultimately have K0\<AA>_ge: "tp (KI 0 X \<inter> \<AA> \<nu>) \<ge> \<alpha>"
            using indecomposable_ordertype_finite_ge [OF indec \<AA>\<nu>_\<A>] by (auto simp: \<A>_def)
          have \<AA>\<nu>: "\<AA> \<nu> \<subseteq> elts (\<alpha> * \<beta>)" "tp (\<AA> \<nu>) = \<alpha>"
            using \<open>\<nu> \<in> D\<close> \<AA> by blast+
          then obtain Y where Ysub: "Y \<subseteq> KI 0 X \<inter> \<AA> \<nu>" and "finite Y" "card Y = k" and fY0: "f ` [Y]\<^bsup>2\<^esup> \<subseteq> {0}"
            using Ak0 [OF _ K0\<AA>_ge] by (auto simp: nsets_def [of _ k])
          have \<dagger>: "X \<inter> Y = {}"
            using Ysub KI_disj_self by blast
          then have "card (X \<union> Y) = 2*k"
            by (simp add: \<open>card X = k\<close> \<open>card Y = k\<close> \<open>finite X\<close> \<open>finite Y\<close> card_Un_disjoint)
          moreover have "X \<union> Y \<subseteq> elts (\<alpha> * \<beta>)"
            using A'_sub \<open>X \<subseteq> A'\<close> \<AA>\<nu>(1) \<open>Y \<subseteq> KI 0 X \<inter> \<AA> \<nu>\<close> by auto
          moreover have "f ` [X \<union> Y]\<^bsup>2\<^esup> \<subseteq> {0}"
            using fX0 fY0 Ysub by (auto simp: \<dagger> nsets_disjoint_2 image_Un image_UN KI_def K_def)
          ultimately show False
            using i \<open>finite X\<close> \<open>finite Y\<close> ordertype_VWF_finite_nat by auto
        qed
        have IX: "tp {x \<in> A. tp (M D \<AA> x) \<ge> tp D} \<ge> \<alpha>"
          if D: "D \<subseteq> elts \<beta>" and A: "A \<subseteq> elts (\<alpha>*\<beta>)" and tpA: "tp A = \<alpha>"
            and \<AA>: "\<AA> \<in> D \<rightarrow> {X. X \<subseteq> elts (\<alpha>*\<beta>) \<and> tp X = \<alpha>}" for D A \<AA>
            \<comment>\<open>remark (9) for any order type\<close>
        proof -
          obtain L where UL: "\<Union>(List.set L) \<subseteq> D"
            and indL: "\<And>X. X \<in> List.set L \<Longrightarrow> indecomposable (tp X)"
            and eqL: "\<And>M. \<lbrakk>M \<subseteq> D; \<And>X. X \<in> List.set L \<Longrightarrow> tp (M \<inter> X) \<ge> tp X\<rbrakk> \<Longrightarrow> tp M = tp D"
            using ord by (metis strong_ordertype_eq D order_refl)
          obtain A'' where A'': "A'' \<subseteq> A" "tp A'' \<ge> \<alpha>"
            and "\<And>x X. \<lbrakk>x \<in> A''; X \<in> List.set L\<rbrakk> \<Longrightarrow> tp (M D \<AA> x \<inter> X) \<ge> tp X"
            using UL indL
          proof (induction L arbitrary: thesis)
            case (Cons X L)
            then obtain A'' where A'': "A'' \<subseteq> A" "tp A'' \<ge> \<alpha>" and "X \<subseteq> D"
              and ge_X: "\<And>x X. \<lbrakk>x \<in> A''; X \<in> List.set L\<rbrakk> \<Longrightarrow> tp (M D \<AA> x \<inter> X) \<ge> tp X" by auto
            then have tp_A'': "tp A'' = \<alpha>"
              by (metis A antisym down ordertype_VWF_mono tpA)
            have ge_\<alpha>: "tp {x \<in> A''. tp (M X \<AA> x) \<ge> tp X} \<ge> \<alpha>"
              by (rule 9) (use A A'' tp_A'' Cons.prems \<open>D \<subseteq> elts \<beta>\<close> \<open>X \<subseteq> D\<close> \<AA> in auto)
            let ?A = "{x \<in> A''. tp (M D \<AA> x \<inter> X) \<ge> tp X}"
            have M_eq: "M D \<AA> x \<inter> X = M X \<AA> x" if "x \<in> A''" for x
              using that \<open>X \<subseteq> D\<close> by (auto simp: M_def)
            show thesis
            proof (rule Cons.prems)
              show "\<alpha> \<le> tp ?A"
                using ge_\<alpha> by (simp add: M_eq cong: conj_cong)
              show "tp Y \<le> tp (M D \<AA> x \<inter> Y)" if "x \<in> ?A" "Y \<in> list.set (X # L)" for x Y
                using that ge_X by force
            qed (use A'' in auto)
          qed (use tpA in auto)
          then have tp_M_ge: "tp (M D \<AA> x) \<ge> tp D" if "x \<in> A''" for x
            using eqL that by (auto simp: M_def)
          have "\<alpha> \<le> tp A''"
            by (simp add: A'')
          also have "\<dots> \<le> tp {x \<in> A''. tp (M D \<AA> x) \<ge> tp D}"
            by (metis (mono_tags, lifting) tp_M_ge eq_iff mem_Collect_eq subsetI)
          also have "\<dots> \<le> tp {x \<in> A. tp D \<le> tp (M D \<AA> x)}"
            by (rule ordertype_mono) (use A'' A down in auto)
          finally show ?thesis .
        qed
        have [simp]: "tp {0} = 1"
          using ordertype_eq_Ord by fastforce
        have IX': "tp {x \<in> A'. tp (K 1 x \<inter> A) \<ge> \<alpha>} \<ge> \<alpha>"
          if A: "A \<subseteq> elts (\<alpha>*\<beta>)" "tp A = \<alpha>" and A': "A' \<subseteq> elts (\<alpha>*\<beta>)" "tp A' = \<alpha>" for A A'
        proof -
          have \<ddagger>: "\<alpha> \<le> tp (K 1 t \<inter> A)" if "t \<in> A'" "1 \<le> tp {\<nu>. \<nu> = 0 \<and> \<alpha> \<le> tp (K 1 t \<inter> A)}" for t
            using that
            by (metis Collect_empty_eq less_eq_V_0_iff ordertype_empty zero_neq_one)
          have "tp {x \<in> A'. 1 \<le> tp {\<nu>. \<nu> = 0 \<and> \<alpha> \<le> tp (K 1 x \<inter> A)}}
                  \<le> tp {x \<in> A'. \<alpha> \<le> tp (K 1 x \<inter> A)}"
            by (rule ordertype_mono) (use "\<ddagger>" A' in \<open>auto simp: down\<close>)
          then show ?thesis
            using IX [of "{0}" A' "\<lambda>x. A"] that \<open>0 \<in> elts \<beta>\<close>
            by (simp add: M_def cong: conj_cong)
        qed

        have 10: "\<exists>x0 \<in> A. \<exists>g \<in> elts \<beta> \<rightarrow> elts \<beta>. strict_mono_on g (elts \<beta>) \<and> (\<forall>\<nu> \<in> F. g \<nu> = \<nu>)
                                      \<and> (\<forall>\<nu> \<in> elts \<beta>. tp (K 1 x0 \<inter> \<AA> (g \<nu>)) \<ge> \<alpha>)"
          if F: "finite F" "F \<subseteq> elts \<beta>"
            and A: "A \<subseteq> elts (\<alpha>*\<beta>)" "tp A = \<alpha>"
            and \<AA>: "\<AA> \<in> elts \<beta> \<rightarrow> {X. X \<subseteq> elts (\<alpha> * \<beta>) \<and> tp X = \<alpha>}"
          for F A \<AA>
        proof -
          define p where "p \<equiv> card F"
          have "\<beta> \<notin> F"
            using that by auto
          then obtain \<iota> :: "nat \<Rightarrow> V" where bij\<iota>: "bij_betw \<iota> {..p} (insert \<beta> F)" and mon\<iota>: "strict_mono_on \<iota> {..p}"
            using ZFC_Cardinals.ex_bij_betw_strict_mono_card [of "insert \<beta> F"] elts_subset_ON \<open>Ord \<beta>\<close> F
            by (simp add: p_def lessThan_Suc_atMost) blast
          have less_\<iota>_I: "\<iota> k < \<iota> l" if "k < l" "l \<le> p" for k l
            using mon\<iota> that by (auto simp: strict_mono_on_def)
          then have less_\<iota>_D: "k < l" if "\<iota> k < \<iota> l" "k \<le> p" for k l
            by (metis less_asym linorder_neqE_nat that)
          have Ord_\<iota>: "Ord (\<iota> k)" if "k \<le> p" for k
            by (metis (no_types, lifting) ON_imp_Ord atMost_iff insert_subset mem_Collect_eq order_trans  \<open>F \<subseteq> elts \<beta>\<close> bij\<iota> bij_betwE elts_subset_ON \<open>Ord \<beta>\<close> that)
          have le_\<iota>0 [simp]: "\<And>j. j \<le> p \<Longrightarrow> \<iota> 0 \<le> \<iota> j"
            by (metis eq_refl leI le_0_eq less_\<iota>_I less_imp_le)
          have le_\<iota>: "\<iota> i \<le> \<iota> (j - Suc 0)" if "i < j" "j \<le> p" for i j
          proof (cases i)
            case 0 then show ?thesis
              using le_\<iota>0 that by auto
          next
            case (Suc i') then show ?thesis
              by (metis (no_types, hide_lams) Suc_pred le_less less_Suc_eq less_Suc_eq_0_disj less_\<iota>_I not_less_eq that)
          qed

          have [simp]: "\<iota> p = \<beta>"
          proof -
            obtain k where k: "\<iota> k = \<beta>" "k \<le> p"
              by (meson atMost_iff bij\<iota> bij_betw_iff_bijections insertI1)
            then have "k = p \<or> k < p"
              by linarith
            then show ?thesis
              using bij\<iota> ord k that(2)
              by (metis OrdmemD atMost_iff bij_betw_iff_bijections insert_iff leD less_\<iota>_D order_refl subsetD)
          qed

          have F_imp_Ex: "\<exists>k < p. \<xi> = \<iota> k" if "\<xi> \<in> F" for \<xi>
          proof -
            obtain k where k: "k \<le> p" "\<xi> = \<iota> k"
              by (metis \<open>\<xi> \<in> F\<close> atMost_iff bij\<iota> bij_betw_def imageE insert_iff)
            then have "k \<noteq> p"
              using that F by auto
            with k show ?thesis
              using le_neq_implies_less by blast
          qed
          have F_imp_ge: "\<xi> \<ge> \<iota> 0" if "\<xi> \<in> F" for \<xi>
            using F_imp_Ex [OF that] by (metis dual_order.order_iff_strict le0 less_\<iota>_I)
          define D where "D \<equiv> \<lambda>k. (if k=0 then {..<\<iota> 0} else {\<iota> (k-1)<..<\<iota> k}) \<inter> elts \<beta>"
          have D\<beta>: "D k \<subseteq> elts \<beta>" for k
            by (auto simp: D_def)
          then have small_D [simp]: "small (D k)" for k
            by (meson down)
          have M_Int_D: "M (elts \<beta>) \<AA> x \<inter> D k = M (D k) \<AA> x" if "k \<le> p" for x k
            using D\<beta> by (auto simp: M_def)
          have \<iota>_le_if_D: "\<iota> k \<le> \<mu>" if "\<mu> \<in> D (Suc k)" for \<mu> k
            using that
            by (simp add: D_def order.order_iff_strict split: if_split_asm)
          have "disjnt (D i) (D j)" if "i < j" "j \<le> p" for i j
          proof (cases j)
            case (Suc j')
            then show ?thesis
              using that
              apply (auto simp: disjnt_def D_def)
              using not_less_eq by (blast intro: less_\<iota>_D less_trans Suc_leD)+
          qed (use that in auto)
          then have disjnt_DD: "disjnt (D i) (D j)" if "i \<noteq> j" "i \<le> p" "j \<le> p" for i j
            using disjnt_sym nat_neq_iff that by auto
          have UN_D_eq: "(\<Union>l \<le> k. D l) = {..<\<iota> k} \<inter> (elts \<beta> - F)" if "k \<le> p" for k
            using that
          proof (induction k)
            case 0
            then show ?case
              by (auto simp: D_def F_imp_ge leD)
          next
            case (Suc k)
            have "D (Suc k) \<union> {..<\<iota> k} \<inter> (elts \<beta> - F) = {..<\<iota> (Suc k)} \<inter> (elts \<beta> - F)"
              (is "?lhs = ?rhs")
            proof
              show "?lhs \<subseteq> ?rhs"
                using Suc.prems
                by (auto simp: D_def if_split_mem2 intro: less_\<iota>_I less_trans dest!: less_\<iota>_D F_imp_Ex)
              have "\<And>x. \<lbrakk>x < \<iota> (Suc k); x \<in> elts \<beta>; x \<notin> F; \<iota> k \<le> x\<rbrakk> \<Longrightarrow> \<iota> k < x"
                using Suc.prems \<open>F \<subseteq> elts \<beta>\<close> bij\<iota> le_imp_less_or_eq
                by (fastforce simp: bij_betw_iff_bijections)
              then show "?rhs \<subseteq> ?lhs"
                using Suc.prems by (auto simp: D_def Ord_not_less Ord_in_Ord [OF \<open>Ord \<beta>\<close>] Ord_\<iota> if_split_mem2)
            qed
            then
            show ?case
              using Suc by (simp add: atMost_Suc)
          qed
          have \<beta>_decomp: "elts \<beta> = F \<union> (\<Union>k \<le> p. D k)"
            using \<open>F \<subseteq> elts \<beta>\<close> OrdmemD [OF \<open>Ord \<beta>\<close>] by (auto simp: UN_D_eq)
          define \<beta>idx where "\<beta>idx \<equiv> \<lambda>\<nu>. @k. \<nu> \<in> D k \<and> k \<le> p"
          have \<beta>idx: "\<nu> \<in> D (\<beta>idx \<nu>) \<and> \<beta>idx \<nu> \<le> p" if "\<nu> \<in> elts \<beta> - F" for \<nu>
            using that by (force simp: \<beta>idx_def \<beta>_decomp intro: someI_ex del: conjI)
          have any_imp_\<beta>idx: "k = \<beta>idx \<nu>" if "\<nu> \<in> D k" "k \<le> p" for k \<nu>
          proof (rule ccontr)
            assume non: "k \<noteq> \<beta>idx \<nu>"
            have "\<nu> \<notin> F"
              using that UN_D_eq by auto
            then show False
              using disjnt_DD [OF non] by (metis D\<beta> Diff_iff \<beta>idx disjnt_iff subsetD that)
          qed
          have "\<exists>A'. A' \<subseteq> A \<and> tp A' = \<alpha> \<and> (\<forall>x \<in> A'. F \<subseteq> M (elts \<beta>) \<AA> x)"
            using F
          proof induction
            case (insert \<nu> F)
            then obtain A' where "A' \<subseteq> A" and A': "A' \<subseteq> elts (\<alpha>*\<beta>)" "tp A' = \<alpha>" and FN: "\<And>x. x \<in> A' \<Longrightarrow> F \<subseteq> M (elts \<beta>) \<AA> x"
              using A(1) by auto
            define A'' where "A'' \<equiv> {x \<in> A'. \<alpha> \<le> tp (K 1 x \<inter> \<AA> \<nu>)}"
            have "\<nu> \<in> elts \<beta>" "F \<subseteq> elts \<beta>"
              using insert by auto
            note ordertype_eq_Ord [OF \<open>Ord \<beta>\<close>, simp]
            show ?case
            proof (intro exI conjI)
              show "A'' \<subseteq> A"
                using \<open>A' \<subseteq> A\<close> by (auto simp: A''_def)
              have "tp A'' \<le> \<alpha>"
                using \<open>A'' \<subseteq> A\<close> down ordertype_VWF_mono A by blast
              moreover have "\<AA> \<nu> \<subseteq> elts (\<alpha>*\<beta>)" "tp (\<AA> \<nu>) = \<alpha>"
                using \<AA> \<open>\<nu> \<in> elts \<beta>\<close> by auto
              then have "\<alpha> \<le> tp A''"
                using IX' [OF _ _ A'] by (simp add: A''_def)
              ultimately show "tp A'' = \<alpha>"
                by (rule antisym)
              have "\<nu> \<in> M (elts \<beta>) \<AA> x" "F \<subseteq> M (elts \<beta>) \<AA> x"
                if "x \<in> A''" for x
              proof -
                show "F \<subseteq> M (elts \<beta>) \<AA> x"
                  using A''_def FN that by blast
                show "\<nu> \<in> M (elts \<beta>) \<AA> x"
                  using \<open>\<nu> \<in> elts \<beta>\<close> that by (simp add: M_def A''_def)
              qed
              then show "\<forall>x\<in>A''. insert \<nu> F \<subseteq> M (elts \<beta>) \<AA> x"
                by blast
            qed
          qed (use A in auto)
          then obtain A' where A': "A' \<subseteq> A" "tp A' = \<alpha>" and FN: "\<And>x. x \<in> A' \<Longrightarrow> F \<subseteq> M (elts \<beta>) \<AA> x"
            by metis
          have False
            if *: "\<And>x0 g. \<lbrakk>x0 \<in> A; g \<in> elts \<beta> \<rightarrow> elts \<beta>; strict_mono_on g (elts \<beta>)\<rbrakk>
                   \<Longrightarrow> (\<exists>\<nu>\<in>F. g \<nu> \<noteq> \<nu>) \<or> (\<exists>\<nu>\<in>elts \<beta>. tp (K 1 x0 \<inter> \<AA> (g \<nu>)) < \<alpha>)"
          proof -
            { fix x       \<comment> \<open>construction of the monotone map @{term g} mentioned above\<close>
              assume "x \<in> A'"
              with A' have "x \<in> A" by blast
              have "\<exists>k. k \<le> p \<and> tp (M (D k) \<AA> x) < tp (D k)" (is "?P")
              proof (rule ccontr)
                assume "\<not> ?P"
                then have le: "tp (D k) \<le> tp (M (D k) \<AA> x)" if "k \<le> p" for k
                  by (meson Ord_linear2 Ord_ordertype that)
                have "\<exists>f\<in>D k \<rightarrow> M (D k) \<AA> x. inj_on f (D k) \<and> (strict_mono_on f (D k))"
                     if "k \<le> p" for k
                  using le [OF that] that VWF_iff_Ord_less
                  apply (clarsimp simp: ordertype_le_ordertype strict_mono_on_def)
                  by (metis (full_types) D\<beta> M_sub_D Ord_in_Ord PiE VWF_iff_Ord_less ord(2) subsetD)
                then obtain h where fun_h: "\<And>k. k \<le> p \<Longrightarrow> h k \<in> D k \<rightarrow> M (D k) \<AA> x"
                  and inj_h: "\<And>k. k \<le> p \<Longrightarrow> inj_on (h k) (D k)"
                  and mono_h: "\<And>k x y. k \<le> p \<Longrightarrow> strict_mono_on (h k) (D k)"
                  by metis
                then have fun_hD: "\<And>k. k \<le> p \<Longrightarrow> h k \<in> D k \<rightarrow> D k"
                  by (auto simp: M_def)
                have h_increasing: "\<nu> \<le> h k \<nu>"
                  if "k \<le> p" and \<nu>: "\<nu> \<in> D k" for k \<nu>
                proof (rule Ord_mono_imp_increasing)
                  show "h k \<in> D k \<rightarrow> D k"
                    by (simp add: fun_hD that(1))
                  show "D k \<subseteq> ON"
                    using D\<beta> elts_subset_ON ord(2) by blast
                qed (auto simp: that mono_h)
                define g where "g \<equiv> \<lambda>\<nu>. if \<nu> \<in> F then \<nu> else h (\<beta>idx \<nu>) \<nu>"
                have [simp]: "g \<nu> = \<nu>" if "\<nu> \<in> F" for \<nu>
                  using that by (auto simp: g_def)
                have fun_g: "g \<in> elts \<beta> \<rightarrow> elts \<beta>"
                proof (rule Pi_I)
                  fix x assume "x \<in> elts \<beta>"
                  then have "x \<in> D (\<beta>idx x)" "\<beta>idx x \<le> p" if "x \<notin> F"
                    using that by (auto simp: \<beta>idx)
                  then show "g x \<in> elts \<beta>"
                    using fun_h  D\<beta> M_sub_D \<open>x \<in> elts \<beta>\<close>
                    by (simp add: g_def) blast
                qed
                have h_in_D: "h (\<beta>idx \<nu>) \<nu> \<in> D (\<beta>idx \<nu>)" if "\<nu> \<notin> F" "\<nu> \<in> elts \<beta>" for \<nu>
                  using \<beta>idx fun_hD that by fastforce
                have 1: "\<iota> k < h (\<beta>idx \<nu>) \<nu>"
                  if "k < p" and \<nu>: "\<nu> \<notin> F" "\<nu> \<in> elts \<beta>" and "\<iota> k < \<nu>" for k \<nu>
                  using that h_in_D [OF \<nu>] \<beta>idx
                  by (fastforce simp: D_def dest: h_increasing split: if_split_asm)
                moreover have 2: "h (\<beta>idx \<mu>) \<mu> < \<iota> k"
                  if \<mu>: "\<mu> \<notin> F" "\<mu> \<in> elts \<beta>" and "k < p" "\<mu> < \<iota> k" for \<mu> k
                proof -
                  have "\<beta>idx \<mu> \<le> k"
                  proof (rule ccontr)
                    assume "\<not> \<beta>idx \<mu> \<le> k"
                    then have "k < \<beta>idx \<mu>"
                      by linarith
                    then show False
                      using \<iota>_le_if_D \<beta>idx
                      by (metis Diff_iff Suc_pred le0 leD le_\<iota> le_less_trans \<mu> \<open>\<mu> < \<iota> k\<close>)
                  qed
                  then show ?thesis
                    using that h_in_D [OF \<mu>]
                    apply (simp add: D_def split: if_split_asm)
                     apply (metis (no_types) dual_order.order_iff_strict le0 less_\<iota>_I less_trans)
                    by (metis (no_types) dual_order.order_iff_strict less_\<iota>_I less_trans)
                qed
                moreover have "h (\<beta>idx \<mu>) \<mu> < h (\<beta>idx \<nu>) \<nu>"
                  if \<mu>: "\<mu> \<notin> F" "\<mu> \<in> elts \<beta>" and \<nu>: "\<nu> \<notin> F" "\<nu> \<in> elts \<beta>" and "\<mu> < \<nu>" for \<mu> \<nu>
                proof -
                  have le: "\<beta>idx \<mu> \<le> \<beta>idx \<nu>" if "\<iota> (\<beta>idx \<mu> - Suc 0) < h (\<beta>idx \<mu>) \<mu>" "h (\<beta>idx \<nu>) \<nu> < \<iota> (\<beta>idx \<nu>)"
                    by (metis 2 that Diff_iff \<beta>idx \<mu> \<nu> \<open>\<mu> < \<nu>\<close> dual_order.strict_implies_order dual_order.strict_trans1 h_increasing leI le_\<iota> less_asym)
                  have "h 0 \<mu> < h 0 \<nu>" if "\<beta>idx \<mu> = 0" "\<beta>idx \<nu> = 0"
                    using that mono_h unfolding strict_mono_on_def
                    by (metis Diff_iff \<beta>idx \<mu> \<nu> \<open>\<mu> < \<nu>\<close>)
                  moreover have "h 0 \<mu> < h (\<beta>idx \<nu>) \<nu>"
                    if "0 < \<beta>idx \<nu>" "h 0 \<mu> < \<iota> 0" and "\<iota> (\<beta>idx \<nu> - Suc 0) < h (\<beta>idx \<nu>) \<nu>"
                    by (meson DiffI \<beta>idx \<nu> le_\<iota> le_less_trans less_le_not_le that)
                  moreover have "\<beta>idx \<nu> \<noteq> 0"
                    if "0 < \<beta>idx \<mu>" "h 0 \<nu> < \<iota> 0" "\<iota> (\<beta>idx \<mu> - Suc 0) < h (\<beta>idx \<mu>) \<mu>"
                    using le le_0_eq that by fastforce
                  moreover have "h (\<beta>idx \<mu>) \<mu> < h (\<beta>idx \<nu>) \<nu>"
                    if "\<iota> (\<beta>idx \<mu> - Suc 0) < h (\<beta>idx \<mu>) \<mu>" "h (\<beta>idx \<nu>) \<nu> < \<iota> (\<beta>idx \<nu>)"
                       "h (\<beta>idx \<mu>) \<mu> < \<iota> (\<beta>idx \<mu>)" "\<iota> (\<beta>idx \<nu> - Suc 0) < h (\<beta>idx \<nu>) \<nu>"
                    using mono_h unfolding strict_mono_on_def
                      by (metis le Diff_iff \<beta>idx \<mu> \<nu> \<open>\<mu> < \<nu>\<close> le_\<iota> le_less le_less_trans that)
                  ultimately show  ?thesis
                    using h_in_D [OF \<mu>] h_in_D [OF \<nu>] by (simp add: D_def split: if_split_asm)
                qed
                ultimately have sm_g: "strict_mono_on g (elts \<beta>)"
                  by (auto simp: g_def strict_mono_on_def dest!: F_imp_Ex)
                show False
                  using * [OF \<open>x \<in> A\<close> fun_g sm_g]
                proof safe
                  fix \<nu>
                  assume "\<nu> \<in> elts \<beta>" and \<nu>: "tp (K 1 x \<inter> \<AA> (g \<nu>)) < \<alpha>"
                  have FM: "F \<subseteq> M (elts \<beta>) \<AA> x"
                    by (meson FN \<open>x \<in> A'\<close>)
                  have False if "tp (K (Suc 0) x \<inter> \<AA> \<nu>) < \<alpha>" "\<nu> \<in> F"
                    using that FM by (auto simp: M_def)
                  moreover have False if "tp (K (Suc 0) x \<inter> \<AA> (g \<nu>)) < \<alpha>" "\<nu> \<in> D k" "k \<le> p" "\<nu> \<notin> F" for k
                  proof -
                    have "h (\<beta>idx \<nu>) \<nu> \<in> M (D (\<beta>idx \<nu>)) \<AA> x"
                      using fun_h \<beta>idx \<open>\<nu> \<in> elts \<beta>\<close> \<open>\<nu> \<notin> F\<close> by auto
                    then show False
                      using that by (simp add: M_def g_def leD)
                  qed
                  ultimately show False
                    using \<open>\<nu> \<in> elts \<beta>\<close> \<nu> by (force simp: \<beta>_decomp)
                qed auto
              qed
              then have "\<exists>l. l \<le> p \<and> tp (M (elts \<beta>) \<AA> x \<inter> D l) < tp (D l)"
                using M_Int_D by auto
            }
            then obtain l where lp: "\<And>x. x \<in> A'\<Longrightarrow> l x \<le> p"
              and lless: "\<And>x. x \<in> A'\<Longrightarrow> tp (M (elts \<beta>) \<AA> x \<inter> D (l x)) < tp (D (l x))"
              by metis
            obtain A'' L where "A'' \<subseteq> A'" and A'': "A'' \<subseteq> elts (\<alpha> * \<beta>)" "tp A'' = \<alpha>" and lL: "\<And>x. x \<in> A'' \<Longrightarrow> l x = L"
            proof -
              have eq: "A' = (\<Union>i\<le>p. {x \<in> A'. l x = i})"
                using lp by auto
              have "\<exists>X\<in>(\<lambda>i. {x \<in> A'. l x = i}) ` {..p}. \<alpha> \<le> tp X"
              proof (rule indecomposable_ordertype_finite_ge [OF indec])
                show "small (\<Union>i\<le>p. {x \<in> A'. l x = i})"
                  by (metis A'(1) A(1) eq down smaller_than_small)
              qed (use A' eq in auto)
              then show thesis
              proof
                fix A''
                assume A'': "A'' \<in> (\<lambda>i. {x \<in> A'. l x = i}) ` {..p}" and "\<alpha> \<le> tp A''"
                then obtain L where L: "\<And>x. x \<in> A'' \<Longrightarrow> l x = L"
                  by auto
                have "A'' \<subseteq> A'"
                  using A'' by force
                then have "tp A'' \<le> tp A'"
                  by (meson A' A down order_trans ordertype_VWF_mono)
                with \<open>\<alpha> \<le> tp A''\<close> have "tp A'' = \<alpha>"
                  using A'(2) by auto
                moreover have "A'' \<subseteq> elts (\<alpha> * \<beta>)"
                  using A' A \<open>A'' \<subseteq> A'\<close> by auto
                ultimately show thesis
                  using L that [OF \<open>A'' \<subseteq> A'\<close>] by blast
              qed
            qed
            have \<AA>D: "\<AA> \<in> D L \<rightarrow> {X. X \<subseteq> elts (\<alpha> * \<beta>) \<and> tp X = \<alpha>}"
              using \<AA> D\<beta> by blast
            have "M (elts \<beta>) \<AA> x \<inter> D L = M (D L) \<AA> x" for x
              using D\<beta> by (auto simp: M_def)
            then have "tp (M (D L) \<AA> x) < tp (D L)" if "x \<in> A''" for x
              using lless that \<open>A'' \<subseteq> A'\<close> lL by force
            then have \<dagger>: "{x \<in> A''. tp (D L) \<le> tp (M (D L) \<AA> x)} = {}"
              using leD by blast
            have "\<alpha> \<le> tp {x \<in> A''. tp (D L) \<le> tp (M (D L) \<AA> x)}"
              using IX [OF D\<beta> A'' \<AA>D] by simp
            then show False
              using \<open>\<alpha> \<noteq> 0\<close> by (simp add: \<dagger>)
          qed
          then show ?thesis
            by (meson Ord_linear2 Ord_ordertype \<open>Ord \<alpha>\<close>)
        qed
        let ?U = "UNIV :: nat set"
        define \<mu> where "\<mu> \<equiv> fst \<circ> from_nat_into (elts \<beta> \<times> ?U)"
        define q where "q \<equiv> to_nat_on (elts \<beta> \<times> ?U)"
        have co_\<beta>U: "countable (elts \<beta> \<times> ?U)"
          by (simp add: \<beta> less_\<omega>1_imp_countable)
        moreover have "elts \<beta> \<times> ?U \<noteq> {}"
          using \<open>0 \<in> elts \<beta>\<close> by blast
        ultimately have "range (from_nat_into (elts \<beta> \<times> ?U)) = (elts \<beta> \<times> ?U)"
          by (metis range_from_nat_into)
        then have \<mu>_in_\<beta> [simp]: "\<mu> i \<in> elts \<beta>" for i
          by (metis SigmaE \<mu>_def comp_apply fst_conv range_eqI)

        then have Ord_\<mu> [simp]: "Ord (\<mu> i)" for i
          using Ord_in_Ord by blast

        have inf_\<beta>U: "infinite (elts \<beta> \<times> ?U)"
          using \<open>0 \<in> elts \<beta>\<close> finite_cartesian_productD2 by auto

        have 11 [simp]: "\<mu> (q (\<nu>,n)) = \<nu>" if "\<nu> \<in> elts \<beta>" for \<nu> n
          by (simp add: \<mu>_def q_def that co_\<beta>U)
        have range_\<mu> [simp]: "range \<mu> = elts \<beta>"
          by (auto simp: image_iff) (metis 11)
        have [simp]: "KI i {} = UNIV" "KI i (insert a X) = K i a \<inter> KI i X" for i a X
          by (auto simp: KI_def)
        define \<Phi> where "\<Phi> \<equiv> \<lambda>n::nat. \<lambda>\<AA> x. (\<forall>\<nu> \<in> elts \<beta>. \<AA> \<nu> \<subseteq> elts (\<alpha>*\<beta>) \<and> tp (\<AA> \<nu>) = \<alpha>) \<and> x ` {..<n} \<subseteq> elts (\<alpha>*\<beta>)
                                         \<and> (\<Union>\<nu> \<in> elts \<beta>. \<AA> \<nu>) \<subseteq> KI 1 (x ` {..<n}) \<and> strict_mono_sets (elts \<beta>) \<AA>"
        define \<Psi> where "\<Psi> \<equiv> \<lambda>n::nat. \<lambda>g \<AA> \<AA>' xn. g \<in> elts \<beta> \<rightarrow> elts \<beta> \<and> strict_mono_on g (elts \<beta>) \<and> (\<forall>i\<le>n. g (\<mu> i) = \<mu> i)
                  \<and> (\<forall>\<nu> \<in> elts \<beta>. \<AA>' \<nu> \<subseteq> K 1 xn \<inter> \<AA> (g \<nu>))
                  \<and> less_sets {xn} (\<AA>' (\<mu> n)) \<and> xn \<in> \<AA> (\<mu> n)"
        let ?\<AA>0 = "\<lambda>\<nu>. plus (\<alpha> * \<nu>) ` elts \<alpha>"
        have base: "\<Phi> 0 ?\<AA>0 x" for x
          by (auto simp: \<Phi>_def add_mult_less add_mult_less_add_mult ordertype_image_plus strict_mono_sets_def less_sets_def)
        have step: "Ex (\<lambda>(g,\<AA>',xn). \<Psi> n g \<AA> \<AA>' xn \<and> \<Phi> (Suc n) \<AA>' (x(n:=xn)))" if "\<Phi> n \<AA> x" for n \<AA> x
        proof -
          have \<AA>: "\<And>\<nu>. \<nu> \<in> elts \<beta> \<Longrightarrow> \<AA> \<nu> \<subseteq> elts (\<alpha> * \<beta>) \<and> tp (\<AA> \<nu>) = \<alpha>"
            and x: "x ` {..<n} \<subseteq> elts (\<alpha> * \<beta>)"
            and sub: "\<Union> (\<AA> ` elts \<beta>) \<subseteq> KI (Suc 0) (x ` {..<n})"
            and sm: "strict_mono_sets (elts \<beta>) \<AA>"
            using that by (auto simp: \<Phi>_def)
          have \<mu>\<beta>: "\<mu> ` {..n} \<subseteq> elts \<beta>" and \<AA>sub: "\<AA> (\<mu> n) \<subseteq> elts (\<alpha> * \<beta>)"
            by (auto simp: \<AA>)
          have \<AA>fun: "\<AA> \<in> elts \<beta> \<rightarrow> {X. X \<subseteq> elts (\<alpha> * \<beta>) \<and> tp X = \<alpha>}"
            by (simp add: \<AA>)
          then obtain xn g where xn: "xn \<in> \<AA> (\<mu> n)" and g: "g \<in> elts \<beta> \<rightarrow> elts \<beta>"
            and sm_g: "strict_mono_on g (elts \<beta>)" and g_\<mu>: "\<forall>\<nu> \<in> \<mu>`{..n}. g \<nu> = \<nu>"
            and g_\<alpha>: "\<forall>\<nu> \<in> elts \<beta>. \<alpha> \<le> tp (K 1 xn \<inter> \<AA> (g \<nu>))"
            using 10 [OF _ \<mu>\<beta> \<AA>sub _ \<AA>fun] by (auto simp: \<AA>)
          have tp1: "tp (K 1 xn \<inter> \<AA> (g \<nu>)) = \<alpha>" if "\<nu> \<in> elts \<beta>" for \<nu>
          proof (rule antisym)
            have "tp (K 1 xn \<inter> \<AA> (g \<nu>)) \<le> tp (\<AA> (g \<nu>))"
            proof (rule ordertype_VWF_mono)
              show "small (\<AA> (g \<nu>))"
                by (metis PiE \<AA> down g that)
            qed auto
            also have "\<dots> = \<alpha>"
              using \<AA> g that by force
            finally show "tp (K 1 xn \<inter> \<AA> (g \<nu>)) \<le> \<alpha>" .
          qed (use that g_\<alpha> in auto)
          have tp2: "tp (\<AA> (\<mu> n)) = \<alpha>"
            by (auto simp: \<AA>)
          obtain "small (\<AA> (\<mu> n))" "\<AA> (\<mu> n) \<subseteq> ON"
            by (meson \<AA>sub ord down elts_subset_ON subset_trans)
          then obtain A2 where A2: "tp A2 = \<alpha>" "A2 \<subseteq> K 1 xn \<inter> \<AA> (\<mu> n)" "less_sets {xn} A2"
            using indecomposable_imp_Ex_less_sets [OF indec \<open>\<alpha> > 1\<close> tp2]
            by (metis \<mu>_in_\<beta> atMost_iff image_eqI inf_le2 le_refl xn tp1 g_\<mu>)
          then have A2_sub: "A2 \<subseteq> \<AA> (\<mu> n)" by simp
          let ?\<AA> = "\<lambda>\<nu>. if \<nu> = \<mu> n then A2 else K 1 xn \<inter> \<AA> (g \<nu>)"
          have [simp]: "({..<Suc n} \<inter> {x. x \<noteq> n}) = ({..<n})"
            by auto
          have "K (Suc 0) xn \<inter> (\<Union>x\<in>elts \<beta> \<inter> {\<nu>. \<nu> \<noteq> \<mu> n}. \<AA> (g x)) \<subseteq> KI (Suc 0) (x ` {..<n})"
            using sub g by (auto simp: KI_def)
          moreover have "A2 \<subseteq> KI (Suc 0) (x ` {..<n})" "A2 \<subseteq> elts (\<alpha> * \<beta>)"
            using \<AA>sub sub A2 by fastforce+
          moreover have "xn \<in> elts (\<alpha> * \<beta>)"
            using \<AA>sub xn by blast
         moreover have "strict_mono_sets (elts \<beta>) ?\<AA>"
            using sm sm_g g g_\<mu> A2_sub
            unfolding strict_mono_sets_def strict_mono_on_def less_sets_def Pi_iff subset_iff Ball_def Bex_def image_iff
            by (simp (no_asm_use) add: if_split_mem2) (smt order_refl)
          ultimately have "\<Phi> (Suc n) ?\<AA> (x(n := xn))"
            using tp1 x A2 by (auto simp: \<Phi>_def K_def)
          with A2 show ?thesis
            by (rule_tac x="(g,?\<AA>,xn)" in exI) (simp add: \<Psi>_def g sm_g g_\<mu> xn)
        qed
        define G where "G \<equiv> \<lambda>n \<AA> x. @(g,\<AA>',x'). \<exists>xn. \<Psi> n g \<AA> \<AA>' xn \<and> x' = (x(n:=xn)) \<and> \<Phi> (Suc n) \<AA>' x'"
        have G\<Phi>: "(\<lambda>(g,\<AA>',x'). \<Phi> (Suc n) \<AA>' x') (G n \<AA> x)"
          and G\<Psi>: "(\<lambda>(g,\<AA>',x'). \<Psi> n g \<AA> \<AA>' (x' n)) (G n \<AA> x)"  if "\<Phi> n \<AA> x" for n \<AA> x
          using step [OF that] by (force simp: G_def dest: some_eq_imp)+
        define H where "H \<equiv> rec_nat (id,?\<AA>0,undefined) (\<lambda>n (g0,\<AA>,x0). G n \<AA> x0)"
        have H_Suc: "H (Suc n) = (case H n of (g0, xa, xb) \<Rightarrow> G n xa xb)" for n
          by (simp add: H_def)
        have "(\<lambda>(g,\<AA>,x). \<Phi> n \<AA> x) (H n)" for n
        proof (induction n)
          case 0 show ?case
            by (simp add: H_def base)
        next
          case (Suc n) then show ?case
            using G\<Phi> by (fastforce simp: H_Suc)
        qed
        then have H_imp_\<Phi>: "\<Phi> n \<AA> x" if "H n = (g,\<AA>,x)" for g \<AA> x n
          by (metis case_prodD that)
        then have H_imp_\<Psi>: "(\<lambda>(g,\<AA>',x'). let (g0,\<AA>,x) = H n in \<Psi> n g \<AA> \<AA>' (x' n)) (H (Suc n))" for n
          using G\<Psi> by (fastforce simp: H_Suc split: prod.split)
        define g where "g \<equiv> \<lambda>n. (\<lambda>(g,\<AA>,x). g) (H (Suc n))"
        have g: "g n \<in> elts \<beta> \<rightarrow> elts \<beta>" and sm_g: "strict_mono_on (g n) (elts \<beta>)"
                 and 13: "\<And>i. i\<le>n \<Longrightarrow> g n (\<mu> i) = \<mu> i" for n
            using H_imp_\<Psi> [of n] by (auto simp: g_def \<Psi>_def)
        define \<AA> where "\<AA> \<equiv> \<lambda>n. (\<lambda>(g,\<AA>,x). \<AA>) (H n)"
        define x where "x \<equiv> \<lambda>n. (\<lambda>(g,\<AA>,x). x n) (H (Suc n))"
        have 14: "\<AA> (Suc n) \<nu> \<subseteq> K 1 (x n) \<inter> \<AA> n (g n \<nu>)" if "\<nu> \<in> elts \<beta>" for \<nu> n
          using H_imp_\<Psi> [of n] that by (force simp: \<Psi>_def \<AA>_def x_def g_def)
        then have x14: "\<AA> (Suc n) \<nu> \<subseteq> \<AA> n (g n \<nu>)" if "\<nu> \<in> elts \<beta>" for \<nu> n
          using that by blast
        have 15: "x n \<in> \<AA> n (\<mu> n)" and 16: "less_sets {x n} (\<AA> (Suc n) (\<mu> n))" for n
          using H_imp_\<Psi> [of n] by (force simp: \<Psi>_def \<AA>_def x_def)+
        have \<AA>_\<alpha>\<beta>: "\<AA> n \<nu> \<subseteq> elts (\<alpha> * \<beta>)" if "\<nu> \<in> elts \<beta>" for \<nu> n
          using H_imp_\<Phi> [of n] that by (auto simp: \<Phi>_def \<AA>_def split: prod.split)
        have 12: "strict_mono_sets (elts \<beta>) (\<AA> n)" for n
          using H_imp_\<Phi> [of n] that by (auto simp: \<Phi>_def \<AA>_def split: prod.split)
        have tp_\<AA>: "tp (\<AA> n \<nu>) = \<alpha>" if "\<nu> \<in> elts \<beta>" for \<nu> n
          using H_imp_\<Phi> [of n] that by (auto simp: \<Phi>_def \<AA>_def split: prod.split)
        let ?Z = "range x"
        have S_dec: "\<Union> (\<AA> (m+k) ` elts \<beta>) \<subseteq> \<Union> (\<AA> m ` elts \<beta>)" for k m
          by (induction k) (use 14 g in \<open>fastforce+\<close>)
        have "x n \<in> K 1 (x m)" if "m<n" for m n
        proof -
          have "x n \<in> (\<Union>\<nu> \<in> elts \<beta>. \<AA> n \<nu>)"
            by (meson "15" UN_I \<mu>_in_\<beta>)
          also have "\<dots> \<subseteq> (\<Union>\<nu> \<in> elts \<beta>. \<AA> (Suc m) \<nu>)"
            using S_dec [of "Suc m"] less_iff_Suc_add that by auto
          also have "\<dots> \<subseteq> K 1 (x m)"
            using 14 by auto
          finally show ?thesis .
        qed
        then have "f{x m, x n} = 1" if "m<n" for m n
          using that by (auto simp: K_def)
        then have Z_K1: "f ` [?Z]\<^bsup>2\<^esup> \<subseteq> {1}"
          by (clarsimp simp: nsets_2_eq) (metis insert_commute less_linear)
        moreover have Z_sub: "?Z \<subseteq> elts (\<alpha> * \<beta>)"
          using "15" \<AA>_\<alpha>\<beta> \<mu>_in_\<beta> by blast
        moreover have "tp ?Z \<ge> \<omega> * \<beta>"
        proof -
          define \<gg> where "\<gg> \<equiv> \<lambda>i j x. wfrec (measure (\<lambda>k. j-k)) (\<lambda>\<gg> k. if k<j then g k (\<gg> (Suc k)) else x) i"
          have \<gg>: "\<gg> i j x = (if i<j then g i (\<gg> (Suc i) j x) else x)" for i j x
            by (simp add: \<gg>_def wfrec cut_apply)
          have 17: "\<gg> k j (\<mu> i) = \<mu> i" if "i \<le> k" for i j k
            using wf_measure [of "\<lambda>k. j-k"] that
            by (induction k rule: wf_induct_rule) (simp add: "13" \<gg> le_imp_less_Suc)
          have \<gg>_in_\<beta>: "\<gg> i j \<nu>  \<in> elts \<beta>" if "\<nu> \<in> elts \<beta>" for i j \<nu>
            using wf_measure [of "\<lambda>k. j-k"] that
          proof (induction i rule: wf_induct_rule)
            case (less i)
            with g show ?case by (force simp: \<gg> [of i])
          qed
          then have \<gg>_fun: "\<gg> i j \<in> elts \<beta> \<rightarrow> elts \<beta>" for i j
            by simp
          have sm_\<gg>: "strict_mono_on (\<gg> i j) (elts \<beta>)" for i j
            using wf_measure [of "\<lambda>k. j-k"]
          proof (induction i rule: wf_induct_rule)
            case (less i)
            with sm_g show ?case
              by (auto simp: \<gg> [of i] strict_mono_on_def \<gg>_in_\<beta>)
          qed
          have *: "\<AA> j (\<mu> j) \<subseteq> \<AA> i (\<gg> i j (\<mu> j))" if "i < j" for i j
            using wf_measure [of "\<lambda>k. j-k"] that
          proof (induction i rule: wf_induct_rule)
            case (less i)
            then have "j - Suc i < j - i"
              by (metis (no_types) Suc_diff_Suc lessI)
            with less \<gg>_in_\<beta> show ?case
              by (simp add: \<gg> [of i]) (metis 17 Suc_lessI \<mu>_in_\<beta> order_refl order_trans x14)
          qed
          have le: "\<gg> i j (\<mu> j) \<le> \<mu> i \<longleftrightarrow> \<mu> j \<le> \<mu> i" for i j
            using sm_\<gg> unfolding strict_mono_on_def
            by (metis "17" Ord_in_Ord Ord_linear2 \<mu>_in_\<beta> leD le_refl less_V_def \<open>Ord \<beta>\<close>)
          then have less: "\<gg> i j (\<mu> j) < \<mu> i \<longleftrightarrow> \<mu> j < \<mu> i" for i j
            by (metis (no_types, lifting) "17" \<mu>_in_\<beta> less_V_def order_refl sm_\<gg> strict_mono_on_def)
          have eq: "\<gg> i j (\<mu> j) = \<mu> i \<longleftrightarrow> \<mu> j = \<mu> i" for i j
            by (metis eq_refl le less less_le)
          have 18: "less_sets (\<AA> m (\<mu> m)) (\<AA> n (\<mu> n)) \<longleftrightarrow> \<mu> m < \<mu> n" for m n
          proof (cases n m rule: linorder_cases)
            case less
            show ?thesis
            proof (intro iffI)
              assume "less_sets (\<AA> m (\<mu> m)) (\<AA> n (\<mu> n))"
              moreover
              have "\<not> less_sets (\<AA> m (\<mu> m)) (\<AA> n (\<mu> n))" if "\<mu> n = \<mu> m"
                by (metis "*" "15" eq less less_V_def less_sets_def less_sets_weaken2 that)
              moreover
              have "\<not> less_sets (\<AA> m (\<mu> m)) (\<AA> n (\<mu> n))" if "\<mu> n < \<mu> m"
                using that 12 15 * [OF less]
                apply (clarsimp simp: less_sets_def strict_mono_sets_def)
                by (metis Ord_in_Ord Ord_linear2 \<gg>_in_\<beta> \<mu>_in_\<beta> \<open>Ord \<beta>\<close> le leD less_asym subsetD)
              ultimately show "\<mu> m < \<mu> n"
                by (meson Ord_in_Ord Ord_linear_lt \<mu>_in_\<beta> \<open>Ord \<beta>\<close>)
            next
              assume "\<mu> m < \<mu> n"
              then have "less_sets (\<AA> n (\<gg> n m (\<mu> m))) (\<AA> n (\<mu> n))"
                by (metis "12" \<gg>_in_\<beta> \<mu>_in_\<beta> eq le less_V_def strict_mono_sets_def)
              then show "less_sets (\<AA> m (\<mu> m)) (\<AA> n (\<mu> n))"
                by (meson *[OF less] less_sets_weaken1)
          qed
          next
            case equal
            with 15 show ?thesis by auto
          next
            case greater
            show ?thesis
            proof (intro iffI)
              assume "less_sets (\<AA> m (\<mu> m)) (\<AA> n (\<mu> n))"
              moreover
              have "\<not> less_sets (\<AA> m (\<mu> m)) (\<AA> n (\<mu> n))" if "\<mu> n = \<mu> m"
                by (metis "*" "15" disjnt_iff eq greater in_mono less_sets_imp_disjnt that)
              moreover
              have "\<not> less_sets (\<AA> m (\<mu> m)) (\<AA> n (\<mu> n))" if "\<mu> n < \<mu> m"
                using that 12 15 * [OF greater]
                apply (clarsimp simp: less_sets_def strict_mono_sets_def)
                by (meson \<gg>_in_\<beta> \<mu>_in_\<beta> in_mono less less_asym)
              ultimately show "\<mu> m < \<mu> n"
                by (meson Ord_\<mu> Ord_linear_lt)
            next
              assume "\<mu> m < \<mu> n"
              then have "less_sets (\<AA> m (\<mu> m)) (\<AA> m (\<gg> m n (\<mu> n)))"
                by (meson 12 Ord_in_Ord Ord_linear2 \<gg>_in_\<beta> \<mu>_in_\<beta> le leD ord(2) strict_mono_sets_def)
              then show "less_sets (\<AA> m (\<mu> m)) (\<AA> n (\<mu> n))"
                by (meson "*" greater less_sets_weaken2)
            qed
          qed
          have \<AA>_increasing_\<mu>: "\<AA> n (\<mu> n) \<subseteq> \<AA> m (\<mu> m)" if "m \<le> n" "\<mu> m = \<mu> n" for m n
            by (metis "*" "17" dual_order.order_iff_strict that)
          moreover have INF: "infinite {n. n \<ge> m \<and> \<mu> m = \<mu> n}" for m
          proof -
            have "infinite (range (\<lambda>n. q (\<mu> m, n)))"
              unfolding q_def
              using to_nat_on_infinite [OF co_\<beta>U inf_\<beta>U] finite_image_iff
              by (simp add: finite_image_iff inj_on_def)
            moreover have "(range (\<lambda>n. q (\<mu> m, n))) \<subseteq> {n. \<mu> m = \<mu> n}"
              using 11 [of "\<mu> m"] by auto
            ultimately have "infinite {n. \<mu> m = \<mu> n}"
              using finite_subset by auto
            then have "infinite ({n. \<mu> m = \<mu> n} - {..<m})"
              by simp
            then show ?thesis
              by (auto simp: finite_nat_set_iff_bounded Bex_def not_less)
          qed
          let ?eqv = "\<lambda>m. {n. m \<le> n \<and> \<mu> m = \<mu> n}"
          have sm_x: "strict_mono_on x (?eqv m)" for m
          proof (clarsimp simp: strict_mono_on_def)
            fix n p
            assume "m \<le> n" "\<mu> p = \<mu> n" "\<mu> m = \<mu> n" "n < p"
            with 16 [of n] show "x n < x p"
              by (simp add: less_sets_def) (metis "*" "15" "17" Suc_lessI le_SucI subsetD)
          qed
          then have inj_x: "inj_on x (?eqv m)" for m
            using strict_mono_on_imp_inj_on by blast
          define ZA where "ZA \<equiv> \<lambda>m. ?Z \<inter> \<AA> m (\<mu> m)"
          have small_ZA [simp]: "small (ZA m)" for m
            by (metis ZA_def inf_le1 small_image_nat smaller_than_small)
          have 19: "tp (ZA m) \<ge> \<omega>" for m
          proof -
            have "x ` {n. m \<le> n \<and> \<mu> m = \<mu> n} \<subseteq> ZA m"
              unfolding ZA_def using "15" \<AA>_increasing_\<mu> by blast
            then have "infinite (ZA m)"
              using INF [of m] finite_image_iff [OF inj_x] by (meson finite_subset)
            then show ?thesis
              by (simp add: ordertype_infinite_ge_\<omega>)
          qed
          have "\<exists>f \<in> elts \<omega> \<rightarrow> ZA m. strict_mono_on f (elts \<omega>)" for m
          proof -
            obtain Z where "Z \<subseteq> ZA m" "tp Z = \<omega>"
              by (meson 19 Ord_\<omega> le_ordertype_obtains_subset small_ZA)
            moreover have "ZA m \<subseteq> ON"
              using Ord_in_Ord \<AA>_\<alpha>\<beta> \<mu>_in_\<beta> unfolding ZA_def by blast
            ultimately show ?thesis
              by (metis strict_mono_on_ordertype Pi_mono small_ZA smaller_than_small subset_iff)
          qed
          then obtain \<phi> where \<phi>: "\<And>m. \<phi> m \<in> elts \<omega> \<rightarrow> ZA m"
                         and sm_\<phi>: "\<And>m. strict_mono_on (\<phi> m) (elts \<omega>)"
            by metis
          have "Ex(\<lambda>(m,\<nu>). \<nu> \<in> elts \<beta> \<and> \<gamma> = \<omega> * \<nu> + ord_of_nat m)" if "\<gamma> \<in> elts (\<omega> * \<beta>)" for \<gamma>
            using that by (auto simp: mult [of \<omega> \<beta>] lift_def elts_\<omega>)
          then obtain split where split: "\<And>\<gamma>. \<gamma> \<in> elts (\<omega> * \<beta>) \<Longrightarrow>
             (\<lambda>(m,\<nu>). \<nu> \<in> elts \<beta> \<and> \<gamma> = \<omega> * \<nu> + ord_of_nat m)(split \<gamma>)"
            by meson
          have split_eq [simp]: "split (\<omega> * \<nu> + ord_of_nat m) = (m,\<nu>)" if "\<nu> \<in> elts \<beta>" for \<nu> m
          proof -
            have [simp]: "\<omega> * \<nu> + ord_of_nat m = \<omega> * \<xi> + ord_of_nat n \<longleftrightarrow> \<xi> = \<nu> \<and> n = m" if "\<xi> \<in> elts \<beta>" for \<xi> n
              by (metis Ord_\<omega> that Ord_mem_iff_less_TC mult_cancellation_lemma ord_of_nat_\<omega> ord_of_nat_inject)
            show ?thesis
              using split [of "\<omega>*\<nu> + m"] that by (auto simp: mult [of \<omega> \<beta>] lift_def cong: conj_cong)
          qed
          define \<pi> where "\<pi> \<equiv> \<lambda>\<gamma>. (\<lambda>(m,\<nu>). \<phi> (q(\<nu>,0)) m)(split \<gamma>)"
          have \<pi>_Pi: "\<pi> \<in> elts (\<omega> * \<beta>) \<rightarrow> (\<Union>m. ZA m)"
            using \<phi> by (fastforce simp: \<pi>_def mult [of \<omega> \<beta>] lift_def elts_\<omega>)
          moreover have "(\<Union>m. ZA m) \<subseteq> ON"
            unfolding ZA_def using \<AA>_\<alpha>\<beta> \<mu>_in_\<beta> elts_subset_ON by blast
          ultimately have Ord_\<pi>_Pi: "\<pi> \<in> elts (\<omega> * \<beta>) \<rightarrow> ON"
            by fastforce
          show "tp ?Z \<ge> \<omega> * \<beta>"
          proof -
            have \<dagger>: "(\<Union>m. ZA m) = ?Z"
              using "15" by (force simp: ZA_def)
            moreover
            have "tp (elts (\<omega> * \<beta>)) \<le> tp (\<Union>m. ZA m)"
            proof (rule ordertype_inc_le)
              show "\<pi> ` elts (\<omega> * \<beta>) \<subseteq> (\<Union>m. ZA m)"
                using \<pi>_Pi by blast
            next
              fix u v
              assume x: "u \<in> elts (\<omega> * \<beta>)" and y: "v \<in> elts (\<omega> * \<beta>)" and "(u,v) \<in> VWF"
              then have "u<v"
                by (meson Ord_\<omega> Ord_in_Ord Ord_mult VWF_iff_Ord_less ord(2))
              moreover
              obtain m \<nu> n \<xi> where ueq: "u = \<omega> * \<nu> + ord_of_nat m" and \<nu>: "\<nu> \<in> elts \<beta>"
                             and veq: "v = \<omega> * \<xi> + ord_of_nat n" and \<xi>: "\<xi> \<in> elts \<beta>"
                using x y by (auto simp:  mult [of \<omega> \<beta>] lift_def elts_\<omega>)
              ultimately have "\<nu> \<le> \<xi>"
                by (meson Ord_\<omega> Ord_in_Ord Ord_linear2 \<open>Ord \<beta>\<close> add_mult_less_add_mult less_asym ord_of_nat_\<omega>)
              consider (eq) "\<nu> = \<xi>" | (lt) "\<nu> < \<xi>"
                using \<open>\<nu> \<le> \<xi>\<close> le_neq_trans by blast
              then have "\<pi> u < \<pi> v"
              proof cases
                case eq
                then have "m < n"
                  using ueq veq \<open>u<v\<close> by simp
                then have "\<phi> (q (\<xi>, 0)) m < \<phi> (q (\<xi>, 0)) n"
                  using sm_\<phi> strict_mono_onD by blast
                then show ?thesis
                  using eq ueq veq \<nu> \<open>m < n\<close> by (simp add: \<pi>_def)
              next
                case lt
                have "\<phi> (q(\<nu>,0)) m \<in> \<AA> (q(\<nu>,0)) (\<mu>(q(\<nu>,0)))" "\<phi> (q (\<xi>,0)) n \<in> \<AA> (q(\<xi>,0)) (\<mu>(q(\<xi>,0)))"
                  using \<phi> unfolding ZA_def by blast+
                then show ?thesis
                  using lt ueq veq \<nu> \<xi> 18 [of "q(\<nu>,0)" "q(\<xi>,0)"]
                  by (simp add: \<pi>_def less_sets_def)
              qed
              then show "(\<pi> u, \<pi> v) \<in> VWF"
                using \<pi>_Pi
                by (metis Ord_\<pi>_Pi PiE VWF_iff_Ord_less x y mem_Collect_eq)
            qed (use \<dagger> in auto)
            ultimately show ?thesis by simp
          qed
        qed
        then obtain Z where "Z \<subseteq> ?Z" "tp Z = \<omega> * \<beta>"
          by (meson Ord_\<omega> Ord_mult ord Z_sub down le_ordertype_obtains_subset)
        ultimately show False
          using iii [of Z] by (meson dual_order.trans image_mono nsets_mono)
      qed
      have False
        if 0: "\<forall>H. tp H = ord_of_nat (2*k) \<longrightarrow> H \<subseteq> elts (\<alpha>*\<beta>) \<longrightarrow> \<not> f ` [H]\<^bsup>2\<^esup> \<subseteq> {0}"
          and 1: "\<forall>H. tp H = min \<gamma> (\<omega> * \<beta>) \<longrightarrow> H \<subseteq> elts (\<alpha>*\<beta>) \<longrightarrow> \<not> f ` [H]\<^bsup>2\<^esup> \<subseteq> {1}"
      proof (cases "\<omega>*\<beta> \<le> \<gamma>")
        case True
        then have \<dagger>: "\<exists>H'\<subseteq>H. tp H' = \<omega> * \<beta>" if "tp H = \<gamma>" "small H" for H
          by (metis Ord_\<omega> Ord_\<omega>1 Ord_in_Ord Ord_mult \<beta> le_ordertype_obtains_subset that)
        have [simp]: "min \<gamma> (\<omega>*\<beta>) = \<omega>*\<beta>"
          by (simp add: min_absorb2 that True)
        then show ?thesis
          using * [OF 0] 1 True
          by simp (meson \<dagger> down image_mono nsets_mono subset_trans)
      next
        case False
        then have \<dagger>: "\<exists>H'\<subseteq>H. tp H' = \<gamma>" if "tp H = \<omega> * \<beta>" "small H" for H
          by (metis Ord_linear_le Ord_ordertype \<open>Ord \<gamma>\<close> le_ordertype_obtains_subset that)
        then have "\<gamma> \<le> \<omega>*\<beta>"
          by (meson Ord_\<omega> Ord_\<omega>1 Ord_in_Ord Ord_linear_le Ord_mult \<beta> \<open>Ord \<gamma>\<close> False)
        then have [simp]: "min \<gamma> (\<omega>*\<beta>) = \<gamma>"
          by (simp add: min_absorb1)
        then show ?thesis
          using * [OF 0] 1 False
          by simp (meson \<dagger> down image_mono nsets_mono subset_trans)
      qed
      then show "\<exists>i<Suc (Suc 0). \<exists>H\<subseteq>elts (\<alpha>*\<beta>). tp H = [ord_of_nat (2*k), min \<gamma> (\<omega>*\<beta>)] ! i \<and> f ` [H]\<^bsup>2\<^esup> \<subseteq> {i}"
        by force
    qed
  qed
qed


theorem Erdos_Milner:
  assumes \<nu>: "\<nu> \<in> elts \<omega>1"
  shows "partn_lst_VWF (\<omega>\<up>(1 + \<nu> * ord_of_nat n)) [ord_of_nat (2^n), \<omega>\<up>(1+\<nu>)] 2"
proof (induction n)
  case 0
  then show ?case
    using partn_lst_VWF_degenerate [of 1 2] by simp
next
  case (Suc n)
  have "Ord \<nu>"
    using Ord_\<omega>1 Ord_in_Ord assms by blast
  have "1+\<nu> \<le> \<nu>+1"
    by (simp add: \<open>Ord \<nu>\<close> one_V_def plus_Ord_le)
  then have [simp]: "min (\<omega> \<up> (1 + \<nu>)) (\<omega> * \<omega> \<up> \<nu>) = \<omega> \<up> (1+\<nu>)"
    by (simp add: \<open>Ord \<nu>\<close> oexp_add min_def)
  have ind: "indecomposable (\<omega> \<up> (1 + \<nu> * ord_of_nat n))"
    by (simp add: \<open>Ord \<nu>\<close> indecomposable_\<omega>_power)
  show ?case
  proof (cases "n = 0")
    case True
    then show ?thesis
      using partn_lst_VWF_\<omega>_2 \<open>Ord \<nu>\<close> one_V_def by auto
  next
    case False
    then have "Suc 0 < 2 ^ n"
      using less_2_cases not_less_eq by fastforce
    then have "partn_lst_VWF (\<omega> \<up> (1 + \<nu> * n) * \<omega> \<up> \<nu>) [ord_of_nat (2 * 2 ^ n), \<omega> \<up> (1 + \<nu>)] 2"
      using Erdos_Milner_aux [OF Suc ind, where \<beta> = "\<omega>\<up>\<nu>"] \<open>Ord \<nu>\<close> \<nu>
      by (auto simp: countable_oexp)
    then show ?thesis
      using \<open>Ord \<nu>\<close> by (simp add: mult_succ mult.assoc oexp_add)
  qed
qed


corollary remark_3: "partn_lst_VWF (\<omega>\<up>(Suc(4*k))) [4, \<omega>\<up>(Suc(2*k))] 2"
  using Erdos_Milner [of "2*k" 2]
  apply (simp flip: ord_of_nat_mult ord_of_nat.simps)
  by (simp add: one_V_def)


text \<open>Theorem 3.2 of Jean A. Larson, ibid.\<close>
corollary Theorem_3_2:
  fixes k n::nat
  shows "partn_lst_VWF (\<omega>\<up>(n*k)) [\<omega>\<up>n, ord_of_nat k] 2"
proof (cases "n=0 \<or> k=0")
  case True
  then show ?thesis
    by (auto intro: partn_lst_triv0 [where i=1] partn_lst_triv1 [where i=0])
next
  case False
  then have "n > 0" "k > 0"
    by auto
  have PV: "partn_lst_VWF (\<omega> \<up> (1 + ord_of_nat (n-1) * ord_of_nat (k-1))) [ord_of_nat (2 ^ (k-1)), \<omega> \<up> (1 + ord_of_nat (n-1))] 2"
    using Erdos_Milner [of "ord_of_nat (n-1)" "k-1"] Ord_\<omega>1 Ord_mem_iff_lt less_imp_le by blast
  have "k+n \<le> Suc (Suc(k-1) * Suc(n-1))"
    by simp
  also have "\<dots> \<le> Suc (k * n)"
    using False by auto
  finally have "1 + (n - 1) * (k - 1) \<le> (n*k)"
    using False by (auto simp: algebra_simps)
  then have "(1 + ord_of_nat (n - 1) * ord_of_nat (k - 1)) \<le> ord_of_nat(n*k)"
    by (metis (mono_tags, lifting) One_nat_def one_V_def ord_of_nat.simps ord_of_nat_add ord_of_nat_mono_iff ord_of_nat_mult)
  then have x: "\<omega> \<up> (1 + ord_of_nat (n - 1) * ord_of_nat (k - 1)) \<le> \<omega>\<up>(n*k)"
    by (simp add: oexp_mono_le)
  then have "partn_lst_VWF (\<omega>\<up>(n*k)) [\<omega> \<up> (1 + ord_of_nat (n-1)), ord_of_nat (2 ^ (k-1))] 2"
    by (metis PV partn_lst_two_swap Partitions.partn_lst_greater_resource less_eq_V_def)
  moreover have "(1 + ord_of_nat (n-1)) = ord_of_nat n"
    using ord_of_minus_1 [OF \<open>n > 0\<close>]
    by (simp add: one_V_def)
  ultimately have "partn_lst_VWF (\<omega>\<up>(n*k)) [\<omega> \<up> n, ord_of_nat (2 ^ (k-1))] 2"
    by simp
  then show ?thesis
    using power_gt_expt [of 2 "k-1"]
    by (force simp: less_Suc_eq intro: partn_lst_less)
qed

end
