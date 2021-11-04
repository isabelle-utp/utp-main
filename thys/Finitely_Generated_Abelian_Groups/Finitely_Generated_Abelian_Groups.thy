(*
    File:     Finitely_Generated_Abelian_Groups.thy
    Author:   Joseph Thommes, TU München
*)
section \<open>Fundamental Theorem of Finitely Generated Abelian Groups\<close>

theory Finitely_Generated_Abelian_Groups
  imports DirProds Group_Relations
begin

notation integer_mod_group ("Z")

locale fin_gen_comm_group = comm_group +
  fixes gen :: "'a set"
  assumes gens_closed: "gen \<subseteq> carrier G"
  and     fin_gen: "finite gen"
  and     generators: "carrier G = generate G gen"

text \<open>Every finite abelian group is also finitely generated.\<close>

sublocale finite_comm_group \<subseteq> fin_gen_comm_group G "carrier G"
  using generate_incl generate_sincl by (unfold_locales, auto)

text \<open>This lemma contains the proof of Kemper from his lecture notes on algebra~\cite{kemper}.
However, the proof is not done in the context of a finitely generated group but for a finitely
generated subgroup in a commutative group.\<close>

lemma (in comm_group) ex_idirgen:
  fixes A :: "'a set"
  assumes "finite A" "A \<subseteq> carrier G"
  shows "\<exists>gs. set gs \<subseteq> generate G A \<and> distinct gs \<and> is_idirprod (generate G A) (\<lambda>g. generate G {g}) (set gs)
            \<and> successively (dvd) (map ord gs) \<and> card (set gs) \<le> card A"
  (is "?t A")
  using assms
proof (induction "card A" arbitrary: A rule: nat_less_induct)
  case i: 1
  show ?case
  proof (cases "relations A = {restrict (\<lambda>_. 0::int) A}") (* only trivial relation *)
    case True
    have fi: "finite A" by fact
    then obtain gs where gs: "set gs = A" "distinct gs" by (meson finite_distinct_list)
    have o: "ord g = 0" if "g \<in> set gs" for g
      by (intro relations_zero_imp_ord_zero[OF that], use i(3) that True gs in auto)
    have m: "map ord gs = replicate (length gs) 0" using o
      by (induction gs; auto)
    show ?thesis
    proof(intro exI conjI subsetI)
      show "\<And>x. x \<in> set gs \<Longrightarrow> x \<in> generate G A" using gs generate.incl[of _ A G] by blast
      show "distinct gs" by fact
      show "is_idirprod (generate G A) (\<lambda>g. generate G {g}) (set gs)"
      proof(unfold is_idirprod_def, intro conjI, rule)
        show "generate G {g} \<lhd> G" if "g \<in> set gs" for g
          by (intro subgroup_imp_normal, use that generate_is_subgroup i(3) gs in auto)
        show "generate G A = IDirProds G (\<lambda>g. generate G {g}) (set gs)" unfolding IDirProds_def
          by (subst gs(1), use generate_idem_Un i(3) in blast)
        show "compl_fam (\<lambda>g. generate G {g}) (set gs)" using compl_fam_iff_relations_triv[OF i(2, 3)] o gs(1) True
          by blast 
      qed
      show "successively (dvd) (map ord gs)" using m
      proof (induction gs)
        case c: (Cons a gs)
        thus ?case by(cases gs; simp)
      qed simp
      show "card (set gs) \<le> card A" using gs by blast
    qed
  next
    case ntrel: False
    then have Ane: "A \<noteq> {}"
      using i(2) triv_rel[of A] unfolding relations_def extensional_def by fastforce
    from ntrel obtain a where a: "a \<in> A" "\<exists>r \<in>relations A. r a \<noteq> 0" using i(2) triv_rel[of A]
      unfolding relations_def extensional_def by fastforce
    hence ac: "a \<in> carrier G" using i(3) by blast
    have iH: "\<And>B.\<lbrakk>card B < card A; finite B; B \<subseteq> carrier G\<rbrakk> \<Longrightarrow> ?t B"
      using i(1) by blast
    have iH2: "\<And>B. \<lbrakk>?t B; generate G A = generate G B; card B < card A\<rbrakk> \<Longrightarrow> ?t A"
      by fastforce
    show ?thesis
    proof(cases "inv a \<in> (A - {a})")
      case True
      have "generate G A = generate G (A - {a})"
      proof(intro generate_subset_eqI[OF i(3)])
        show "A - (A - {a}) \<subseteq> generate G (A - {a})"
        proof -
          have "A - (A - {a}) = {a}" using a True by auto
          also have "\<dots> \<subseteq> generate G {inv a}" using generate.inv[of "inv a" "{inv a}" G] ac by simp
          also have "\<dots> \<subseteq> generate G (A - {a})" by (intro mono_generate, use True in simp)
          finally show ?thesis .
        qed
      qed simp
      moreover have "?t (A - {a})"
        by (intro iH[of "A - {a}"], use i(2, 3) a(1) in auto, meson Ane card_gt_0_iff diff_Suc_less)
      ultimately show ?thesis using card.remove[OF i(2) a(1)] by fastforce
    next
      case inv: False
      define n where n: "n = card A"
      define all_gens where
        "all_gens = {gs\<in>Pow (generate G A). finite gs \<and> card gs \<le> n \<and> generate G gs = generate G A}"

      define exps where "exps = (\<Union>gs'\<in>all_gens. \<Union>rel\<in>relations gs'. nat ` {e\<in>rel`gs'. e > 0})"
      define min_exp where "min_exp = Inf exps"

      have "exps \<noteq> {}"
      proof -
        let ?B = "A - {a} \<union> {inv a}"
        have "A \<in> all_gens" unfolding all_gens_def using generate.incl n i(2) by fast
        moreover have "?B \<in> all_gens"
        proof -
          have "card (A - {a}) = n - 1" using a n by (meson card_Diff_singleton_if i(2))
          hence "card ?B = n" using inv i(2, 3) n a(1)
            by (metis Un_empty_right Un_insert_right card.remove card_insert_disjoint finite_Diff) 
          moreover have "generate G A = generate G ?B"
          proof(intro generate_one_switched_eqI[OF i(3) a(1), of _ "inv a"])
            show "inv a \<in> generate G A" using generate.inv[OF a(1), of G] .
            show "a \<in> generate G ?B"
            proof -
              have "a \<in> generate G {inv a}" using generate.inv[of "inv a" "{inv a}" G] ac by simp
              also have "\<dots> \<subseteq> generate G ?B" by (intro mono_generate, blast)
              finally show ?thesis .
            qed
          qed simp
          moreover hence "?B \<subseteq> generate G A" using generate_sincl by simp
          ultimately show ?thesis unfolding all_gens_def using i(2) by blast
        qed
        moreover have "(\<exists>r \<in> relations A. r a > 0) \<or> (\<exists>r \<in> relations ?B. r (inv a) > 0)"
        proof(cases "\<exists>r \<in> relations A. r a > 0")
          case True
          then show ?thesis by blast
        next
          case False
          with a obtain r where r: "r \<in> relations A" "r a < 0" by force
          have rc: "(\<lambda>x. x [^] r x) \<in> A \<rightarrow> carrier G" using i(3) int_pow_closed by fast
          let ?r = "restrict (r(inv a := - r a)) ?B"
          have "?r \<in> relations ?B"
          proof
            have "finprod G (\<lambda>x. x [^] ?r x) ?B = finprod G (\<lambda>x. x [^] r x) A"
            proof -
              have "finprod G (\<lambda>x. x [^] ?r x) ?B
                  = finprod G (\<lambda>x. x [^] ?r x) (insert (inv a) (A - {a}))" by simp
              also have "\<dots> = (inv a) [^] ?r (inv a) \<otimes> finprod G (\<lambda>x. x [^] ?r x) (A - {a})"
              proof(intro finprod_insert[OF _ inv])
                show "finite (A - {a})" using i(2) by fast
                show "inv a [^] ?r (inv a) \<in> carrier G"
                  using int_pow_closed[OF inv_closed[OF ac]] by fast
                show "(\<lambda>x. x [^] ?r x) \<in> A - {a} \<rightarrow> carrier G" using int_pow_closed i(3) by fast
              qed
              also have "\<dots> = a [^] r a \<otimes> finprod G (\<lambda>x. x [^] r x) (A - {a})"
              proof -
                have "(inv a) [^] ?r (inv a) = a [^] r a"
                  by (simp add: int_pow_inv int_pow_neg ac)
                moreover have "finprod G (\<lambda>x. x [^] r x) (A - {a})
                             = finprod G (\<lambda>x. x [^] ?r x) (A - {a})"
                proof(intro finprod_cong)
                  show "((\<lambda>x. x [^] r x) \<in> A - {a} \<rightarrow> carrier G) = True" using rc by blast
                  have "i [^] r i = i [^] ?r i" if "i \<in> A - {a}" for i using that inv by auto
                  thus "\<And>i. i \<in> A - {a} =simp=> i [^] r i = i [^] restrict (r(inv a := - r a)) (A - {a} \<union> {inv a}) i"
                    by algebra
                qed simp
                ultimately show ?thesis by argo
              qed
              also have "\<dots> = finprod G (\<lambda>x. x [^] r x) A"
                by (intro finprod_minus[symmetric, OF a(1) rc i(2)])
              finally show ?thesis .
            qed
            also have "\<dots> = \<one>" using r unfolding relations_def by fast
            finally show "finprod G (\<lambda>x. x [^] ?r x) ?B = \<one>" .
          qed simp
          then show ?thesis using r by fastforce
        qed
        ultimately show ?thesis unfolding exps_def using a by blast
      qed
      hence me: "min_exp \<in> exps"
        unfolding min_exp_def using Inf_nat_def1 by force
      from cInf_lower min_exp_def have le: "\<And>x. x \<in> exps \<Longrightarrow> min_exp \<le> x" by blast
      from me obtain gs rel g
        where gr: "gs \<in> all_gens" "rel \<in> relations gs" "g \<in> gs" "rel g = min_exp" "min_exp > 0"
        unfolding exps_def by auto
      from gr(1) have cgs: "card gs \<le> card A" unfolding all_gens_def n by blast
      with gr(3) have cgsg: "card (gs - {g}) < card A"
        by (metis Ane card.infinite card_Diff1_less card_gt_0_iff finite.emptyI
                  finite.insertI finite_Diff2 i.prems(1) le_neq_implies_less less_trans)
      from gr(1) have fgs: "finite gs" and gsg: "generate G gs = generate G A"
        unfolding all_gens_def n using i(2) card.infinite Ane by force+
      from gsg have gsc: "gs \<subseteq> carrier G" unfolding all_gens_def
        using generate_incl[OF i(3)] generate_sincl[of gs] by simp
      hence gc: "g \<in> carrier G" using gr(3) by blast
      have ihgsg: "?t (gs - {g})"
        by (intro iH, use cgs fgs gsc gr(3) cgsg in auto)
      then obtain hs where
        hs: "set hs \<subseteq> generate G (gs - {g})" "distinct hs"
            "is_idirprod (generate G (gs - {g})) (\<lambda>g. generate G {g}) (set hs)"
            "successively (dvd) (map ord hs)" "card (set hs) \<le> card (gs - {g})" by blast
      hence hsc: "set hs \<subseteq> carrier G"
        using generate_sincl[of "set hs"] generate_incl[of "gs - {g}"] gsc by blast
      from hs(3) have ghs: "generate G (gs - {g}) = generate G (set hs)"
        unfolding is_idirprod_def IDirProds_def using generate_idem_Un[OF hsc] by argo
      have dvot: "?t A \<or> (\<forall>e\<in>rel`gs. rel g dvd e)"
      proof(intro disjCI)
        assume na: "\<not> (\<forall>e\<in>rel ` gs. rel g dvd e)"
        have "\<And>x. \<lbrakk>x \<in> gs; \<not>rel g dvd rel x\<rbrakk> \<Longrightarrow> ?t A"
        proof -
          fix x
          assume x: "x \<in> gs" "\<not> rel g dvd rel x"
          hence xng: "x \<noteq> g" by auto
          from x have xc: "x \<in> carrier G" using gsc by blast
          have rg: "rel g > 0" using gr by simp
          define r::int where r: "r = rel x mod rel g"
          define q::int where q: "q = rel x div rel g"
          from r rg x have "r > 0"
            using mod_int_pos_iff[of "rel x" "rel g"] mod_eq_0_iff_dvd by force
          moreover have "r < rel g" using r rg Euclidean_Division.pos_mod_bound by blast
          moreover have "rel x = q * rel g + r" using r q by presburger
          ultimately have rq: "rel x = q * (rel g) + r" "0 < r" "r < rel g" by auto
          define t where t: "t = g \<otimes> x [^] q"
          hence tc: "t \<in> carrier G" using gsc gr(3) x by fast
          define s where s: "s = gs - {g} \<union> {t}"
          hence fs: "finite s" using fgs by blast
          have sc: "s \<subseteq> carrier G" using s tc gsc by blast
          have g: "generate G gs = generate G s"
          proof(unfold s, intro generate_one_switched_eqI[OF gsc gr(3), of _ t])
            show "t \<in> generate G gs"
            proof(unfold t, intro generate.eng)
              show "g \<in> generate G gs" using gr(3) generate.incl by fast
              show "x [^] q \<in> generate G gs"
                using x generate_pow[OF xc] generate_sincl[of "{x}"] mono_generate[of "{x}" gs]
                by fast
            qed
            show "g \<in> generate G (gs - {g} \<union> {t})"
            proof -
              have gti: "g = t \<otimes> inv (x [^] q)"
                using inv_solve_right[OF gc tc int_pow_closed[OF xc, of q]] t by blast
              moreover have "t \<in> generate G (gs - {g} \<union> {t})" by (intro generate.incl[of t], simp)
              moreover have "inv (x [^] q) \<in> generate G (gs - {g})"
              proof -
                have "x [^] q \<in> generate G {x}" using generate_pow[OF xc] by blast
                from generate_m_inv_closed[OF _ this] xc
                have "inv (x [^] q) \<in> generate G {x}" by blast
                moreover have "generate G {x} \<subseteq> generate G (gs - {g})"
                  by (intro mono_generate, use x a in force)
                finally show ?thesis .
              qed
              ultimately show ?thesis
                using generate.eng mono_generate[of "gs - {g}" "gs - {g} \<union> {t}"] by fast
            qed
          qed simp
          show "\<lbrakk>x \<in> gs; \<not> rel g dvd rel x\<rbrakk> \<Longrightarrow> ?t A"
          proof (cases "t \<in> gs - {g}")
            case xt: True
            from xt have gts: "s = gs - {g}" using x s by auto
            moreover have "card (gs - {g}) < card gs" using fgs gr(3) by (meson card_Diff1_less)
            ultimately have "card (set hs) < card A" using hs(5) cgs by simp
            moreover have "set hs \<subseteq> generate G (set hs)" using generate_sincl by simp
            moreover have "distinct hs" by fact
            moreover have "is_idirprod (generate G (set hs)) (\<lambda>g. generate G {g}) (set hs)"
              using hs ghs unfolding is_idirprod_def by blast
            moreover have "generate G A = generate G (set hs)" using g gts ghs gsg by argo
            moreover have "successively (dvd) (map ord hs)" by fact
            ultimately show "?t A" using iH2 by blast
          next
            case tngsg: False
            hence xnt: "x \<noteq> t" using x xng by blast
            have "rel g dvd rel x"
            proof (rule ccontr)
              have "nat r \<in> exps" unfolding exps_def
              proof
                show "s \<in> all_gens" unfolding all_gens_def
                  using gsg g fgs generate_sincl[of s] switch_elem_card_le[OF gr(3), of t] cgs n s
                  by auto
                have xs: "x \<in> s" using s xng x(1) by blast
                have ts: "t \<in> s" using s by fast
                show "nat r \<in> (\<Union>rel\<in>relations s. nat ` {e \<in> rel ` s. 0 < e})"
                proof
                  let ?r = "restrict (rel(x := r, t := rel g)) s"
                  show "?r \<in> relations s"
                  proof
                    have "finprod G (\<lambda>x. x [^] ?r x) s = finprod G (\<lambda>x. x [^] rel x) gs"
                    proof -
                      have "finprod G (\<lambda>x. x [^] ?r x) s = x [^] r \<otimes> (t [^] rel g \<otimes> finprod G (\<lambda>x. x [^] rel x) (gs - {g} - {x}))"
                      proof -
                        have "finprod G (\<lambda>x. x [^] ?r x) s = x [^] ?r x \<otimes> finprod G (\<lambda>x. x [^] ?r x) (s - {x})"
                          by (intro finprod_minus[OF xs _ fs], use sc in auto) 
                        moreover have "finprod G (\<lambda>x. x [^] ?r x) (s - {x}) = t [^] ?r t \<otimes> finprod G (\<lambda>x. x [^] ?r x) (s - {x} - {t})"
                          by (intro finprod_minus, use ts xnt fs sc in auto)
                        moreover have "finprod G (\<lambda>x. x [^] ?r x) (s - {x} - {t}) = finprod G (\<lambda>x. x [^] rel x) (s - {x} - {t})"
                          unfolding s by (intro finprod_cong',  use gsc in auto)
                        moreover have "s - {x} - {t} = gs - {g} - {x}" unfolding s using tngsg by blast
                        moreover hence "finprod G (\<lambda>x. x [^] rel x) (s - {x} - {t}) = finprod G (\<lambda>x. x [^] rel x) (gs - {g} - {x})" by simp
                        moreover have "x [^] ?r x = x [^] r" using xs xnt by auto
                        moreover have "t [^] ?r t = t [^] rel g" using ts by simp
                        ultimately show ?thesis by argo
                      qed
                      also have "\<dots> = x [^] r \<otimes> t [^] rel g \<otimes> finprod G (\<lambda>x. x [^] rel x) (gs - {g} - {x})"
                        by (intro m_assoc[symmetric], use xc tc in simp_all, intro finprod_closed, use gsc in fast)
                      also have "\<dots> = g [^] rel g \<otimes> x [^] rel x \<otimes> finprod G (\<lambda>x. x [^] rel x) (gs - {g} - {x})"
                      proof -
                        have "x [^] r \<otimes> t [^] rel g = g [^] rel g \<otimes> x [^] rel x"
                        proof -
                          have "x [^] r \<otimes> t [^] rel g = x [^] r \<otimes> (g \<otimes> x [^] q) [^] rel g" using t by blast
                          also have "\<dots> = x [^] r \<otimes> x [^] (q * rel g) \<otimes> g [^] rel g"
                          proof -
                            have "(g \<otimes> x [^] q) [^] rel g = g [^] rel g \<otimes> (x [^] q) [^] rel g"
                              using gc xc int_pow_distrib by auto
                            moreover have "(x [^] q) [^] rel g = x [^] (q * rel g)" using xc int_pow_pow by auto
                            moreover have "g [^] rel g \<otimes> x [^] (q * rel g) = x [^] (q * rel g) \<otimes> g [^] rel g"
                              using m_comm[OF int_pow_closed[OF xc] int_pow_closed[OF gc]] by simp
                            ultimately have "(g \<otimes> x [^] q) [^] rel g = x [^] (q * rel g) \<otimes> g [^] rel g" by argo
                            thus ?thesis by (simp add: gc m_assoc xc)
                          qed
                          also have "\<dots> = x [^] rel x \<otimes> g [^] rel g"
                          proof -
                            have "x [^] r \<otimes> x [^] (q * rel g) = x [^] (q * rel g + r)"
                              by (simp add: add.commute int_pow_mult xc)
                            also have "\<dots> = x [^] rel x" using rq by argo
                            finally show ?thesis by argo
                          qed
                          finally show ?thesis by (simp add: gc m_comm xc)
                        qed
                        thus ?thesis by simp
                      qed
                      also have "\<dots> = g [^] rel g \<otimes> (x [^] rel x \<otimes> finprod G (\<lambda>x. x [^] rel x) (gs - {g} - {x}))"
                        by (intro m_assoc, use xc gc in simp_all, intro finprod_closed, use gsc in fast)
                      also have "\<dots> = g [^] rel g \<otimes> finprod G (\<lambda>x. x [^] rel x) (gs - {g})"
                      proof -
                        have "finprod G (\<lambda>x. x [^] rel x) (gs - {g}) = x [^] rel x \<otimes> finprod G (\<lambda>x. x [^] rel x) (gs - {g} - {x})"
                          by (intro finprod_minus, use xng x(1) fgs gsc in auto)
                        thus ?thesis by argo
                      qed
                      also have "\<dots> = finprod G (\<lambda>x. x [^] rel x) gs" by (intro finprod_minus[symmetric, OF gr(3) _ fgs], use gsc in auto)
                      finally show ?thesis .
                    qed                        
                    thus "finprod G (\<lambda>x. x [^] ?r x) s = \<one>" using gr(2) unfolding relations_def by simp
                  qed auto
                  show "nat r \<in> nat ` {e \<in> ?r ` s. 0 < e}" using xs xnt rq(2) by fastforce
                qed
              qed
              from le[OF this] rq(3) gr(4, 5) show False by linarith
            qed
            thus "\<lbrakk>x \<in> gs; \<not> rel g dvd rel x\<rbrakk> \<Longrightarrow> ?t A" by blast
          qed
        qed
        thus "?t A" using na by blast
      qed
      show "?t A"
      proof (cases "\<forall>e\<in>rel`gs. rel g dvd e")
        case dv: True
        define tau where "tau = finprod G (\<lambda>x. x [^] ((rel x) div rel g)) gs"
        have tc: "tau \<in> carrier G"
          by (subst tau_def, intro finprod_closed[of "(\<lambda>x. x [^] ((rel x) div rel g))" gs], use gsc in fast) 
        have gts: "generate G gs = generate G (gs - {g} \<union> {tau})"
        proof(intro generate_one_switched_eqI[OF gsc gr(3), of _ tau])
          show "tau \<in> generate G gs" by (subst generate_eq_finprod_Pi_int_image[OF fgs gsc], unfold tau_def, fast)
          show "g \<in> generate G (gs - {g} \<union> {tau})"
          proof -
            have "tau = g \<otimes> finprod G (\<lambda>x. x [^] ((rel x) div rel g)) (gs - {g})"
            proof -
              have "finprod G (\<lambda>x. x [^] ((rel x) div rel g)) gs = g [^] (rel g div rel g) \<otimes> finprod G (\<lambda>x. x [^] ((rel x) div rel g)) (gs - {g})"
                by (intro finprod_minus[OF gr(3) _ fgs], use gsc in fast)
              moreover have "g [^] (rel g div rel g) = g" using gr gsc by auto
              ultimately show ?thesis unfolding tau_def by argo
            qed
            hence gti: "g = tau \<otimes> inv finprod G (\<lambda>x. x [^] ((rel x) div rel g)) (gs - {g})"
              using inv_solve_right[OF gc tc finprod_closed[of "(\<lambda>x. x [^] ((rel x) div rel g))" "gs - {g}"]] gsc
              by fast
            have "tau \<in> generate G (gs - {g} \<union> {tau})" by (intro generate.incl[of tau], simp)
            moreover have "inv finprod G (\<lambda>x. x [^] ((rel x) div rel g)) (gs - {g}) \<in> generate G (gs - {g})"
            proof -
              have "finprod G (\<lambda>x. x [^] ((rel x) div rel g)) (gs - {g}) \<in> generate G (gs - {g})"
                using generate_eq_finprod_Pi_int_image[of "gs - {g}"] fgs gsc by fast
              from  generate_m_inv_closed[OF _ this] gsc show ?thesis by blast
            qed
            ultimately show ?thesis by (subst gti, intro generate.eng, use mono_generate[of "gs - {g}"] in auto)
          qed
        qed simp
        with gr(1) have gt: "generate G (gs - {g} \<union> {tau}) = generate G A" unfolding all_gens_def by blast
        have trgo: "tau [^] rel g = \<one>"
        proof -
          have "tau [^] rel g = finprod G (\<lambda>x. x [^] ((rel x) div rel g)) gs [^] rel g" unfolding tau_def by blast
          also have "\<dots> = finprod G ((\<lambda>x. x [^] rel g) \<circ> (\<lambda>x. x [^] ((rel x) div rel g))) gs"
            by (intro finprod_exp, use gsc in auto)
          also have "\<dots> = finprod G (\<lambda>a. a [^] rel a) gs"
          proof(intro finprod_cong')
            show "((\<lambda>x. x [^] rel g) \<circ> (\<lambda>x. x [^] ((rel x) div rel g))) x = x [^] rel x" if "x \<in> gs" for x
            proof -
              have "((\<lambda>x. x [^] rel g) \<circ> (\<lambda>x. x [^] ((rel x) div rel g))) x = x [^] (((rel x) div rel g) * rel g)"
                using that gsc int_pow_pow by auto
              also have "\<dots> = x [^] rel x" using dv that by auto
              finally show ?thesis .
            qed
          qed (use gsc in auto)
          also have "\<dots> = \<one>" using gr(2) unfolding relations_def by blast
          finally show ?thesis .
        qed
        hence otdrg: "ord tau dvd rel g" using tc int_pow_eq_id by force
        have ot: "ord tau = rel g"
        proof -
          from gr(4, 5) have "rel g > 0" by simp
          with otdrg have "ord tau \<le> rel g" by (meson zdvd_imp_le)
          moreover have "\<not>ord tau < rel g" 
          proof
            assume a: "int (ord tau) < rel g"
            define T where T: "T = gs - {g} \<union> {tau}"
            hence tT: "tau \<in> T" by blast
            let ?r = "restrict ((\<lambda>_.(0::int))(tau := int(ord tau))) T"
            from T have "T \<in> all_gens"
              using gt generate_sincl[of "gs - {g} \<union> {tau}"] switch_elem_card_le[OF gr(3), of tau] fgs cgs n
              unfolding all_gens_def by auto
            moreover have "?r \<in> relations T"
            proof(intro in_relationsI finprod_one_eqI)
              have "tau [^] int (ord tau) = \<one>" using tc pow_ord_eq_1[OF tc] int_pow_int by metis
              thus "x [^] ?r x = \<one>" if "x \<in> T" for x using tT that by(cases "\<not>x = tau", auto)
            qed auto
            moreover have "?r tau = ord tau" using tT by auto
            moreover have "ord tau > 0" using dvd_nat_bounds gr(4) gr(5) int_dvd_int_iff otdrg by presburger
            ultimately have "ord tau \<in> exps" unfolding exps_def using tT by (auto, force)
            with le a gr(4) show False by force
          qed
          ultimately show ?thesis by auto
        qed
        hence otnz: "ord tau \<noteq> 0" using gr me exps_def by linarith
        define l where l: "l = tau#hs"
        hence ls: "set l = set hs \<union> {tau}" by auto
        with hsc tc have slc: "set l \<subseteq> carrier G" by auto
        have gAhst: "generate G A = generate G (set hs \<union> {tau})"
        proof -
          have "generate G A = generate G (gs - {g} \<union> {tau})" using gt by simp
          also have "\<dots> = generate G (set hs \<union> {tau})"
            by (rule generate_subset_change_eqI, use hsc gsc tc ghs in auto)
          finally show ?thesis .
        qed
        have glgA: "generate G (set l) = generate G A" using gAhst ls by simp
        have lgA: "set l \<subseteq> generate G A"
          using ls gt gts hs(1)
                mono_generate[of "gs - {g}" gs] generate.incl[of tau "gs - {g} \<union> {tau}"]
          by fast
        show ?thesis
        proof (cases "ord tau = 1")
          case True
          hence "tau = \<one>" using ord_eq_1 tc by blast
          hence "generate G A = generate G (gs - {g})"
            using gAhst generate_one_irrel hs(3) ghs by auto
          from iH2[OF ihgsg this cgsg] show ?thesis .
        next
          case otau: False
          consider (nd) "\<not>distinct l" | (ltn) "length l < n \<and> distinct l" | (dn) "length l = n \<and> distinct l"
          proof -
            have "length l \<le> n"
            proof -
              have "length l = length hs + 1" using l by simp
              moreover have "length hs \<le> card (gs - {g})" using hs(2, 5) by (metis distinct_card)
              moreover have "card (gs - {g}) + 1 \<le> n"
                using n cgsg gr(3) fgs Ane i(2) by (simp add: card_gt_0_iff)
              ultimately show ?thesis by linarith
            qed
            thus "\<lbrakk>\<not> distinct l \<Longrightarrow> thesis; length l < n \<and> distinct l \<Longrightarrow> thesis; length l = n \<and> distinct l \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis"
              by linarith 
          qed
          thus ?thesis
          proof(cases)
            case nd
            with hs(2) l have ths: "set hs = set hs \<union> {tau}" by auto
            hence "set l = set hs" using l by auto
            hence "generate G (gs - {g}) = generate G A" using gAhst ths ghs by argo
            moreover have "card (set hs) \<le> card A"
              by (metis Diff_iff card_mono cgs dual_order.trans fgs hs(5) subsetI)
            ultimately show ?thesis using hs by auto
          next
            case ltn
            then have cl: "card (set l) < card A" using n by (metis distinct_card)
            from iH[OF this] hsc tc ls have "?t (set l)" by blast
            thus ?thesis by (subst (1 2) gAhst, use cl ls in fastforce)
          next
            case dn
            hence ln: "length l = n" and dl: "distinct l" by auto
            have c: "complementary (generate G {tau}) (generate G (gs - {g}))"
            proof -
              have "x = \<one>" if "x \<in> generate G {tau} \<inter> generate G (set hs)" for x
              proof -
                from that generate_incl[OF hsc] have xc: "x \<in> carrier G" by blast
                from that have xgt: "x \<in> generate G {tau}" and xgs: "x \<in> generate G (set hs)"
                  by auto
                from generate_nat_pow[OF otnz tc] xgt have "\<exists>a. a \<ge> 0 \<and> a < ord tau \<and> x = tau [^] a"
                  unfolding atLeastAtMost_def atLeast_def atMost_def
                  by (auto, metis Suc_pred less_Suc_eq_le neq0_conv otnz)
                then obtain a where a: "0 \<le> a" "a < ord tau" "x = tau [^] a" by blast
                then have ix: "inv x \<in> generate G (set hs)"
                  using xgs generate_m_inv_closed ghs hsc by blast
                with generate_eq_finprod_Pi_int_image[OF _ hsc] obtain f where
                  f: "f \<in> Pi (set hs) (\<lambda>_. (UNIV::int set))" "inv x = finprod G (\<lambda>g. g [^] f g) (set hs)"
                  by blast
                let ?f = "restrict (f(tau := a)) (set l)"
                have fr: "?f \<in> relations (set l)"
                proof(intro in_relationsI)
                  from ls dl l have sh: "set hs = set l - {tau}" by auto
                  have "finprod G (\<lambda>a. a [^] ?f a) (set l) = tau [^] ?f tau \<otimes> finprod G (\<lambda>a. a [^] ?f a) (set hs)"
                    by (subst sh, intro finprod_minus, use l slc in auto)
                  moreover have "tau [^] ?f tau = x" using a l int_pow_int by fastforce
                  moreover have "finprod G (\<lambda>a. a [^] ?f a) (set hs) = finprod G (\<lambda>g. g [^] f g) (set hs)"
                    by (intro finprod_cong', use slc dl l in auto)
                  ultimately have "finprod G (\<lambda>a. a [^] ?f a) (set l) = x \<otimes> inv x" using f by argo
                  thus "finprod G (\<lambda>a. a [^] ?f a) (set l) = \<one>" using xc by auto
                qed blast
                have "\<not>a > 0"
                proof
                  assume ag: "0 < a"
                  have "set l \<in> all_gens" unfolding all_gens_def using glgA lgA dn distinct_card
                    by fastforce
                  moreover have "int a = ?f tau" using l by auto
                  moreover have "tau \<in> set l" using l by simp
                  ultimately have "a \<in> exps" using fr ag unfolding exps_def by (auto, force)
                  from le[OF this] a(2) ot gr(4) show False by simp
                qed
                hence "a = 0" using a by blast
                thus "x = \<one>" using tc a by force
              qed
              thus ?thesis unfolding complementary_def using generate.one ghs by blast
            qed
            moreover have idl: "is_idirprod (generate G A) (\<lambda>g. generate G {g}) (set l)" 
            proof -
              have "is_idirprod (generate G (set hs \<union> {tau})) (\<lambda>g. generate G {g}) (set hs \<union> {tau})"
                by (intro idirprod_generate_ind, use tc hsc hs(3) ghs c in auto)
              thus ?thesis using ls gAhst by auto
            qed
            moreover have "\<not>?t A \<Longrightarrow> successively (dvd) (map ord l)"
            proof (cases hs)
              case Nil
              thus ?thesis using l by simp
            next
              case (Cons a list)
              hence ac: "a \<in> carrier G" using hsc by auto
              assume nA: "\<not>?t A"
              have "ord tau dvd ord a"
              proof (rule ccontr)
                assume nd: "\<not> ord tau dvd ord a"
                have "int (ord tau) > 0" using otnz by simp
                with nd obtain r q::int where rq: "ord a = q * (ord tau) + r" "0 < r" "r < ord tau"
                  using Euclidean_Division.pos_mod_bound div_mult_mod_eq mod_int_pos_iff mod_0_imp_dvd
                  by (metis linorder_not_le of_nat_le_0_iff of_nat_mod)
                define b where b: "b = tau \<otimes> a [^] q"
                hence bc: "b \<in> carrier G" using hsc tc Cons by auto
                have g: "generate G (set (b#hs)) = generate G (set l)"
                proof -
                  have se: "set (b#hs) = set l - {tau} \<union> {b}" using l Cons dl by auto
                  show ?thesis
                  proof(subst se, intro generate_one_switched_eqI[symmetric, of _ tau _ b])
                    show "b \<in> generate G (set l)"
                    proof -
                      have "tau \<in> generate G (set l)" using l generate.incl[of tau "set l"] by auto
                      moreover have "a [^] q \<in> generate G (set l)" 
                        using mono_generate[of "{a}" "set l"] generate_pow[OF ac] Cons l by auto
                      ultimately show ?thesis using b generate.eng by fast
                    qed
                    show "tau \<in> generate G (set l - {tau} \<union> {b})"
                    proof -
                      have "tau = b \<otimes> inv(a [^] q)" by (simp add: ac b m_assoc tc)
                      moreover have "b \<in> generate G (set l - {tau} \<union> {b})"
                        using generate.incl[of b "set l - {tau} \<union> {b}"] by blast
                      moreover have "inv(a [^] q) \<in> generate G (set l - {tau} \<union> {b})"
                      proof -
                        have "generate G {a} \<subseteq> generate G (set l - {tau} \<union> {b})"
                          using mono_generate[of "{a}" "set l - {tau} \<union> {b}"] dl Cons l by auto
                        moreover have "inv(a [^] q) \<in> generate G {a}"
                          by (subst generate_pow[OF ac], subst int_pow_neg[OF ac, of q, symmetric], blast)
                        ultimately show ?thesis by fast
                      qed
                      ultimately show ?thesis using generate.eng by fast
                    qed
                  qed (use bc tc hsc dl Cons l in auto)
                qed
                show False
                proof (cases "card (set (b#hs)) \<noteq> n")
                  case True
                  hence cln: "card (set (b#hs)) < n"
                    using l Cons ln by (metis card_length list.size(4) nat_less_le)
                  hence seq: "set (b#hs) = set hs"
                  proof -
                    from dn l Cons True have "b \<in> set hs"
                      by (metis distinct.simps(2) distinct_card list.size(4))
                    thus ?thesis by auto
                  qed
                  with cln have clA: "card (set hs) < card A" using n by auto
                  moreover have "set hs \<subseteq> generate G (set hs)" using generate_sincl by simp
                  moreover have "distinct hs" by fact
                  moreover have "is_idirprod (generate G (set hs)) (\<lambda>g. generate G {g}) (set hs)"
                    by (intro is_idirprod_generate, use hs[unfolded is_idirprod_def] hsc in auto)
                  moreover have "generate G A = generate G (set hs)" using glgA g seq by argo
                  moreover have "successively (dvd) (map ord hs)" by fact
                  ultimately show False using iH2 nA by blast
                next
                  case False
                  hence anb: "a \<noteq> b"
                    by (metis card_distinct distinct_length_2_or_more l list.size(4) ln local.Cons)
                  have "nat r \<in> exps" unfolding exps_def
                  proof(rule)
                    show "set (b#hs) \<in> all_gens" unfolding all_gens_def
                      using gAhst g ls generate_sincl[of "set (b#hs)"] False by simp
                    let ?r = "restrict ((\<lambda>_. 0::int)(b := ord tau, a := r)) (set (b#hs))"
                    have "?r \<in> relations (set (b#hs))"
                    proof(intro in_relationsI)
                      show "finprod G (\<lambda>x. x [^] ?r x) (set (b#hs)) = \<one>"
                      proof -
                        have "finprod G (\<lambda>x. x [^] ?r x) (set (b#hs)) = b [^] ?r b \<otimes> finprod G (\<lambda>x. x[^] ?r x) (set (b#hs) - {b})"
                          by (intro finprod_minus, use hsc Cons bc in auto)
                        moreover have "finprod G (\<lambda>x. x[^] ?r x) (set (b#hs) - {b}) = a [^] ?r a \<otimes> finprod G (\<lambda>x. x[^] ?r x) (set (b#hs) - {b} - {a})"
                          by (intro finprod_minus, use hsc Cons False n anb in auto)
                        moreover have "finprod G (\<lambda>x. x[^] ?r x) (set (b#hs) - {b} - {a}) = \<one>"
                          by (intro finprod_one_eqI, simp)
                        ultimately have "finprod G (\<lambda>x. x [^] ?r x) (set (b#hs)) = b [^] ?r b \<otimes> (a [^] ?r a \<otimes> \<one>)"
                          by argo
                        also have "\<dots> = b [^] ?r b \<otimes> a [^] ?r a" using Cons hsc by simp
                        also have "\<dots> = b [^] int(ord tau) \<otimes> a [^] r" using anb Cons by simp
                        also have "\<dots> = \<one>"
                        proof -
                          have "b [^] int (ord tau) = tau [^] int (ord tau) \<otimes> (a [^] q) [^] int (ord tau)"
                            using b bc hsc int_pow_distrib local.Cons tc by force
                          also have "\<dots> = (a [^] q) [^] int (ord tau)"
                            using trgo hsc local.Cons ot by force
                          finally have "b [^] int (ord tau) \<otimes> a [^] r = (a [^] q) [^] int (ord tau) \<otimes> a [^] r"
                            by argo
                          also have "\<dots> = a [^] (q * int (ord tau) + r)" using Cons hsc
                            by (metis comm_group_axioms comm_group_def group.int_pow_pow
                                      int_pow_mult list.set_intros(1) subsetD)
                          also have "\<dots> = a [^] int (ord a)" using rq by argo
                          finally show ?thesis using Cons hsc int_pow_eq_id by simp
                        qed
                        finally show ?thesis .
                      qed
                    qed simp
                    moreover have "r \<in> {e \<in> ?r ` set (b # hs). 0 < e}"
                    proof (rule, rule, rule)
                      show "0 < r" by fact
                      show "a \<in> set (b#hs)" using Cons by simp
                      thus "r = ?r a" by auto
                    qed
                    ultimately show "nat r \<in> (\<Union>rel\<in>relations (set (b # hs)). nat ` {e \<in> rel ` set (b # hs). 0 < e})"
                      by fast
                  qed
                  moreover have "nat r < min_exp" using ot rq(2, 3) gr(4) by linarith
                  ultimately show False using le by fastforce
                qed
              qed
              thus ?thesis using hs(4) Cons l by simp
            qed
            ultimately show ?thesis using lgA n dn by (metis card_length)
          qed
        qed
      qed (use dvot in blast)
    qed
  qed
qed

lemma (in comm_group) fundamental_subgr:
  fixes A :: "'a set"
  assumes "finite A" "A \<subseteq> carrier G"
  obtains gs where
    "set gs \<subseteq> generate G A" "distinct gs" "is_idirprod (generate G A) (\<lambda>g. generate G {g}) (set gs)"
    "successively (dvd) (map ord gs)" "card (set gs) \<le> card A"
  using assms ex_idirgen by meson

text \<open>As every group is a subgroup of itself, the theorem follows directly. However, for reasons of
convenience and uniqueness (although not completely proved), we strengthen the result by proving
that the decomposition can be done without having the trivial factor in the product.
We formulate the theorem in various ways: firstly, the invariant factor decomposition.\<close>

theorem (in fin_gen_comm_group) invariant_factor_decomposition_idirprod:
  obtains gs where
    "set gs \<subseteq> carrier G" "distinct gs" "is_idirprod (carrier G) (\<lambda>g. generate G {g}) (set gs)"
    "successively (dvd) (map ord gs)" "card (set gs) \<le> card gen" "\<one> \<notin> set gs"
proof -
  from fundamental_subgr[OF fin_gen gens_closed] obtain gs where
  gs: "set gs \<subseteq> carrier G" "distinct gs" "is_idirprod (carrier G) (\<lambda>g. generate G {g}) (set gs)"
    "successively (dvd) (map ord gs)" "card (set gs) \<le> card gen" using generators by auto
  hence cf: "compl_fam (\<lambda>g. generate G {g}) (set gs)" by simp
  let ?r = "remove1 \<one> gs"
  have r: "set ?r = set gs - {\<one>}" using gs by auto
  have "set ?r \<subseteq> carrier G" using gs by auto
  moreover have "distinct ?r" using gs by auto
  moreover have "is_idirprod (carrier G) (\<lambda>g. generate G {g}) (set ?r)"
  proof (intro is_idirprod_generate)
    show "set ?r \<subseteq> carrier G" using gs by auto
    show "compl_fam (\<lambda>g. generate G {g}) (set (remove1 \<one> gs))"
      by (rule compl_fam_generate_subset[OF cf gs(1)], use set_remove1_subset in fastforce)
    show "carrier G = generate G (set ?r)"
    proof -
      have "generate G (set ?r) = generate G (set gs)" using generate_one_irrel' r by simp
      with gs(3) show ?thesis by simp
    qed
  qed
  moreover have "successively (dvd) (map ord ?r)"
  proof (cases gs)
    case (Cons a list)
    have r: "(map ord (remove1 \<one> gs)) = remove1 1 (map ord gs)" using gs(1) 
    proof(induction gs)
      case (Cons a gs)
      hence "a \<in> carrier G" by simp
      with Cons ord_eq_1[OF this] show ?case by auto
    qed simp
    show ?thesis by (unfold r,
                     rule transp_successively_remove1[OF _ gs(4), unfolded transp_def],
                     auto)
  qed simp
  moreover have "card (set ?r) \<le> card gen" using gs(5) r
    by (metis List.finite_set card_Diff1_le dual_order.trans)
  moreover have "\<one> \<notin> set ?r" using gs(2) by auto
  ultimately show ?thesis using that by blast
qed

corollary (in fin_gen_comm_group) invariant_factor_decomposition_dirprod:
  obtains gs where
    "set gs \<subseteq> carrier G" "distinct gs"
    "DirProds (\<lambda>g. G\<lparr>carrier := generate G {g}\<rparr>) (set gs) \<cong> G"
    "successively (dvd) (map ord gs)" "card (set gs) \<le> card gen"
    "compl_fam (\<lambda>g. generate G {g}) (set gs)" "\<one> \<notin> set gs"
proof -
  from invariant_factor_decomposition_idirprod obtain gs where
    gs: "set gs \<subseteq> carrier G" "distinct gs" "is_idirprod (carrier G) (\<lambda>g. generate G {g}) (set gs)"
        "successively (dvd) (map ord gs)" "card (set gs) \<le> card gen" "\<one> \<notin> set gs" by blast
  with cong_DirProds_IDirProds[OF gs(3)] gs 
  have "DirProds (\<lambda>g. G\<lparr>carrier := generate G {g}\<rparr>) (set gs) \<cong> G" by blast
  with gs that show ?thesis by auto
qed

corollary (in fin_gen_comm_group) invariant_factor_decomposition_dirprod_fam:
  obtains Hs where
    "\<And>H. H \<in> set Hs \<Longrightarrow> subgroup H G" "distinct Hs"
    "DirProds (\<lambda>H. G\<lparr>carrier := H\<rparr>) (set Hs) \<cong> G" "successively (dvd) (map card Hs)"
    "card (set Hs) \<le> card gen" "compl_fam id (set Hs)" "{\<one>} \<notin> set Hs"
proof -
  from invariant_factor_decomposition_dirprod obtain gs where
  gs: "set gs \<subseteq> carrier G" "distinct gs"
      "DirProds (\<lambda>g. G\<lparr>carrier := generate G {g}\<rparr>) (set gs) \<cong> G"
      "successively (dvd) (map ord gs)" "card (set gs) \<le> card gen"
      "compl_fam (\<lambda>g. generate G {g}) (set gs)" "\<one> \<notin> set gs" by blast
  let ?gen = "(\<lambda>g. generate G {g})"
  let ?Hs = "map (\<lambda>g. ?gen g) gs"
  have "subgroup H G" if "H \<in> set ?Hs" for H using that gs by (auto intro: generate_is_subgroup)
  moreover have "distinct ?Hs"
    using compl_fam_imp_generate_inj[OF gs(1)] gs distinct_map by blast
  moreover have "DirProds (\<lambda>H. G\<lparr>carrier := H\<rparr>) (set ?Hs) \<cong> G"
  proof -
    have gg: "group (G\<lparr>carrier := ?gen g\<rparr>)" if "g \<in> set gs" for g
      by (use gs that in \<open>auto intro: subgroup.subgroup_is_group generate_is_subgroup\<close>)
    then interpret og: group "DirProds (\<lambda>g. G\<lparr>carrier := ?gen g\<rparr>) (set gs)"
      using DirProds_group_iff by blast
    have "DirProds (\<lambda>g. G\<lparr>carrier := ?gen g\<rparr>) (set gs) \<cong> DirProds (\<lambda>H. G\<lparr>carrier := H\<rparr>) (set ?Hs)"
    proof (intro DirProds_iso[of ?gen])
      show "bij_betw ?gen (set gs) (set ?Hs)"
        using \<open>distinct ?Hs\<close> gs(2) compl_fam_imp_generate_inj[OF gs(1, 6)]
        by (simp add: bij_betw_def)
      show "G\<lparr>carrier := ?gen g\<rparr> \<cong> G\<lparr>carrier := ?gen g\<rparr>" if "g \<in> set gs" for g by simp
      show "group (G\<lparr>carrier := ?gen g\<rparr>)" if "g \<in> set gs" for g using that by fact
      show "Group.group (G\<lparr>carrier := H\<rparr>)" if "H \<in> set ?Hs" for H
        by (use gs that in \<open>auto intro: subgroup.subgroup_is_group generate_is_subgroup\<close>)
    qed
    from group.iso_sym[OF og.is_group this] show ?thesis using gs iso_trans by blast
  qed
  moreover have "successively (dvd) (map card ?Hs)"
  proof -
    have "card (generate G {g}) = ord g" if "g \<in> set gs" for g
      using generate_pow_card that gs(1) by auto
    hence "map card ?Hs = map ord gs" by simp
    thus ?thesis using gs(4) by argo
  qed
  moreover have "card (set ?Hs) \<le> card gen" using gs
    by (metis \<open>distinct ?Hs\<close> distinct_card length_map)
  moreover have "compl_fam id (set ?Hs)"
    using compl_fam_cong[OF _ compl_fam_imp_generate_inj[OF gs(1, 6)], of id] using gs by auto
  moreover have "{\<one>} \<notin> set ?Hs" using generate_singleton_one gs by auto
  ultimately show ?thesis using that by blast
qed

text \<open>Here, the invariant factor decomposition in its classical form.\<close>

corollary (in fin_gen_comm_group) invariant_factor_decomposition_Zn:
  obtains ns where
    "DirProds (\<lambda>n. Z (ns!n)) {..<length ns} \<cong> G" "successively (dvd) ns" "length ns \<le> card gen"
proof -
  from invariant_factor_decomposition_dirprod obtain gs where
      gs: "set gs \<subseteq> carrier G" "distinct gs"
          "DirProds (\<lambda>g. G\<lparr>carrier := generate G {g}\<rparr>) (set gs) \<cong> G"
          "successively (dvd) (map ord gs)" "card (set gs) \<le> card gen"
          "compl_fam (\<lambda>g. generate G {g}) (set gs)" "\<one> \<notin> set gs" by blast
  let ?DP = "DirProds (\<lambda>g. G\<lparr>carrier := generate G {g}\<rparr>) (set gs)"
  have "\<exists>ns. DirProds (\<lambda>n. Z (ns!n)) {..<length ns} \<cong> G
           \<and> successively (dvd) ns \<and> length ns \<le> card gen"
  proof (cases gs, rule)
    case Nil
    from gs(3) Nil have co: "carrier ?DP = {\<one>\<^bsub>?DP\<^esub>}" unfolding DirProds_def by auto
    let ?ns = "[]"
    have "DirProds (\<lambda>n. Z ([] ! n)) {} \<cong> ?DP"
    proof(intro triv_iso DirProds_is_group)
      show "carrier (DirProds (\<lambda>n. Z ([] ! n)) {}) = {\<one>\<^bsub>DirProds (\<lambda>n. Z ([] ! n)) {}\<^esub>}"
        using DirProds_empty by blast
    qed (use co group_integer_mod_group Nil in auto)
    from that[of ?ns] gs co iso_trans[OF this gs(3)]
    show "DirProds (\<lambda>n. Z (?ns ! n)) {..<length ?ns} \<cong> G
        \<and> successively (dvd) ?ns \<and> length ?ns \<le> card gen"
      unfolding lessThan_def by simp
  next
    case c: (Cons a list)    
    let ?l = "map ord gs"
    from c have l: "length ?l > 0" by auto
    have "DirProds (\<lambda>n. Z (?l ! n)) {..<length ?l} \<cong> G"
    proof -
      have "DirProds (\<lambda>n. Z (?l ! n)) {..<length ?l} \<cong> ?DP"
      proof(intro DirProds_iso[where ?f = "\<lambda>n. gs!n"])
        show "bij_betw ((!) gs) {..<length ?l} (set gs)" using gs
          by (simp add: bij_betw_nth)
        show "Z (map ord gs ! i) \<cong> G\<lparr>carrier := generate G {gs ! i}\<rparr>" if "i \<in> {..<length ?l}" for i
        proof(rule group.iso_sym[OF subgroup.subgroup_is_group[OF generate_is_subgroup]
                   cyclic_group.Zn_iso[OF cyclic_groupI2]])
          show "order (G\<lparr>carrier := generate G {gs ! i}\<rparr>) = map ord gs ! i"
            unfolding order_def using that generate_pow_card[of "gs ! i"] gs(1) by force
        qed (use gs(1) that in auto)
        show "Group.group (Z (map ord gs ! i))" if "i \<in> {..<length (map ord gs)}" for i
          using group_integer_mod_group by blast
        show "Group.group (G\<lparr>carrier := generate G {g}\<rparr>)" if "g \<in> set gs" for g
          using that gs(1) subgroup.subgroup_is_group[OF generate_is_subgroup] by auto
      qed
      from iso_trans[OF this gs(3)] show ?thesis .
    qed
    moreover have "length ?l \<le> card gen" using gs by (metis distinct_card length_map)
    ultimately show ?thesis using gs c by fastforce
  qed
  thus ?thesis using that by blast
qed

text \<open>As every \<open>integer_mod_group\<close> can be decomposed into a product of prime power groups,
we obtain (by using the fact that the direct product does not care about nestedness)
the primary decomposition.\<close>

lemma Zn_iso_DirProds_prime_powers:
  assumes "n \<noteq> 0"
  shows "Z n \<cong> DirProds (\<lambda>p. Z (p ^ multiplicity p n)) (prime_factors n)" (is "Z n \<cong> ?DP")
proof (cases "n = 1")
  case True
  show ?thesis by (intro triv_iso[OF group_integer_mod_group DirProds_is_group],
                   use DirProds_empty carrier_integer_mod_group True in auto)
next
  case nno: False
  interpret DP: group ?DP by (intro DirProds_is_group, use group_integer_mod_group in blast)
  have "order ?DP = prod (order \<circ> (\<lambda>p. Z (p ^ multiplicity p n))) (prime_factors n)"
    by (intro DirProds_order, blast)
  also have "\<dots> = prod (\<lambda>p. p ^ multiplicity p n) (prime_factors n)" using Zn_order by simp
  also have n: "\<dots> = n" using prod_prime_factors[OF assms] by simp
  finally have oDP: "order ?DP = n" .
  then interpret DP: finite_group ?DP
    by (unfold_locales, unfold order_def, metis assms card.infinite)
  let ?f = "\<lambda>p\<in>(prime_factors n). 1"
  have fc: "?f \<in> carrier ?DP"
  proof -
    have p: "0 < multiplicity p n" if "p \<in> prime_factors n" for p
      using prime_factors_multiplicity that by auto
    have pk: "1 < p ^ k" if "Factorial_Ring.prime p" "0 < k" for p k::nat
      using that one_less_power prime_gt_1_nat by blast
    show ?thesis unfolding DirProds_def PiE_def
      by(use carrier_integer_mod_group assms nno pk p in auto,
         metis in_prime_factors_iff nat_int of_nat_power one_less_nat_eq)
  qed
  have of: "DP.ord ?f = n"
  proof -
    have "n dvd j" if j: "?f [^]\<^bsub>?DP\<^esub> j = \<one>\<^bsub>?DP\<^esub>" for j
    proof (intro pairwise_coprime_dvd'[OF _ _ n[symmetric]])
      show "finite (prime_factors n)" by simp
      show "\<forall>a\<in>#prime_factorization n. a ^ multiplicity a n dvd j"
      proof 
        show "p ^ multiplicity p n dvd j" if "p \<in> prime_factors n" for p
        proof -
          from j have "(?f [^]\<^bsub>?DP\<^esub> j) p = 0"
            using that unfolding DirProds_def one_integer_mod_group by auto
          hence "?f p [^]\<^bsub>Z (p ^ multiplicity p n)\<^esub> j = 0" using comp_exp_nat[OF that] by metis
          hence "group.ord (Z (p ^ multiplicity p n)) (?f p) dvd j" using comp_in_carr[OF fc that]
            by (metis group.pow_eq_id group_integer_mod_group one_integer_mod_group)
          moreover have "group.ord (Z (p ^ multiplicity p n)) (?f p) = p ^ multiplicity p n"
            by (metis (no_types, lifting) Zn_neq1_cyclic_group Zn_order comp_in_carr
                                          cyclic_group.ord_gen_is_group_order fc integer_mod_group_1
                                          restrict_apply' that)
          ultimately show ?thesis by simp
        qed
      qed
      show "coprime (i ^ multiplicity i n) (j ^ multiplicity j n)"
        if "i \<in># prime_factorization n" "j \<in># prime_factorization n" "i \<noteq> j" for i j
        using that diff_prime_power_imp_coprime by blast
    qed
    thus ?thesis using fc DP.ord_dvd_group_order gcd_nat.asym oDP by force
  qed
  interpret DP: cyclic_group ?DP ?f by (intro DP.element_ord_generates_cyclic, use of oDP fc in auto)
  show ?thesis using DP.iso_sym[OF DP.Zn_iso[OF oDP]] .
qed

lemma Zn_iso_DirProds_prime_powers':
  assumes "n \<noteq> 0"
  shows "Z n \<cong> DirProds (\<lambda>p. Z p) ((\<lambda>p. p ^ multiplicity p n) ` (prime_factors n))" (is "Z n \<cong> ?DP")
proof -
  have cp: "(\<lambda>p. Z (p ^ multiplicity p n)) = (\<lambda>p. Z p) \<circ> (\<lambda>p. p ^ multiplicity p n)" by auto
  have "DirProds (\<lambda>p. Z (p ^ multiplicity p n)) (prime_factors n) \<cong> ?DP"
  proof(subst cp, intro DirProds_iso2)
    show "inj_on (\<lambda>p. p ^ multiplicity p n) (prime_factors n)"
      by (intro inj_onI; simp add: prime_factors_multiplicity prime_power_inj'')
    show "group (DirProds Z ((\<lambda>p. p ^ multiplicity p n) ` prime_factors n))"
      by (intro DirProds_is_group, use group_integer_mod_group in auto)
  qed
  with Zn_iso_DirProds_prime_powers[OF assms] show ?thesis using Group.iso_trans by blast
qed

corollary (in fin_gen_comm_group) primary_decomposition_Zn:
  obtains ns where
    "DirProds (\<lambda>n. Z (ns!n)) {..<length ns} \<cong> G"
    "\<forall>n\<in>set ns. n = 0 \<or> (\<exists>p k. Factorial_Ring.prime p \<and> k > 0 \<and> n = p ^ k)"
proof -
  from invariant_factor_decomposition_Zn obtain ms where
    ms: "DirProds (\<lambda>m. Z (ms!m)) {..<length ms} \<cong> G" "successively (dvd) ms" "length ms \<le> card gen"
    by blast
  let ?I = "{..<length ms}"
  let ?J = "\<lambda>i. if ms!i = 0 then {0} else (\<lambda>p. p ^ multiplicity p (ms!i)) ` (prime_factors (ms!i))"
  let ?G = "\<lambda>i. Z"
  let ?f = "\<lambda>i. DirProds (?G i) (?J i)"
  have "DirProds (\<lambda>m. Z (ms!m)) {..<length ms} \<cong> DirProds ?f {..<length ms}"
  proof (intro DirProds_iso[of id])
    show "bij_betw id {..<length ms} {..<length ms}" by blast
    show "Z (ms ! i) \<cong> ?f (id i)" if "i \<in> {..<length ms}" for i
      by (cases "ms!i = 0",
          simp add: DirProds_one_cong_sym,
          auto intro: Zn_iso_DirProds_prime_powers')
    show "\<And>i. i \<in> {..<length ms} \<Longrightarrow> group (Z (ms ! i))" by auto
    show "group (?f j)" if "j \<in> {..<length ms}" for j by (auto intro: DirProds_is_group)
  qed
  also have "\<dots> \<cong> DirProds (\<lambda>(i,j). ?G i j) (Sigma ?I ?J)"
    by(rule DirProds_Sigma)
  finally have G1: "G \<cong> DirProds (\<lambda>(i,j). ?G i j) (Sigma ?I ?J)" using ms(1)
    by (metis (no_types, lifting) DirProds_is_group Group.iso_trans group.iso_sym group_integer_mod_group)
  have "\<exists>ps. set ps = Sigma ?I ?J \<and> distinct ps" by(intro finite_distinct_list, auto)
  then obtain ps where ps: "set ps = Sigma ?I ?J" "distinct ps" by blast
  define ns where ns: "ns = map snd ps"
  have "DirProds (\<lambda>n. Z (ns!n)) {..<length ns} \<cong> DirProds (\<lambda>(i,j). ?G i j) (Sigma ?I ?J)"
  proof -
    obtain b::"nat \<Rightarrow> (nat \<times> nat)"
      where b: "\<forall>i<length ns. ns!i = snd (b i)" "bij_betw b {..<length ns} (Sigma ?I ?J)"
      using ns ps bij_betw_nth by fastforce
    moreover have "Z (ns ! i) \<cong> (case b i of (i, x) \<Rightarrow> Z x)" if "i \<in> {..<length ns}" for i
    proof -
      have "ns ! i = snd (b i)" using b that by blast
      thus ?thesis by (simp add: case_prod_beta)
    qed
    ultimately show ?thesis by (auto intro: DirProds_iso)
  qed
  with G1 have "DirProds (\<lambda>n. Z (ns!n)) {..<length ns} \<cong> G" using Group.iso_trans iso_sym by blast
  moreover have "n = 0 \<or> (\<exists>p k. Factorial_Ring.prime p \<and> k > 0 \<and> n = p ^ k)" if "n\<in>set ns" for n
  proof -
    have "k = 0 \<or> (\<exists>p\<in>prime_factors (ms!i). k = p ^ multiplicity p (ms!i))" if "k \<in> ?J i" for k i
      by (cases "ms!i = 0", use that in auto)
    with that ns ps show ?thesis
      by (auto, metis (no_types, lifting) mem_Collect_eq neq0_conv prime_factors_multiplicity)
  qed
  ultimately show
  "(\<And>ns. \<lbrakk>DirProds (\<lambda>n. Z (ns ! n)) {..<length ns} \<cong> G;
          \<forall>n\<in>set ns. n = 0 \<or> (\<exists>p k. Factorial_Ring.prime p \<and> k > 0 \<and> n = p ^ k)\<rbrakk> \<Longrightarrow> thesis)
    \<Longrightarrow> thesis" by blast
qed

text \<open>As every finite group is also finitely generated, it follows that a finite group can be
decomposed in a product of finite cyclic groups.\<close>

lemma (in finite_comm_group) cyclic_product:
  obtains ns where "DirProds (\<lambda>n. Z (ns!n)) {..<length ns} \<cong> G" "\<forall>n\<in>set ns. n\<noteq>0"
proof -
  from primary_decomposition_Zn obtain ns where
    ns: "DirProds (\<lambda>n. Z (ns ! n)) {..<length ns} \<cong> G"
        "\<forall>n\<in>set ns. n = 0 \<or> (\<exists>p k. normalization_semidom_class.prime p \<and> 0 < k \<and> n = p ^ k)"
    by blast
  have "False" if "n \<in> {..<length ns}" "ns!n = 0" for n
  proof -
    from that have "order (DirProds (\<lambda>n. Z (ns ! n)) {..<length ns}) = 0"
      using DirProds_order[of "{..<length ns}" "\<lambda>n. Z (ns!n)"] Zn_order by auto
    with fin iso_same_card[OF ns(1)] show False unfolding order_def by auto
  qed
  hence "\<forall>n\<in>set ns. n\<noteq>0"
    by (metis in_set_conv_nth lessThan_iff)
  with ns show ?thesis using that by blast
qed

no_notation integer_mod_group ("Z")

end
