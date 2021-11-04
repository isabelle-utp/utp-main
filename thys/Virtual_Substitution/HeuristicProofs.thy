subsection "Heuristic Proofs"
theory HeuristicProofs
  imports VSQuad Heuristic OptimizationProofs
begin

lemma the_real_step_augment:
  assumes  steph : "\<And>xs var L F \<Gamma>. length xs = var \<Longrightarrow> (\<exists>x. eval (list_conj (map fm.Atom L @ F)) (xs @ x # \<Gamma>)) = (\<exists>x. eval (step var L F) (xs @ x # \<Gamma>))"
  shows "(\<exists>xs. (length xs = amount \<and> eval (list_disj (map(\<lambda>(L,F,n). ExN n (list_conj (map fm.Atom L @ F))) F))  (xs @ \<Gamma>))) = (eval (the_real_step_augment step amount F)  \<Gamma>)"
proof(induction amount arbitrary: F \<Gamma>)
  case 0
  then show ?case by auto
next
  case (Suc amount)
  have h1 : "\<And>F. (\<exists>x xs. length xs = amount \<and> F (xs @ x # \<Gamma>)) = (\<exists>xs. length xs = Suc amount \<and> F (xs @  \<Gamma>))"
    by (smt (z3) Suc_inject append.assoc append_Cons append_Nil2 append_eq_conv_conj length_append_singleton lessI self_append_conv2 take_hd_drop)

  have h2: "\<And>X x \<Gamma>. (\<exists>f\<in>set (dnf_modified X).
         eval (case f of (L, F, n) \<Rightarrow> ExN n (list_conj (map fm.Atom L @ F))) (x @ \<Gamma>)) = (\<exists>(al, fl, n)\<in>set (dnf_modified X). \<exists>L. length L = n \<and> (\<forall>a\<in>set al. aEval a (L @ (x @ \<Gamma>))) \<and> (\<forall>f\<in>set fl. eval f (L @ (x @ \<Gamma>))))"
    subgoal for X x \<Gamma>
      apply(rule bex_cong)
      apply simp_all
      subgoal for f
        apply(cases f)
        apply(auto simp add:eval_list_conj)
        by (metis Un_iff eval.simps(1) imageI)
      done
    done
  have h3 : "\<And>G. (\<exists>x. \<exists>f\<in>set F. G x f) = (\<exists>f\<in>set F. \<exists>x. G x f)"
    by blast
  show ?case
    apply simp
    unfolding Suc[symmetric]
    unfolding eval_list_disj
    apply simp
    unfolding h1[symmetric, of "\<lambda>x. (\<exists>f\<in>set F. eval (case f of (L, F, n) \<Rightarrow> ExN n (list_conj (map fm.Atom L @ F))) x)"]
    unfolding HOL.ex_comm[of "\<lambda>x xs. length xs = amount \<and> (\<exists>f\<in>set F. eval (case f of (L, F, n) \<Rightarrow> ExN n (list_conj (map fm.Atom L @ F))) (xs @ x # \<Gamma>))"]
    unfolding HOL.ex_comm[of "\<lambda>x xs. length xs = amount \<and>
        (\<exists>f\<in>set (dnf_modified (push_forall
                     (nnf (unpower 0
                            (groupQuantifiers
                              (clearQuantifiers(list_disj (map (\<lambda>(L, F, n). ExN n (step (n + amount) L F)) F)))))))).
            eval (case f of (L, F, n) \<Rightarrow> ExN n (list_conj (map fm.Atom L @ F))) (xs @ x # \<Gamma>))"]
    apply(rule ex_cong1)
    apply simp
    subgoal for xs
      unfolding h2
      unfolding dnf_modified_eval 
      unfolding opt'
      unfolding eval_list_disj
      unfolding List.set_map Set.bex_simps(7)
      unfolding h3
      apply(cases "length xs = amount")
      apply (simp_all add:opt)
      apply(rule bex_cong)
      apply simp_all
      subgoal for f
        apply(cases f)
        apply simp
        subgoal for a b c
          unfolding HOL.ex_comm[of "\<lambda>x l. length l = c \<and> eval (list_conj (map fm.Atom a @ b)) (l @ xs @ x # \<Gamma>)"]
          unfolding HOL.ex_comm[of "\<lambda>x l. length l = c \<and> eval (step (c + amount) a b) (l @ xs @ x # \<Gamma>)"]
          apply(rule ex_cong1)
          apply simp
          subgoal for l
            apply(cases "length l = c")
            apply simp_all
            using steph[of "l @ xs" "c + amount" a b \<Gamma>]
            by simp
          done
        done
      done
    done
qed

lemma step_converter : 
  assumes  steph : "\<And>xs var L F \<Gamma>. length xs = var \<Longrightarrow> (\<exists>x. eval (list_conj (map fm.Atom L @ F)) (xs @ x # \<Gamma>)) = (\<exists>x. eval (step var L F) (xs @ x # \<Gamma>))"
  shows "\<And>var L F \<Gamma>. (\<exists>xs. length xs = var + 1 \<and> eval (list_conj (map fm.Atom L @ F)) (xs @ \<Gamma>)) =
      (\<exists>xs. (length xs = (var + 1)) \<and> eval (step var L F) (xs @ \<Gamma>))"
proof safe
  fix var L F \<Gamma> xs
  assume h : "length xs = var + 1"
    "eval (list_conj (map fm.Atom L @ F)) (xs @ \<Gamma>)"
  have h1 : "length (take var xs) = var" using h by auto
  have h2 : "(\<exists>x. eval (step var L F) (take var xs @ x # \<Gamma>))"
    using h steph[OF h1]
    by (metis Cons_nth_drop_Suc One_nat_def add.right_neutral add_Suc_right append.assoc append_Cons append_Nil append_take_drop_id drop_all lessI order_refl) 
  then obtain x where h3: "eval (step var L F) (take var xs @ x # \<Gamma>)" by auto
  show "\<exists>xs. length xs = var + 1 \<and> eval (step var L F) (xs @ \<Gamma>)"
    apply(rule exI[where x="take var xs @[x]"])
    apply (auto)
    using h(1) apply simp
    using h3 by simp
next
  fix var L F \<Gamma> xs
  assume h: "length xs = var + 1"
    "eval (step var L F) (xs @ \<Gamma>)"
  have h1 : "length (take var xs) = var" using h by auto
  have h2 : "(\<exists>x. eval (list_conj (map fm.Atom L @ F)) (take var xs @ x # \<Gamma>))"
    using h steph[OF h1]
    by (metis Cons_nth_drop_Suc One_nat_def add.right_neutral add_Suc_right append.assoc append_Cons append_Nil append_take_drop_id drop_all lessI order_refl) 
  then obtain x where h3: "eval (list_conj (map fm.Atom L @ F)) (take var xs @ x # \<Gamma>)" by auto
  show "\<exists>xs. length xs = var + 1 \<and> eval (list_conj (map fm.Atom L @ F)) (xs @ \<Gamma>)"
    apply(rule exI[where x="take var xs @[x]"])
    apply (auto)
    using h(1) apply simp
    using h3 by simp
qed

lemma step_augmenter_eval : 
  assumes  steph : "\<And>xs var L F \<Gamma>. length xs = var \<Longrightarrow> (\<exists>x. eval (list_conj (map fm.Atom L @ F)) (xs @ x # \<Gamma>)) = (\<exists>x. eval (step var L F) (xs @ x # \<Gamma>))"
  assumes heuristic: "\<And>n var L F. heuristic n L F = var \<Longrightarrow> var \<le> n"
  shows "\<And>var amount L F \<Gamma>.
      amount \<le> var + 1 \<Longrightarrow>
      (\<exists>xs. length xs = var + 1 \<and> eval (list_conj (map fm.Atom L @ F)) (xs @ \<Gamma>)) =
      (\<exists>xs. (length xs = (var + 1)) \<and> eval (step_augment step heuristic amount var L F) (xs @ \<Gamma>))"
  subgoal for var amount L F \<Gamma>
  proof(induction var arbitrary: L F \<Gamma> amount)
    case 0
    then have "amount = 0 \<or> amount = Suc 0" by auto
    then show ?case apply simp using steph[of "[]" 0 L F \<Gamma>] apply auto
      apply (metis append_Cons length_Cons list.size(3) self_append_conv2)
      apply (metis append_Cons length_Cons list.size(3) self_append_conv2)
      apply (metis Suc_length_conv append_Cons length_0_conv self_append_conv2)
      by (metis Suc_length_conv append_Cons append_self_conv2 length_0_conv)
  next
    case (Suc var)
    define heu where "heu = heuristic (Suc var) L F"
    have heurange : "heu \<le> Suc var" unfolding heu_def
      by (simp add: heuristic)
    have lessThan1 : "1 \<le> var + 1" by auto 

    {
      fix amount
      assume amountLessThan: "amount \<le> var + 1"
      have "(\<exists>xs. length xs = Suc (Suc var) \<and>
          eval (list_conj (map fm.Atom L @ F)) (xs @ \<Gamma>)) = (\<exists>xs. length xs = Suc (Suc var) \<and>
          eval
           (step (Suc var) (map (swap_atom (Suc var) heu) L)
             (map (swap_fm (Suc var) heu) F))
           (xs @ \<Gamma>))"
      proof(safe)
        fix xs
        assume h: "length (xs::real list) = Suc (Suc var)" "eval (list_conj (map fm.Atom L @ F)) (xs @ \<Gamma>)"
        then have length : "length (take (Suc var) (swap_list (Suc var) heu xs)) = Suc var" by auto
        have take: "(take (Suc var) (swap_list (Suc var) heu xs) @ xs ! heu # \<Gamma>) = (swap_list (Suc var) heu (xs @ \<Gamma>)) " using h(1)
          unfolding swap_list.simps 
          by (smt (verit, ccfv_threshold) Cons_nth_drop_Suc append.right_neutral append_Nil2 append_assoc append_eq_conv_conj append_self_conv2 append_take_drop_id drop0 heu_def heurange le_imp_less_Suc length_greater_0_conv length_list_update lessI list.sel(1) list.sel(3) list.simps(3) list.size(3) list_update_append nth_Cons_0 nth_append nth_append_length nth_list_update_eq take0 take_hd_drop)
        have length1 : "Suc var < length (xs @ \<Gamma>)" using h by auto
        have length2 : "heu < length (xs @ \<Gamma>)" using h heurange by auto
        have h1: "(\<exists>x. eval
        (step (Suc var) (map (swap_atom (Suc var) heu) L)
          (map (swap_fm (Suc var) heu) F))
        (take (Suc var) (swap_list (Suc var) heu xs) @ x # \<Gamma>))"
          unfolding steph[OF length, symmetric]
          apply(rule exI[where x="nth xs heu"])
          using h unfolding eval_list_conj take apply (auto simp del:swap_list.simps)
          unfolding swap_fm[OF length1 length2,symmetric] swap_atom[OF length1 length2,symmetric]
          by (meson UnCI eval.simps(1) imageI)+
        then obtain x where heval: "eval
       (step (Suc var) (map (swap_atom (Suc var) heu) L)
         (map (swap_fm (Suc var) heu) F))
       (take (Suc var) (swap_list (Suc var) heu xs) @ x # \<Gamma>)" by auto
        show "\<exists>xs. length xs = Suc (Suc var) \<and>
               eval
                (step (Suc var) (map (swap_atom (Suc var) heu) L)
                  (map (swap_fm (Suc var) heu) F))
                (xs @ \<Gamma>)"
          apply(rule exI[where x="take (Suc var) (swap_list (Suc var) heu xs) @ [x]"])
          apply auto
          using h apply simp
          using heval by auto
      next
        fix xs
        assume h : "length xs = Suc (Suc var)""
          eval
           (step (Suc var) (map (swap_atom (Suc var) heu) L)
             (map (swap_fm (Suc var) heu) F))
           (xs @ \<Gamma>)"
        define choppedXS where "choppedXS = take (Suc var) xs"
        then have length : "length choppedXS = Suc var"
          using h(1) by force
        have "(\<exists>x. eval (step (Suc var) (map (swap_atom (Suc var) heu) L) (map (swap_fm (Suc var) heu) F)) (choppedXS @ x # \<Gamma>))"
          using h(2) choppedXS_def
          by (metis append.assoc append_Cons append_Nil2 append_eq_conv_conj h(1) lessI take_hd_drop) 
        then have "\<exists>x. (\<forall>l\<in> set L. aEval (swap_atom (Suc var) heu l) (choppedXS@x#\<Gamma>)) \<and> (\<forall>f\<in> set F. eval (swap_fm (Suc var) heu f) (choppedXS@x#\<Gamma>))"
          unfolding steph[symmetric, OF length, of "(map (swap_atom (Suc var) heu) L)" "(map (swap_fm (Suc var) heu) F)" \<Gamma>] eval_list_conj apply auto
          by (metis Un_iff eval.simps(1) imageI)
        then obtain x where x : "(\<forall>l\<in>set L. aEval (swap_atom (Suc var) heu l) (choppedXS @ x # \<Gamma>)) \<and>
      (\<forall>f\<in>set F. eval (swap_fm (Suc var) heu f) (choppedXS @ x # \<Gamma>))" by auto
        have length1 : "Suc var < length (swap_list (Suc var) heu (choppedXS @ [x]) @ \<Gamma>)"
          by (simp add: length)
        have length2 : "heu < length (swap_list (Suc var) heu (choppedXS @ [x]) @ \<Gamma>)"
          using \<open>Suc var < length (swap_list (Suc var) heu (choppedXS @ [x]) @ \<Gamma>)\<close> heurange by linarith
        have swapswap : "(swap_list (Suc var) heu (swap_list (Suc var) heu (choppedXS @ [x]) @ \<Gamma>)) = (choppedXS @ [x]) @ \<Gamma>" apply auto
          by (smt (z3) Cons_nth_drop_Suc append_eq_conv_conj append_same_eq heurange id_take_nth_drop le_neq_implies_less length length1 length_append_singleton lessI list.sel(1) list_update_append1 list_update_length list_update_swap nth_append nth_append_length nth_list_update_neq swap_list.simps take_hd_drop take_update_swap upd_conv_take_nth_drop)
        show "\<exists>xs. length xs = Suc (Suc var) \<and>
               eval (list_conj (map fm.Atom L @ F)) (xs @ \<Gamma>)"
          apply(rule exI[where x="swap_list (Suc var) heu (choppedXS @ [x])"])
          apply(auto simp add: eval_list_conj simp del: swap_list.simps)
          apply(simp add :length)
          unfolding swap_atom[OF length1 length2] swap_fm[OF length1 length2] swapswap
          using x by auto
      qed
      also have "... = (\<exists>xs. length xs = Suc (Suc var) \<and>
          (\<exists>f\<in>set (dnf ((push_forall \<circ> nnf \<circ> unpower 0 o groupQuantifiers o clearQuantifiers)(step (Suc var) (map (swap_atom (Suc var) heu) L)
                          (map (swap_fm (Suc var) heu) F)))).
              eval (case f of (x, xa) \<Rightarrow> step_augment step heuristic amount var x xa)
               (xs @ \<Gamma>)))"
        unfolding opt[of "(step (Suc var) (map (swap_atom (Suc var) heu) L) (map (swap_fm (Suc var) heu) F))", symmetric]
        unfolding dnf_eval[of "(push_forall \<circ> nnf \<circ> unpower 0 o groupQuantifiers o clearQuantifiers)(step (Suc var) (map (swap_atom (Suc var) heu) L)
             (map (swap_fm (Suc var) heu) F))", symmetric]
      proof(safe)
        fix xs a b
        assume h: "length xs = Suc (Suc var)""
       (a, b)
       \<in> set (dnf ((push_forall \<circ> nnf \<circ> unpower 0 o groupQuantifiers o clearQuantifiers)(step (Suc var) (map (swap_atom (Suc var) heu) L)
                     (map (swap_fm (Suc var) heu) F)))) ""
       \<forall>a\<in>set a. aEval a (xs @ \<Gamma>) ""
       \<forall>f\<in>set b. eval f (xs @ \<Gamma>)"
        have "(\<exists>xs'. length xs' = var + 1 \<and>
        eval (step_augment step heuristic amount var a b) (xs' @ xs ! Suc var # \<Gamma>))"
          unfolding Suc(1)[of amount a b "nth xs (Suc var)#\<Gamma>", OF amountLessThan, symmetric]
          apply(rule exI[where x="take (Suc var) xs"])
          using h(1) h(3-4) apply(auto simp add: eval_list_conj)
          apply (metis Cons_nth_drop_Suc append_Cons append_eq_append_conv2 append_eq_conv_conj append_take_drop_id lessI)
          by (metis Cons_nth_drop_Suc append_Cons append_eq_append_conv2 append_eq_conv_conj append_take_drop_id lessI)
        then obtain xs' where xs': "length xs' = var + 1" "eval (step_augment step heuristic amount var a b) (xs' @ xs ! Suc var # \<Gamma>)"
          by auto

        show "\<exists>xs. length xs = Suc (Suc var) \<and>
            (\<exists>f\<in>set (dnf ((push_forall \<circ> nnf \<circ> unpower 0 o groupQuantifiers o clearQuantifiers)(step (Suc var) (map (swap_atom (Suc var) heu) L)
                            (map (swap_fm (Suc var) heu) F)))).
                eval (case f of (x, xa) \<Rightarrow> step_augment step heuristic amount var x xa)
                 (xs @ \<Gamma>))"
          apply(rule exI[where x="xs' @[ xs ! Suc var]"])
          apply auto
          using xs' apply simp
          apply(rule bexI[where x="(a,b)"])
          using xs' h apply(cases amount) apply (simp_all add:eval_list_conj)
          using h(2) by auto
      next
        fix xs a b
        assume h: "length xs = Suc (Suc var) ""
       (a, b)
       \<in> set (dnf ((push_forall \<circ> nnf \<circ> unpower 0 o groupQuantifiers o clearQuantifiers)(step (Suc var) (map (swap_atom (Suc var) heu) L)
                     (map (swap_fm (Suc var) heu) F)))) ""
       eval (step_augment step heuristic amount var a b) (xs @ \<Gamma>)"
        have "(\<exists>xs'. length xs' = var + 1 \<and>
        eval (list_conj (map fm.Atom a @ b)) (xs' @ xs ! Suc var # \<Gamma>))"
          unfolding Suc(1)[of amount a b "nth xs (Suc var)#\<Gamma>", OF amountLessThan]
          apply(rule exI[where x="take (Suc var) xs"])
          using h(1) h(3) apply auto
          by (metis Cons_nth_drop_Suc append.right_neutral append_Cons append_assoc append_eq_conv_conj append_self_conv2 append_take_drop_id lessI)
        then obtain xs' where xs': "length xs' = var + 1" " eval (list_conj (map fm.Atom a @ b)) (xs' @ xs ! Suc var # \<Gamma>)"
          by auto
        show "\<exists>xs. length xs = Suc (Suc var) \<and>
            (\<exists>(al, fl)
              \<in>set (dnf ((push_forall \<circ> nnf \<circ> unpower 0 o groupQuantifiers o clearQuantifiers)(step (Suc var) (map (swap_atom (Suc var) heu) L)
                           (map (swap_fm (Suc var) heu) F)))).
                (\<forall>a\<in>set al. aEval a (xs @ \<Gamma>)) \<and>
                (\<forall>f\<in>set fl. eval f (xs @ \<Gamma>)))"
          apply(rule exI[where x="xs' @[ xs ! Suc var]"])
          apply auto
          using xs' apply simp
          apply(rule bexI[where x="(a,b)"])
          using xs' h apply (simp_all add: eval_list_conj)
        proof -
          assume "\<forall>f\<in>fm.Atom ` set a \<union> set b. eval f (xs' @ xs ! Suc var # \<Gamma>)"
          then have "\<forall>f. f \<in> fm.Atom ` set a \<union> set b \<longrightarrow> eval f (xs' @ xs ! Suc var # \<Gamma>)"
            by meson
          then have f1: "v \<notin> set a \<or> eval (fm.Atom v) (xs' @ xs ! Suc var # \<Gamma>)" for v
            by blast
          obtain aa :: atom where
            "(\<exists>v0. v0 \<in> set a \<and> \<not> eval (fm.Atom v0) (xs' @ xs ! Suc var # \<Gamma>)) = (aa \<in> set a \<and> \<not> eval (fm.Atom aa) (xs' @ xs ! Suc var # \<Gamma>))"
            by blast
          then show "\<forall>a\<in>set a. aEval a (xs' @ xs ! Suc var # \<Gamma>)"
            using f1 eval.simps(1) by auto
        qed

      qed
      finally have "(\<exists>xs. length xs = Suc (Suc var) \<and> eval (list_conj (map fm.Atom L @ F)) (xs @ \<Gamma>)) =
  (\<exists>xs. length xs = Suc (Suc var) \<and>
        (\<exists>f\<in>set (dnf ((push_forall \<circ> nnf \<circ> unpower 0 o groupQuantifiers o clearQuantifiers) (step (Suc var) (map (swap_atom (Suc var) heu) L) (map (swap_fm (Suc var) heu) F)))).
            eval (case f of (x, xa) \<Rightarrow> step_augment step heuristic amount var x xa) (xs @ \<Gamma>)))"
        by auto 
    }then show ?case apply(cases amount) using Suc(2)  by (simp_all add:eval_list_disj heu_def[symmetric])
  qed
  done

lemma qe_eq_repeat_eval_augment : "amount \<le> var+1 \<Longrightarrow>
      (\<exists>xs. (length xs = var + 1) \<and> eval (list_conj (map fm.Atom L @ F)) (xs @ \<Gamma>)) =
      (\<exists>xs. (length xs = var + 1) \<and> eval (step_augment qe_eq_repeat IdentityHeuristic amount var L F) (xs @ \<Gamma>))"
  apply(rule step_augmenter_eval[of qe_eq_repeat IdentityHeuristic amount var L F \<Gamma>])
  using qe_eq_repeat_eval apply blast by auto

lemma qe_eq_repeat_eval' : "
      (\<exists>xs. (length xs = var + 1) \<and> eval (list_conj (map fm.Atom L @ F)) (xs @ \<Gamma>)) =
      (\<exists>xs. (length xs = var + 1) \<and> eval (qe_eq_repeat var L F) (xs @ \<Gamma>))"
  apply(rule step_converter[of qe_eq_repeat var L F \<Gamma>])
  using qe_eq_repeat_eval by blast

lemma gen_qe_eval_augment : "amount \<le> var+1 \<Longrightarrow>
      (\<exists>xs. (length xs = var + 1) \<and> eval (list_conj (map fm.Atom L @ F)) (xs @ \<Gamma>)) =
      (\<exists>xs. (length xs = var + 1) \<and> eval (step_augment gen_qe IdentityHeuristic amount var L F) (xs @ \<Gamma>))"
  apply(rule step_augmenter_eval[of gen_qe IdentityHeuristic amount var L F \<Gamma>])
  using gen_qe_eval apply blast by auto

lemma gen_qe_eval' : "
      (\<exists>xs. (length xs = var + 1) \<and> eval (list_conj (map fm.Atom L @ F)) (xs @ \<Gamma>)) =
      (\<exists>xs. (length xs = var + 1) \<and> eval (gen_qe var L F) (xs @ \<Gamma>))"
  apply(rule step_converter[of gen_qe var L F \<Gamma>])
  using gen_qe_eval by blast

lemma luckyFind_eval_augment : "amount \<le> var+1 \<Longrightarrow>
      (\<exists>xs. (length xs = var + 1) \<and> eval (list_conj (map fm.Atom L @ F)) (xs @ \<Gamma>)) =
      (\<exists>xs. (length xs = var + 1) \<and> eval (step_augment luckyFind' IdentityHeuristic amount var L F) (xs @ \<Gamma>))"
  apply(rule step_augmenter_eval[of luckyFind' IdentityHeuristic amount var L F \<Gamma>])
  using luckyFind'_eval apply blast by auto

lemma luckyFind_eval' : "
      (\<exists>xs. (length xs = var + 1) \<and> eval (list_conj (map fm.Atom L @ F)) (xs @ \<Gamma>)) =
      (\<exists>xs. (length xs = var + 1) \<and> eval (luckyFind' var L F) (xs @ \<Gamma>))"
  apply(rule step_converter[of luckyFind' var L F \<Gamma>])
  using luckyFind'_eval by blast

lemma luckiestFind_eval' : "
      (\<exists>xs. (length xs = var + 1) \<and> eval (list_conj (map fm.Atom L @ F)) (xs @ \<Gamma>)) =
      (\<exists>xs. (length xs = var + 1) \<and> eval (luckiestFind var L F) (xs @ \<Gamma>))"
  apply(rule step_converter[of luckiestFind var L F \<Gamma>])
  using luckiestFind_eval by blast


lemma sortedListMember : "sorted_list_of_fset b = var # list \<Longrightarrow> fmember var b "
  by (metis fset_of_list_elem list.set_intros(1) sorted_list_of_fset_simps(2))

lemma rangeHeuristic : 
  assumes "heuristicPicker n L F = Some (var, step)"
  shows "var\<le>n"
proof(cases "aquireData n L")
  case (fields a b c)
  then show ?thesis using assms apply(simp_all del: aquireData.simps getBest.simps)
    apply(cases "getBest a L")
    apply(simp_all del: aquireData.simps getBest.simps)
    apply(cases F) apply(simp_all del: aquireData.simps getBest.simps)
    apply(cases "getBest c L") apply(simp_all del: aquireData.simps getBest.simps)
    apply(cases "getBest b L")apply(simp_all del: aquireData.simps getBest.simps)
    apply (metis not_le_imp_less option.distinct(1) option.inject prod.inject)
    apply (metis not_le_imp_less option.distinct(1) option.inject prod.inject)
    apply(cases "getBest b L")apply(simp_all del: aquireData.simps getBest.simps)
    by (metis not_le_imp_less option.distinct(1) option.inject prod.inject)+
qed

lemma pickedOneOfThem : 
  assumes "heuristicPicker n L F = Some (var, step)"
  shows "step = qe_eq_repeat \<or> step = gen_qe \<or> step = luckyFind'"
  using assms
  apply(cases "aquireData n L")
  subgoal for l e g
    using assms apply(simp_all del: aquireData.simps getBest.simps)
    apply(cases "getBest l L")
    apply(simp_all del: aquireData.simps getBest.simps)
    apply(cases F) apply(simp_all del: aquireData.simps getBest.simps)
    apply(cases "getBest g L") apply(simp_all del: aquireData.simps getBest.simps)
    apply(cases "getBest e L")apply(simp_all del: aquireData.simps getBest.simps)
    apply (metis option.distinct(1) option.inject prod.inject)
    apply (metis option.distinct(1) option.inject prod.inject)
    apply(cases "getBest e L")apply(simp_all del: aquireData.simps getBest.simps)
    by (metis  option.distinct(1) option.inject prod.inject)+
  done

lemma superPicker_eval : 
  "amount\<le> var+1 \<Longrightarrow> (\<exists>xs. length xs = var + 1 \<and> eval (list_conj (map fm.Atom L @ F)) (xs @ \<Gamma>)) =
      (\<exists>xs. (length xs = (var + 1)) \<and> eval (superPicker amount var L F) (xs @ \<Gamma>))"
proof(induction var arbitrary : L F \<Gamma> amount)
  case 0
  then show ?case apply(simp del:heuristicPicker.simps)
    apply(cases "heuristicPicker 0 L F") apply(cases amount)
    apply (simp_all del:heuristicPicker.simps)
    subgoal for a
      apply(cases a)
      apply (simp_all del:heuristicPicker.simps)
      subgoal for var step
        apply(cases var) apply(cases amount)
        apply(simp_all del:heuristicPicker.simps) 
      proof-
        assume h: "heuristicPicker 0 L F = Some (0, step)"
        show "(\<exists>xs. length xs = Suc 0 \<and> eval (list_conj (map fm.Atom L @ F)) (xs @ \<Gamma>)) =
    (\<exists>xs. length xs = Suc 0 \<and> eval (step 0 L F) (xs @ \<Gamma>)) "
          using pickedOneOfThem[OF h]
          using  qe_eq_repeat_eval'[of 0 L F \<Gamma>] gen_qe_eval'[of 0 L F \<Gamma>] luckyFind_eval'[of 0 L F \<Gamma>]
          by auto
      next
        show "\<And>nat. amount \<le> Suc 0 \<Longrightarrow>
           heuristicPicker 0 L F = Some (Suc nat, step) \<Longrightarrow>
           a = (Suc nat, step) \<Longrightarrow>
           var = Suc nat \<Longrightarrow>
           (\<exists>xs. length xs = Suc 0 \<and> eval (list_conj (map fm.Atom L @ F)) (xs @ \<Gamma>)) =
           (\<exists>xs. length xs = Suc 0 \<and> eval (superPicker amount 0 L F) (xs @ \<Gamma>)) "
          apply(cases amount) by(simp_all del:heuristicPicker.simps) 
      qed
      done
    done
next
  case (Suc i)
  then show ?case apply(cases "heuristicPicker (Suc i) L F") apply(cases amount)
    apply(simp_all del:heuristicPicker.simps)
    subgoal for a
      apply(cases a)
      apply(simp_all del:heuristicPicker.simps) apply(cases amount) apply simp
      apply(cases amount) apply(simp_all del:heuristicPicker.simps)
      subgoal for var step amountPred amountPred' 
      proof-
        assume amountPred : "amountPred \<le> Suc i"
        assume ih: "(\<And>amount L F \<Gamma>.
        amount \<le> Suc i \<Longrightarrow>
        (\<exists>xs. length xs = Suc i \<and> eval (list_conj (map fm.Atom L @ F)) (xs @ \<Gamma>)) =
        (\<exists>xs. length xs = Suc i \<and> eval (superPicker amount i L F) (xs @ \<Gamma>)))"
        assume h0 : "heuristicPicker (Suc i) L F = Some (var, step)"
        have h1: "\<And>xs X F. (\<exists>f\<in>set (map (\<lambda>(x, y). F x y)
                     (dnf X)).
              eval f (xs)) = (\<exists>(al,fl)\<in>set(dnf X).
              eval (F al fl) (xs))"
          subgoal for xs X F
            apply auto
            subgoal for a b
              apply(rule bexI[where x="(a,b)"])
              apply simp_all
              done
            done
          done
        have eval_map : "\<And>al fl xs \<Gamma>.(\<forall>f\<in>set (map fm.Atom al @ fl). eval f (xs @ \<Gamma>)) = ((\<forall>a\<in>set al. aEval a (xs @ \<Gamma>)) \<and> (\<forall>f\<in>set fl. eval f (xs @ \<Gamma>)))"
          apply auto
          by (meson Un_iff eval.simps(1) imageI)
        have rearangeExists :  "\<And> X F.((\<exists>xs. length xs = Suc (Suc i) \<and>
               (\<exists>(al, fl)\<in>set (dnf X). F al fl xs)) =
            (\<exists>(al,fl)\<in>set (dnf X).(\<exists>xs. length xs = Suc (Suc i) \<and>
                F al fl xs)))"
          by blast
        have dropTheEnd : "\<And>F \<Gamma>.(\<exists>xs. length xs = Suc (Suc i) \<and> F (xs @ \<Gamma>)) = (\<exists>x. (\<exists>xs. length xs = i+1 \<and> F (xs @ x#\<Gamma>)))"
          apply(safe)
          subgoal for F \<Gamma> xs
            apply(rule exI[where x="nth xs (i+1)"])
            apply(rule exI[where x="take (i+1) xs"]) apply auto
            by (metis Cons_nth_drop_Suc append.right_neutral append_Cons append_assoc append_eq_conv_conj append_self_conv2 append_take_drop_id lessI)
          subgoal for F \<Gamma> x xs
            apply(rule exI[where x="xs@[x]"])
            by auto
          done
        have h2 : "\<And>X \<Gamma> amount. amount\<le> Suc i \<Longrightarrow>((\<exists>xs. length xs = Suc (Suc i) \<and>
          (\<exists>(al, fl)\<in>set (dnf X).
              eval (superPicker amount i al fl) (xs @ \<Gamma>)))
          = (\<exists>xs. length xs = Suc (Suc i) \<and>
          (\<exists>(al, fl)\<in>set (dnf X).
              (\<forall>a\<in>set al. aEval a (xs@\<Gamma>))\<and>(\<forall>f\<in>set fl. eval f (xs@\<Gamma>)))))"
          subgoal for X \<Gamma> amount
            unfolding rearangeExists
            apply(rule bex_cong)
            apply simp
            subgoal for x
              apply (cases x)
              apply simp
              subgoal for al fl
                unfolding dropTheEnd 
                unfolding dropTheEnd[of"\<lambda>xs. (\<forall>a\<in>set al. aEval a xs) \<and> (\<forall>f\<in>set fl. eval f xs)"]
                apply simp
                unfolding ih[of amount al fl "_#\<Gamma>",symmetric]
                unfolding eval_list_conj
                apply(rule ex_cong1)
                subgoal for xa
                  apply(rule ex_cong1)
                  subgoal for xab apply auto
                    by (meson Un_iff eval.simps(1) image_eqI)
                  done
                done
              done
            done
          done
        have h3 : "\<And>L F. (\<exists>xs. length xs = Suc (Suc i) \<and> eval (step (Suc i) L F) (xs@\<Gamma>)) = (\<exists>xs. length xs = Suc (Suc i) \<and> eval (list_conj (map fm.Atom L @ F)) (xs @ \<Gamma>))"
          subgoal for L F
            using pickedOneOfThem[OF h0]
            using  qe_eq_repeat_eval'[of "Suc i" L F \<Gamma>] gen_qe_eval'[of "Suc i" L F \<Gamma>] luckyFind_eval'[of "Suc i" L F \<Gamma>]
            by auto
          done
        have heurange : "var\<le> Suc i" using rangeHeuristic[OF h0] by auto
        show ?thesis
          unfolding eval_list_disj
          unfolding h1
          unfolding h2[OF amountPred]
          unfolding dnf_eval 
          unfolding opt'
          unfolding h3 
        proof(safe)
          fix xs
          assume h : "length xs = Suc (Suc i)" "eval (list_conj (map fm.Atom L @ F)) (xs @ \<Gamma>)"
          have h3 : "var < length (xs @ \<Gamma>)"  using h heurange by auto
          have h1: "(swap_list (Suc i) var (xs @ \<Gamma>)) = (swap_list (Suc i) var xs @ \<Gamma>)"
            using h(1) heurange apply simp
            by (simp add: list_update_append nth_append)
          have h2 : "Suc i < length (xs @ \<Gamma>)" using h by auto

          show "\<exists>xs. length xs = Suc (Suc i) \<and>
               eval (list_conj (map fm.Atom (map (swap_atom (Suc i) var) L) @ map (swap_fm (Suc i) var) F)) (xs @ \<Gamma>)"
            apply(rule exI[where x="swap_list (Suc i) var xs"])
            apply(auto simp add:h eval_list_conj simp del:swap_list.simps)
            apply(simp add: h)
            using swap_fm[OF h2 h3] swap_atom[OF h2 h3] unfolding h1
            using h(2) unfolding eval_list_conj
            apply auto

            by (meson Un_iff eval.simps(1) imageI)
        next
          fix xs
          assume h : "length xs = Suc (Suc i)""eval (list_conj (map fm.Atom (map (swap_atom (Suc i) var) L) @ map (swap_fm (Suc i) var) F)) (xs @ \<Gamma>)"
          have h3 : "var < length (swap_list (Suc i) var xs @ \<Gamma>)"  using h heurange by auto
          have h1: "swap_list (Suc i) var (swap_list (Suc i) var xs @ \<Gamma>) = xs @ \<Gamma>"
            apply auto
            using h(1) heurange
            by (smt (z3) le_imp_less_Suc length_list_update lessI list_update_append list_update_id list_update_overwrite list_update_swap nth_append nth_list_update_eq)
          have h2 : "Suc i < length (swap_list (Suc i) var xs @ \<Gamma>)" using h by auto
          show "\<exists>xs. length xs = Suc (Suc i) \<and> eval (list_conj (map fm.Atom L @ F)) (xs @ \<Gamma>)"
            apply(rule exI[where x="swap_list (Suc i) var xs"])
            apply(auto simp add:eval_list_conj simp del:swap_list.simps)
            apply(simp add: h)
            unfolding swap_fm[OF h2 h3] swap_atom[OF h2 h3]
            unfolding h1
            using h(2) unfolding eval_list_conj
            apply auto
            apply (meson Un_iff eval.simps(1) imageI)
            done
        qed
      qed
      done
    done
qed 


lemma brownHueristic_less_than: "brownsHeuristic n L F = var \<Longrightarrow> var\<le> n"
  apply simp
  apply(cases "sorted_list_of_fset
           ((\<lambda>x. case foldl
                        (\<lambda>(maxdeg, totaldeg, appearancecount) l.
                            let deg = MPoly_Type.degree (case l of Less p \<Rightarrow> p | Eq p \<Rightarrow> p | Leq p \<Rightarrow> p | Neq p \<Rightarrow> p) x
                            in (max maxdeg deg, totaldeg + deg, appearancecount + (if 0 < deg then 1 else 0)))
                        (0, 0, 0) L of
                  (a, b, c) \<Rightarrow> Quad (a, b, c, x)) |`|
            fset_of_list [0..<n])")
  apply auto
  subgoal for a apply(cases a)
    by auto
  done
end
