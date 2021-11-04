theory Observe_Failure imports
  More_CC
begin

declare [[show_variants]]

context fixes "oracle" :: "('s, 'in, 'out) oracle'" begin

fun obsf_oracle :: "('s exception, 'in, 'out exception) oracle'" where 
  "obsf_oracle Fault x = return_spmf (Fault, Fault)"
| "obsf_oracle (OK s) x = TRY map_spmf (map_prod OK OK) (oracle s x) ELSE return_spmf (Fault, Fault)"

end

type_synonym ('a, 'b) resource_obsf = "('a, 'b exception) resource"

translations
  (type) "('a, 'b) resource_obsf" <= (type) "('a, 'b exception) resource"

primcorec obsf_resource :: "('in, 'out) resource \<Rightarrow> ('in, 'out) resource_obsf" where
  "run_resource (obsf_resource res) = (\<lambda>x.
   map_spmf (map_prod id obsf_resource) 
     (map_spmf (map_prod id (\<lambda>resF. case resF of OK res' \<Rightarrow> res' | Fault \<Rightarrow> fail_resource))
       (TRY map_spmf (map_prod OK OK) (run_resource res x) ELSE return_spmf (Fault, Fault))))"

lemma obsf_resource_sel:
  "run_resource (obsf_resource res) x = 
   map_spmf (map_prod id (\<lambda>resF. obsf_resource (case resF of OK res' \<Rightarrow> res' | Fault \<Rightarrow> fail_resource))) 
    (TRY map_spmf (map_prod OK OK) (run_resource res x) ELSE return_spmf (Fault, Fault))"
  by(simp add: spmf.map_comp prod.map_comp o_def id_def)

declare obsf_resource.simps [simp del]

lemma obsf_resource_exception [simp]: "obsf_resource fail_resource = const_resource Fault"
  by coinduction(simp add: rel_fun_def obsf_resource_sel)

lemma obsf_resource_sel2 [simp]:
  "run_resource (obsf_resource res) x = 
   try_spmf (map_spmf (map_prod OK obsf_resource) (run_resource res x)) (return_spmf (Fault, const_resource Fault))"
  by(simp add: map_try_spmf spmf.map_comp o_def prod.map_comp obsf_resource_sel)

lemma lossless_obsf_resource [simp]: "lossless_resource \<I> (obsf_resource res)"
  by(coinduction arbitrary: res) auto

lemma WT_obsf_resource [WT_intro, simp]: "exception_\<I> \<I> \<turnstile>res obsf_resource res \<surd>" if "\<I> \<turnstile>res res \<surd>"
  using that by(coinduction arbitrary: res)(auto dest: WT_resourceD split: if_split_asm)


type_synonym ('a, 'b) distinguisher_obsf = "(bool, 'a, 'b exception) gpv"

translations
  (type) "('a, 'b) distinguisher_obsf" <= (type) "(bool, 'a, 'b exception) gpv"

abbreviation connect_obsf :: "('a, 'b) distinguisher_obsf \<Rightarrow> ('a, 'b) resource_obsf \<Rightarrow> bool spmf" where
  "connect_obsf == connect"

definition obsf_distinguisher :: "('a, 'b) distinguisher \<Rightarrow> ('a, 'b) distinguisher_obsf" where
  "obsf_distinguisher \<D> = map_gpv' (\<lambda>x. x = Some True) id option_of_exception (gpv_stop \<D>)"
                                      
lemma WT_obsf_distinguisher [WT_intro]:
  "exception_\<I> \<I> \<turnstile>g obsf_distinguisher \<A> \<surd>" if [WT_intro]: "\<I> \<turnstile>g \<A> \<surd>"
  unfolding obsf_distinguisher_def by(rule WT_intro|simp)+

lemma interaction_bounded_by_obsf_distinguisher [interaction_bound]:
  "interaction_bounded_by consider (obsf_distinguisher \<A>) bound"
  if [interaction_bound]: "interaction_bounded_by consider \<A> bound"
  unfolding obsf_distinguisher_def by(rule interaction_bound|simp)+

lemma plossless_obsf_distinguisher [simp]:
  "plossless_gpv (exception_\<I> \<I>) (obsf_distinguisher \<A>)"
  if "plossless_gpv \<I> \<A>" "\<I> \<turnstile>g \<A> \<surd>"
  using that unfolding obsf_distinguisher_def by(simp)


type_synonym ('a, 'b, 'c, 'd) converter_obsf = "('a, 'b exception, 'c, 'd exception) converter"

translations                                                                                       
  (type) "('a, 'b, 'c, 'd) converter_obsf" <= (type) "('a, 'b exception, 'c, 'd exception) converter"

primcorec obsf_converter :: "('a, 'b, 'c, 'd) converter \<Rightarrow> ('a, 'b, 'c, 'd) converter_obsf" where
  "run_converter (obsf_converter conv) = (\<lambda>x. 
   map_gpv (map_prod id obsf_converter) id 
    (map_gpv (\<lambda>convF. case convF of Fault \<Rightarrow> (Fault, fail_converter) | OK (a, conv') \<Rightarrow> (OK a, conv')) id
      (try_gpv (map_gpv' exception_of_option id option_of_exception (gpv_stop (run_converter conv x))) (Done Fault))))"

lemma obsf_converter_exception [simp]: "obsf_converter fail_converter = const_converter Fault"
  by(coinduction)(simp add: rel_fun_def)

lemma obsf_converter_sel [simp]:
  "run_converter (obsf_converter conv) x =
   TRY map_gpv' (\<lambda>y. case y of None \<Rightarrow> (Fault, const_converter Fault) | Some(x, conv') \<Rightarrow> (OK x, obsf_converter conv')) id option_of_exception
         (gpv_stop (run_converter conv x))
   ELSE Done (Fault, const_converter Fault)"
  by(simp add: map_try_gpv)
    (simp add: map_gpv_conv_map_gpv' map_gpv'_comp o_def option.case_distrib[where h="map_prod _ _"] split_def id_def cong del: option.case_cong)

declare obsf_converter.sel [simp del]

lemma exec_gpv_obsf_resource:
  defines "exec_gpv1 \<equiv> exec_gpv"
    and "exec_gpv2 \<equiv> exec_gpv"
  shows
  "exec_gpv1 run_resource (map_gpv' id id option_of_exception (gpv_stop gpv)) (obsf_resource res) \<upharpoonleft> {(Some x, y)|x y. True} =
   map_spmf (map_prod Some obsf_resource) (exec_gpv2 run_resource gpv res)"
  (is "?lhs = ?rhs")
proof(rule spmf.leq_antisym)
  show "ord_spmf (=) ?lhs ?rhs" unfolding exec_gpv1_def
  proof(induction arbitrary: gpv res rule: exec_gpv_fixp_induct_strong)
    case adm show ?case by simp
    case bottom show ?case by simp
    case (step exec_gpv')
    show ?case unfolding exec_gpv2_def
      apply(subst exec_gpv.simps)
      apply(clarsimp simp add: map_bind_spmf bind_map_spmf restrict_bind_spmf o_def try_spmf_def intro!: ord_spmf_bind_reflI split!: generat.split)
      apply(clarsimp simp add: bind_map_pmf bind_spmf_def bind_assoc_pmf bind_return_pmf spmf.leq_trans[OF restrict_spmf_mono, OF step.hyps] id_def step.IH[simplified, simplified id_def exec_gpv2_def] intro!: rel_pmf_bind_reflI split!: option.split)
      done
  qed

  show "ord_spmf (=) ?rhs ?lhs" unfolding exec_gpv2_def
  proof(induction arbitrary: gpv res rule: exec_gpv_fixp_induct)
    case adm show ?case by simp
    case bottom show ?case by simp
    case (step exec_gpv')
    show ?case unfolding exec_gpv1_def
      apply(subst exec_gpv.simps)
      apply(clarsimp simp add: bind_map_spmf map_bind_spmf restrict_bind_spmf o_def try_spmf_def intro!: ord_spmf_bind_reflI split!: generat.split)
      apply(clarsimp simp add: bind_spmf_def bind_assoc_pmf bind_map_pmf map_bind_pmf bind_return_pmf id_def step.IH[simplified, simplified id_def exec_gpv1_def] intro!: rel_pmf_bind_reflI split!: option.split)
      done
  qed
qed
  
lemma obsf_attach: 
  assumes pfinite: "pfinite_converter \<I> \<I>' conv"
    and WT: "\<I>, \<I>' \<turnstile>\<^sub>C conv \<surd>"
    and WT_resource: "\<I>' \<turnstile>res res \<surd>"
  shows "outs_\<I> \<I> \<turnstile>\<^sub>R attach (obsf_converter conv) (obsf_resource res) \<sim> obsf_resource (attach conv res)"
  using assms
proof(coinduction arbitrary: conv res)
  case (eq_resource_on out conv res)
  then show ?case (is "rel_spmf ?X ?lhs ?rhs")
  proof -
    have "?lhs = map_spmf (\<lambda>((b, conv'), res'). (b, conv' \<rhd> res'))
     (exec_gpv run_resource
       (TRY map_gpv' (case_option (Fault, const_converter Fault) (\<lambda>(x, conv'). (OK x, obsf_converter conv'))) id option_of_exception (gpv_stop (run_converter conv out)) ELSE Done (Fault, const_converter Fault))
       (obsf_resource res))"
      (is "_ = map_spmf ?attach (exec_gpv _ (TRY ?gpv ELSE _) _)") by(clarsimp)
    also have "\<dots> =  TRY map_spmf ?attach (exec_gpv run_resource ?gpv (obsf_resource res)) ELSE return_spmf (Fault, const_resource Fault)"
      by(rule run_lossless_resource.exec_gpv_try_gpv[where \<I>="exception_\<I> \<I>'"])
        (use eq_resource_on in \<open>auto intro!: WT_gpv_map_gpv' WT_gpv_stop pfinite_gpv_stop[THEN iffD2] dest: WT_converterD pfinite_converterD lossless_resourceD\<close>)
    also have "\<dots> = TRY map_spmf (\<lambda>(rc, res'). case rc of None \<Rightarrow> (Fault, const_resource Fault) | Some (x, conv') \<Rightarrow> (OK x, obsf_converter conv' \<rhd> res'))
            ((exec_gpv run_resource (map_gpv' id id option_of_exception (gpv_stop (run_converter conv out))) (obsf_resource res)) \<upharpoonleft> {(Some x, y)|x y. True}) 
               ELSE return_spmf (Fault, const_resource Fault)" (is "_ = TRY map_spmf ?f _ ELSE ?z")
      by(subst map_gpv'_id12)(clarsimp simp add: map_gpv'_map_gpv_swap exec_gpv_map_gpv_id try_spmf_def restrict_spmf_def bind_map_pmf intro!: bind_pmf_cong[OF refl] split: option.split)
    also have "\<dots> = TRY map_spmf ?f (map_spmf (map_prod Some obsf_resource) (exec_gpv run_resource (run_converter conv out) res)) ELSE ?z"
      by(simp only: exec_gpv_obsf_resource)
    also have "rel_spmf ?X \<dots> ?rhs" using eq_resource_on
      by(auto simp add: spmf.map_comp o_def spmf_rel_map intro!: rel_spmf_try_spmf rel_spmf_reflI)
        (auto intro!: exI dest: run_resource.in_set_spmf_exec_gpv_into_results_gpv WT_converterD pfinite_converterD run_resource.exec_gpv_invariant)
    finally show ?case .
  qed
qed


lemma colossless_obsf_converter [simp]:
  "colossless_converter (exception_\<I> \<I>) \<I>' (obsf_converter conv)"
  by(coinduction arbitrary: conv)(auto split: option.split_asm)


lemma WT_obsf_converter [WT_intro]:
  "exception_\<I> \<I>, exception_\<I> \<I>' \<turnstile>\<^sub>C obsf_converter conv \<surd>" if "\<I>, \<I>' \<turnstile>\<^sub>C conv \<surd>"
  using that
  by(coinduction arbitrary: conv)(auto 4 3 dest: WT_converterD results_gpv_stop_SomeD split!: option.splits intro!: WT_intro)

lemma inline1_gpv_stop_obsf_converter:
  defines "inline1a \<equiv> inline1"
    and "inline1b \<equiv> inline1"
  shows "bind_spmf (inline1a run_converter (map_gpv' id id option_of_exception (gpv_stop gpv)) (obsf_converter conv))
     (\<lambda>xy. case xy of Inl (None, conv') \<Rightarrow> return_pmf None | Inl (Some x, conv') \<Rightarrow> return_spmf (Inl (x, conv')) | Inr y \<Rightarrow> return_spmf (Inr y)) = 
   map_spmf (map_sum (apsnd obsf_converter)
       (apsnd (map_prod (\<lambda>rpv input. case input of Fault \<Rightarrow> Done (Fault, const_converter Fault) | OK input' \<Rightarrow> 
            map_gpv' (\<lambda>res. case res of None \<Rightarrow> (Fault, const_converter Fault) | Some (x, conv') \<Rightarrow> (OK x, obsf_converter conv')) id option_of_exception (try_gpv (gpv_stop (rpv input')) (Done None))) 
     (\<lambda>rpv input. case input of Fault \<Rightarrow> Done None | OK input' \<Rightarrow> map_gpv' id id option_of_exception (gpv_stop (rpv input'))))))
    (inline1b run_converter gpv conv)"
  (is "?lhs = ?rhs")
proof(rule spmf.leq_antisym)
  show "ord_spmf (=) ?lhs ?rhs" unfolding inline1a_def
  proof(induction arbitrary: gpv conv rule: inline1_fixp_induct_strong)
    case adm show ?case by simp
    case bottom show ?case by simp
    case (step inline1')
    show ?case unfolding inline1b_def
      apply(subst inline1_unfold)
      apply(clarsimp simp add: map_spmf_bind_spmf bind_map_spmf spmf.map_comp o_def generat.map_comp intro!: ord_spmf_bind_reflI split!: generat.split)
      apply(clarsimp simp add: bind_spmf_def try_spmf_def bind_assoc_pmf bind_map_pmf bind_return_pmf intro!: rel_pmf_bind_reflI split!: option.split)
      subgoal unfolding bind_spmf_def[symmetric]
        by(rule ord_spmf_bindI[OF step.hyps, THEN spmf.leq_trans])
          (auto split!: option.split intro!: ord_spmf_bindI[OF step.hyps, THEN spmf.leq_trans] ord_spmf_reflI)
      subgoal unfolding bind_spmf_def[symmetric]
        by(clarsimp simp add: in_set_spmf[symmetric] inline1b_def split!: generat.split intro!: step.IH[THEN spmf.leq_trans])
          (auto simp add: fun_eq_iff map'_try_gpv split: exception.split)
      done
  qed

  show "ord_spmf (=) ?rhs ?lhs" unfolding inline1b_def
  proof(induction arbitrary: gpv conv rule: inline1_fixp_induct_strong)
    case adm show ?case by simp
    case bottom show ?case by simp
    case (step inline1')
    show ?case unfolding inline1a_def
      apply(subst inline1_unfold)
      apply(clarsimp simp add: map_spmf_bind_spmf bind_map_spmf spmf.map_comp o_def generat.map_comp intro!: ord_spmf_bind_reflI split!: generat.split)
      apply(clarsimp simp add: bind_spmf_def try_spmf_def bind_assoc_pmf bind_map_pmf bind_return_pmf intro!: rel_pmf_bind_reflI split!: option.split)
      apply(clarsimp simp add: bind_spmf_def[symmetric] in_set_spmf[symmetric] inline1a_def id_def[symmetric] split!: generat.split intro!: step.IH[THEN spmf.leq_trans])
      apply(auto simp add: fun_eq_iff map'_try_gpv split: exception.split)
      done
  qed
qed

lemma inline_gpv_stop_obsf_converter:
  "bind_gpv (inline run_converter (map_gpv' id id option_of_exception (gpv_stop gpv)) (obsf_converter conv)) (\<lambda>(x, conv'). case x of None \<Rightarrow> Fail | Some x' \<Rightarrow> Done (x, conv')) =
   bind_gpv (map_gpv' id id option_of_exception (gpv_stop (inline run_converter gpv conv))) (\<lambda>x. case x of None \<Rightarrow> Fail | Some (x', conv) \<Rightarrow> Done (Some x', obsf_converter conv))"
proof(coinduction arbitrary: gpv conv rule: gpv_coinduct_bind)
  case (Eq_gpv gpv conv)
  show "?case TYPE('c \<times> ('b, 'c, 'd, 'e) converter) TYPE('c \<times> ('b, 'c, 'd, 'e) converter)" (is "rel_spmf ?X ?lhs ?rhs")
  proof -
    have "?lhs = map_spmf (\<lambda>xyz. case xyz of Inl (x, conv) \<Rightarrow> Pure (Some x, conv) | Inr (out, rpv, rpv') \<Rightarrow> IO out (\<lambda>input. bind_gpv (bind_gpv (rpv input) (\<lambda>(x, y). inline run_converter (rpv' x) y)) (\<lambda>(x, conv'). case x of None \<Rightarrow> Fail | Some x' \<Rightarrow> Done (x, conv'))))
      (bind_spmf (inline1 run_converter (map_gpv' id id option_of_exception (gpv_stop gpv)) (obsf_converter conv))
         (\<lambda>xy. case xy of Inl (None, conv') \<Rightarrow> return_pmf None | Inl (Some x, conv') \<Rightarrow> return_spmf (Inl (x, conv')) | Inr y \<Rightarrow> return_spmf (Inr y)))"
      (is "_ = map_spmf ?f _")
      by(auto simp del: bind_gpv_sel' simp add: bind_gpv.sel map_bind_spmf inline_sel bind_map_spmf o_def intro!: bind_spmf_cong[OF refl] split!: sum.split option.split)
    also have "\<dots> = map_spmf ?f (map_spmf (map_sum (apsnd obsf_converter) (apsnd (map_prod (\<lambda>rpv. case_exception (Done (Fault, const_converter Fault))
                     (\<lambda>input'. map_gpv' (case_option (Fault, const_converter Fault) (\<lambda>(x, conv'). (OK x, obsf_converter conv'))) id option_of_exception (TRY gpv_stop (rpv input') ELSE Done None)))
             (\<lambda>rpv. case_exception (Done None) (\<lambda>input'. map_gpv' id id option_of_exception (gpv_stop (rpv input')))))))
       (inline1 run_converter gpv conv))"
      by(simp only: inline1_gpv_stop_obsf_converter)
    also have "\<dots> = bind_spmf (inline1 run_converter gpv conv) (\<lambda>y. return_spmf (?f (map_sum (apsnd obsf_converter)
                     (apsnd (map_prod (\<lambda>rpv. case_exception (Done (Fault, const_converter Fault)) (\<lambda>input'. map_gpv' (case_option (Fault, const_converter Fault) (\<lambda>(x, conv'). (OK x, obsf_converter conv'))) id option_of_exception (TRY gpv_stop (rpv input') ELSE Done None)))
                         (\<lambda>rpv. case_exception (Done None) (\<lambda>input'. map_gpv' id id option_of_exception (gpv_stop (rpv input'))))))
                     y)))"
      by(simp add: map_spmf_conv_bind_spmf)
    also have "rel_spmf ?X \<dots> (bind_spmf (inline1 run_converter gpv conv)
       (\<lambda>x. map_spmf (map_generat id id ((\<circ>) (case_sum id (\<lambda>r. bind_gpv r (case_option Fail (\<lambda>(x', conv). Done (Some x', obsf_converter conv)))))))
              (case map_generat id id (map_fun option_of_exception (map_gpv' id id option_of_exception))
                     (map_generat Some id (\<lambda>rpv. case_option (Done None) (\<lambda>input'. gpv_stop (rpv input')))
                       (case x of Inl x \<Rightarrow> Pure x
                        | Inr (out, oracle, rpv) \<Rightarrow> IO out (\<lambda>input. bind_gpv (oracle input) (\<lambda>(x, y). inline run_converter (rpv x) y)))) of
               Pure x \<Rightarrow>
                 map_spmf (map_generat id id ((\<circ>) Inl)) (the_gpv (case x of None \<Rightarrow> Fail | Some (x', conv) \<Rightarrow> Done (Some x', obsf_converter conv)))
               | IO out c \<Rightarrow> return_spmf (IO out (\<lambda>input. Inr (c input))))))" 
      (is "rel_spmf _ _ ?rhs2" is "rel_spmf _ (bind_spmf _ ?L) (bind_spmf _ ?R)") 
    proof(rule rel_spmf_bind_reflI)
      fix x :: "'a \<times> ('b, 'c, 'd, 'e) converter + 'd \<times> ('c \<times> ('b, 'c, 'd, 'e) converter, 'd, 'e) rpv \<times> ('a, 'b, 'c) rpv"
      assume x: "x \<in> set_spmf (inline1 run_converter gpv conv)"
      consider (Inl) a conv' where "x = Inl (a, conv')" | (Inr) out rpv rpv' where "x = Inr (out, rpv, rpv')" by(cases x) auto
      then show "rel_spmf ?X (?L x) (?R x)" 
      proof cases
        case Inr
        have "\<exists>(gpv2 :: ('c \<times> ('b, 'c, 'd, 'e) converter, 'd, 'e exception) gpv) (gpv2' :: ('c \<times> ('b, 'c, 'd, 'e) converter, 'd, 'e exception) gpv) f f'.
           bind_gpv (map_gpv' (case_option (Fault, const_converter Fault) (\<lambda>p. (OK (fst p), obsf_converter (snd p)))) id option_of_exception (TRY gpv_stop (rpv input) ELSE Done None))
             (\<lambda>x. case fst x of Fault \<Rightarrow> Fail | OK xa \<Rightarrow> bind_gpv (inline run_converter (map_gpv' id id option_of_exception (gpv_stop (rpv' xa))) (snd x)) (\<lambda>p. case fst p of None \<Rightarrow> Fail | Some x' \<Rightarrow> Done (Some x', snd p))) =
             bind_gpv gpv2 f \<and>
           bind_gpv (map_gpv' id id option_of_exception (gpv_stop (rpv input))) (case_option Fail (\<lambda>x. bind_gpv (map_gpv' id id option_of_exception (gpv_stop (inline run_converter (rpv' (fst x)) (snd x)))) (case_option Fail (\<lambda>p. Done (Some (fst p), obsf_converter (snd p)))))) =
             bind_gpv gpv2' f' \<and>
           rel_gpv (\<lambda>x y. \<exists>gpv conv. f x = bind_gpv (inline run_converter (map_gpv' id id option_of_exception (gpv_stop gpv)) (obsf_converter conv)) (\<lambda>p. case fst p of None \<Rightarrow> Fail | Some x' \<Rightarrow> Done (Some x', snd p)) \<and>
                     f' y = bind_gpv (map_gpv' id id option_of_exception (gpv_stop (inline run_converter gpv conv))) (case_option Fail (\<lambda>p. Done (Some (fst p), obsf_converter (snd p)))))
              (=) gpv2 gpv2'"
          (is "\<exists>gpv2 gpv2' f f'. ?lhs1 input = _ \<and> ?rhs1 input = _ \<and> rel_gpv (?X f f') _ _ _") for input 
        proof(intro exI conjI)
          let ?gpv2 = "bind_gpv (map_gpv' id id option_of_exception (TRY gpv_stop (rpv input) ELSE Done None)) (\<lambda>x. case x of None \<Rightarrow> Fail | Some x \<Rightarrow> Done x)"
          let ?gpv2' = "bind_gpv (map_gpv' id id option_of_exception (gpv_stop (rpv input))) (\<lambda>x. case x of None \<Rightarrow> Fail | Some x \<Rightarrow> Done x)"
          let ?f = "\<lambda>x. bind_gpv (inline run_converter (map_gpv' id id option_of_exception (gpv_stop (rpv' (fst x)))) (obsf_converter (snd x))) (\<lambda>p. case fst p of None \<Rightarrow> Fail | Some x' \<Rightarrow> Done (Some x', snd p))"
          let ?f' = "\<lambda>x. bind_gpv (map_gpv' id id option_of_exception (gpv_stop (inline run_converter (rpv' (fst x)) (snd x)))) (case_option Fail (\<lambda>p. Done (Some (fst p), obsf_converter (snd p))))"
          show "?lhs1 input = bind_gpv ?gpv2 ?f"
            by(subst map_gpv'_id12[THEN trans, OF map_gpv'_map_gpv_swap])
              (auto simp add: bind_map_gpv o_def bind_gpv_assoc intro!: bind_gpv_cong split!: option.split)
          show "?rhs1 input = bind_gpv ?gpv2' ?f'"
            by(auto simp add: bind_gpv_assoc id_def[symmetric] intro!: bind_gpv_cong split!: option.split)
          show "rel_gpv (?X ?f ?f') (=) ?gpv2 ?gpv2'" using Inr x
            by(auto simp add: map'_try_gpv id_def[symmetric] bind_try_Done_Fail intro: gpv.rel_refl_strong)
        qed
        then show ?thesis using Inr
          by(clarsimp split!: sum.split exception.split simp add: rel_fun_def bind_gpv_assoc split_def map_gpv'_bind_gpv exception.case_distrib[where h="\<lambda>x. bind_gpv (inline _ x _) _"] option.case_distrib[where h="\<lambda>x. bind_gpv (map_gpv' _ _ _ x) _"] cong: exception.case_cong option.case_cong)
      qed simp
    qed
    moreover have "?rhs2 = ?rhs" 
      by(simp del: bind_gpv_sel' add: bind_gpv.sel map_bind_spmf inline_sel bind_map_spmf o_def)
    ultimately show ?thesis by(simp only:)
  qed
qed

lemma obsf_comp_converter:
  assumes WT: "\<I>, \<I>' \<turnstile>\<^sub>C conv1 \<surd>" "\<I>', \<I>'' \<turnstile>\<^sub>C conv2 \<surd>"
    and pfinite1: "pfinite_converter \<I> \<I>' conv1"
  shows "exception_\<I> \<I>, exception_\<I> \<I>'' \<turnstile>\<^sub>C obsf_converter (comp_converter conv1 conv2) \<sim> comp_converter (obsf_converter conv1) (obsf_converter conv2)"
  using WT pfinite1 supply eq_\<I>_gpv_map_gpv[simp del]
proof(coinduction arbitrary: conv1 conv2)
  case eq_\<I>_converter
  show ?case (is "eq_\<I>_gpv ?X _ ?lhs ?rhs")
  proof -
    have "eq_\<I>_gpv (=) (exception_\<I> \<I>'') ?rhs (TRY map_gpv (\<lambda>((b, conv1'), conv2'). (b, conv1' \<odot> conv2')) id
               (inline run_converter
                 (map_gpv'
                   (case_option (Fault, const_converter Fault)
                     (\<lambda>(x, conv'). (OK x, obsf_converter conv')))
                   id option_of_exception (gpv_stop (run_converter conv1 q)))
                 (obsf_converter conv2)) ELSE Done (Fault, const_converter Fault))"
      (is "eq_\<I>_gpv _ _ _ ?rhs2" is "eq_\<I>_gpv _ _ _ (try_gpv (map_gpv ?f _ ?inline) ?else)")
      using eq_\<I>_converter
      apply simp
      apply(rule run_colossless_converter.inline_try_gpv[where \<I>="exception_\<I> \<I>'"])
          apply(auto intro!: WT_intro pfinite_gpv_stop[THEN iffD2] dest: WT_converterD pfinite_converterD colossless_converterD)
      done
    term "bind_gpv (inline run_converter (map_gpv' id id option_of_exception (gpv_stop (run_converter conv1 q))) (obsf_converter conv2))
           (\<lambda>(x, conv'). case x of None \<Rightarrow> Fail | Some x' \<Rightarrow> Done (x, conv'))"
    
    also have "?rhs2 = try_gpv (map_gpv ?f id
       (map_gpv (\<lambda>(xo, conv'). case xo of None \<Rightarrow> ((Fault, const_converter Fault), conv') | Some (x, conv) \<Rightarrow> ((OK x, obsf_converter conv), conv')) id
         (bind_gpv (inline run_converter (map_gpv' id id option_of_exception (gpv_stop (run_converter conv1 q))) (obsf_converter conv2))
           (\<lambda>(x, conv'). case x of None \<Rightarrow> Fail | Some x' \<Rightarrow> Done (x, conv')))))
        ?else"
      apply(simp add: map_gpv_bind_gpv gpv.map_id)
      apply(subst try_gpv_bind_gpv)
      apply(simp add: split_def option.case_distrib[where h="map_gpv _ _"] option.case_distrib[where h="fst"] option.case_distrib[where h="\<lambda>x. try_gpv x _"] cong del: option.case_cong)
      apply(subst option.case_distrib[where h=Done, symmetric, abs_def])+
      apply(fold map_gpv_conv_bind)
      apply(simp add: map_try_gpv gpv.map_comp o_def)
      apply(rule try_gpv_cong)
       apply(subst map_gpv'_id12)
       apply(subst map_gpv'_map_gpv_swap)
       apply(simp add: inline_map_gpv gpv.map_comp id_def[symmetric])
       apply(rule gpv.map_cong[OF refl])
        apply(auto split: option.split)
      done
    also have "\<dots> = try_gpv (map_gpv ?f id
       (map_gpv (\<lambda>(xo, conv'). case xo of None \<Rightarrow> ((Fault, const_converter Fault), conv') | Some (x, conv) \<Rightarrow> ((OK x, obsf_converter conv), conv')) id 
(bind_gpv
                (map_gpv' id id option_of_exception
                  (gpv_stop (inline run_converter (run_converter conv1 q) conv2)))
                (case_option Fail
                  (\<lambda>(x', conv).
                      Done
                       (Some x',
                        obsf_converter
                         conv)))))) ?else"
      by(simp only: inline_gpv_stop_obsf_converter)
    also have "eq_\<I>_gpv ?X (exception_\<I> \<I>'') ?lhs \<dots>" using eq_\<I>_converter
      apply simp
      apply(simp add: map_gpv_bind_gpv gpv.map_id)
      apply(subst try_gpv_bind_gpv)
      apply(simp add: split_def option.case_distrib[where h="map_gpv _ _"] option.case_distrib[where h="fst"] option.case_distrib[where h="\<lambda>x. try_gpv x _"] cong del: option.case_cong)
      apply(subst option.case_distrib[where h=Done, symmetric, abs_def])+
      apply(fold map_gpv_conv_bind)
      apply(simp add: map_try_gpv gpv.map_comp o_def)
      apply(rule eq_\<I>_gpv_try_gpv_cong)
       apply(subst map_gpv'_id12)
       apply(subst map_gpv'_map_gpv_swap)
       apply(simp add: eq_\<I>_gpv_map_gpv id_def[symmetric])
       apply(subst map_gpv_conv_map_gpv')
       apply(subst gpv_stop_map')
       apply(subst option.map_id0)
       apply(subst map_gpv_conv_map_gpv'[symmetric])
       apply(subst map_gpv'_map_gpv_swap)
       apply(simp add: eq_\<I>_gpv_map_gpv id_def[symmetric])
       apply(rule eq_\<I>_gpv_reflI)
        apply(clarsimp split!: option.split simp add: eq_onp_def)
         apply(erule notE)
         apply(rule eq_\<I>_converter_reflI)
         apply simp
        apply(drule results_gpv_stop_SomeD)
        apply(rule conjI)
         apply(rule imageI)
         apply(drule run_converter.results_gpv_inline)
           apply(erule (1) WT_converterD)
          apply simp
         apply clarsimp
         apply(drule (2) WT_converterD_results)
         apply simp
        apply(rule disjI1)
        apply(rule exI conjI refl)+
         apply(drule run_converter.results_gpv_inline)
           apply(erule (1) WT_converterD)
          apply simp
         apply clarsimp
         apply(drule (2) WT_converterD_results)
         apply simp
         apply(drule run_converter.results_gpv_inline)
           apply(erule (1) WT_converterD)
          apply simp
        apply clarsimp
        apply(drule (1) pfinite_converterD)
        apply blast
       apply(rule WT_intro run_converter.WT_gpv_inline_invar|simp)+
        apply(erule (1) WT_converterD)
       apply simp
      apply(simp add: eq_onp_def)
      apply(rule disjI2)
      apply(rule eq_\<I>_converter_reflI)
      apply simp
      done
    finally (eq_\<I>_gpv_eq_OO2) show ?thesis . 
  qed
qed

lemma resource_of_obsf_oracle_Fault [simp]:
  "resource_of_oracle (obsf_oracle oracle) Fault = const_resource Fault"
  by(coinduction)(auto simp add: rel_fun_def)

lemma obsf_resource_of_oracle [simp]:
  "obsf_resource (resource_of_oracle oracle s) = resource_of_oracle (obsf_oracle oracle) (OK s)"
  by(coinduction arbitrary: s rule: resource.coinduct_strong)
    (auto 4 3 simp add: rel_fun_def map_try_spmf spmf_rel_map intro!: rel_spmf_try_spmf rel_spmf_reflI)

lemma trace_callee_eq_obsf_Fault [simp]: "A \<turnstile>\<^sub>C obsf_oracle callee1(Fault) \<approx> obsf_oracle callee2(Fault)"
  by(coinduction rule: trace_callee_eq_coinduct) auto

lemma obsf_resource_eq_\<I>_cong: "A \<turnstile>\<^sub>R obsf_resource res1 \<sim> obsf_resource res2" if "A \<turnstile>\<^sub>R res1 \<sim> res2"
  using that by(coinduction arbitrary: res1 res2)(fastforce intro!: rel_spmf_try_spmf simp add: spmf_rel_map elim!: rel_spmf_mono dest: eq_resource_onD)

lemma trace_callee_eq_obsf_oracleI:
  assumes "trace_callee_eq callee1 callee2 A p q"
  shows "trace_callee_eq (obsf_oracle callee1) (obsf_oracle callee2) A (try_spmf (map_spmf OK p) (return_spmf Fault)) (try_spmf (map_spmf OK q) (return_spmf Fault))"
  using assms
proof(coinduction arbitrary: p q rule: trace_callee_eq_coinduct_strong)
  case (step z p q)
  have "?lhs = map_pmf (\<lambda>x. case x of None \<Rightarrow> Some Fault | Some y \<Rightarrow> Some (OK y)) (bind_spmf p (\<lambda>s'. map_spmf fst (callee1 s' z)))"
    by(auto simp add: bind_spmf_def try_spmf_def bind_assoc_pmf map_bind_pmf bind_map_pmf bind_return_pmf option.case_distrib[where h="map_pmf _"] option.case_distrib[where h=return_pmf, symmetric, abs_def] map_pmf_def[symmetric] pmf.map_comp o_def intro!: bind_pmf_cong[OF refl] pmf.map_cong[OF refl] split: option.split)
  also have "bind_spmf p (\<lambda>s'. map_spmf fst (callee1 s' z)) = bind_spmf q (\<lambda>s'. map_spmf fst (callee2 s' z))"
    using step(1)[THEN trace_callee_eqD[where xs="[]" and x=z]] step(2) by simp
  also have "map_pmf (\<lambda>x. case x of None \<Rightarrow> Some Fault | Some y \<Rightarrow> Some (OK y)) \<dots> = ?rhs" 
    by(auto simp add: bind_spmf_def try_spmf_def bind_assoc_pmf map_bind_pmf bind_map_pmf bind_return_pmf option.case_distrib[where h="map_pmf _"] option.case_distrib[where h=return_pmf, symmetric, abs_def] map_pmf_def[symmetric] pmf.map_comp o_def intro!: bind_pmf_cong[OF refl] pmf.map_cong[OF refl] split: option.split)
  finally show ?case .
next
  case (sim x s1 s2 ye s1' s2' p q)
  have eq1: "bind_spmf (try_spmf (map_spmf OK p) (return_spmf Fault)) (\<lambda>s. obsf_oracle callee1 s x) = 
     try_spmf (bind_spmf p (\<lambda>s. map_spmf (map_prod OK OK) (callee1 s x))) (return_spmf (Fault, Fault))"
    by(auto simp add: bind_spmf_def try_spmf_def bind_assoc_pmf bind_map_pmf bind_return_pmf intro!: bind_pmf_cong[OF refl] split: option.split)
  have eq2: "bind_spmf (try_spmf (map_spmf OK q) (return_spmf Fault)) (\<lambda>s. obsf_oracle callee2 s x) = 
     try_spmf (bind_spmf q (\<lambda>s. map_spmf (map_prod OK OK) (callee2 s x))) (return_spmf (Fault, Fault))"
    by(auto simp add: bind_spmf_def try_spmf_def bind_assoc_pmf bind_map_pmf bind_return_pmf intro!: bind_pmf_cong[OF refl] split: option.split)

  show ?case
  proof(cases ye)
    case [simp]: Fault
    have "lossless_spmf (bind_spmf p (\<lambda>s. map_spmf (map_prod OK OK) (callee1 s x))) \<longleftrightarrow> lossless_spmf (bind_spmf q (\<lambda>s. map_spmf (map_prod OK OK) (callee2 s x)))"
      using sim(1)[THEN trace_callee_eqD[where xs="[]" and x=x], THEN arg_cong[where f="lossless_spmf"]] sim(2) by simp
    then have "?eq" by(simp add: eq1 eq2)(subst (1 2) cond_spmf_fst_try2, auto)
    then show ?thesis ..
  next
    case [simp]: (OK y)
    have eq3: "fst ` set_spmf (bind_spmf p (\<lambda>s. callee1 s x)) = fst ` set_spmf (bind_spmf q (\<lambda>s. callee2 s x))" 
      using trace_callee_eqD[OF sim(1) _ sim(2), where xs="[]", THEN arg_cong[where f="set_spmf"]]
      by(auto simp add: bind_UNION image_UN del: equalityI)
    show ?thesis
    proof(cases "y \<in> fst ` set_spmf (bind_spmf p (\<lambda>s. callee1 s x))")
      case True
      have eq4: "cond_spmf_fst (bind_spmf p (\<lambda>s. map_spmf (apfst OK) (callee1 s x))) (OK y) = cond_spmf_fst (bind_spmf p (\<lambda>s. callee1 s x)) y"
        "cond_spmf_fst (bind_spmf q (\<lambda>s. map_spmf (apfst OK) (callee2 s x))) (OK y) = cond_spmf_fst (bind_spmf q (\<lambda>s. callee2 s x)) y"
        by(fold map_bind_spmf[unfolded o_def])(simp_all add: cond_spmf_fst_map_inj)
      have ?sim
        unfolding eq1 eq2
        apply(subst (1 2) cond_spmf_fst_try1)
          apply simp
         apply simp
        apply(rule exI[where x="cond_spmf_fst (bind_spmf p (\<lambda>s. map_spmf (apfst OK) (callee1 s x))) ye"])
        apply(rule exI[where x="cond_spmf_fst (bind_spmf q (\<lambda>s. map_spmf (apfst OK) (callee2 s x))) ye"])
        apply(subst (1 2) try_spmf_lossless)
        subgoal using True unfolding eq3 by(auto simp add: bind_UNION image_UN intro!: rev_bexI rev_image_eqI)
        subgoal using True by(auto simp add: bind_UNION image_UN intro!: rev_bexI rev_image_eqI)
        apply(simp add: map_cond_spmf_fst map_bind_spmf o_def spmf.map_comp map_prod_def split_def)
        apply(simp add: eq4)
        apply(rule trace_callee_eqI)
        subgoal for xs z
          using sim(1)[THEN trace_callee_eqD[where xs="(x, y) # xs" and x=z]] sim(2)
          apply simp
          done
        done
      then show ?thesis ..
    next
      case False
      with eq3 have "y \<notin> fst ` set_spmf (bind_spmf q (\<lambda>s. callee2 s x))" by auto
      with False have ?eq
        apply simp
        apply(subst (1 2) cond_spmf_fst_eq_return_None[THEN iffD2])
          apply(auto simp add: bind_UNION split: if_split_asm intro: rev_image_eqI)
        done
      then show ?thesis ..
    qed
  qed
qed

lemma trace_callee_eq'_obsf_resourceI:
  assumes " A \<turnstile>\<^sub>C callee1(s) \<approx> callee2(s')"
  shows "A \<turnstile>\<^sub>C obsf_oracle callee1(OK s) \<approx> obsf_oracle callee2(OK s')"
  using assms[THEN trace_callee_eq_obsf_oracleI] by simp

lemma trace_eq_obsf_resourceI:
  assumes "A \<turnstile>\<^sub>R res1 \<approx> res2"
  shows "A \<turnstile>\<^sub>R obsf_resource res1 \<approx> obsf_resource res2"
  using assms
  apply(subst (2 4) resource_of_oracle_run_resource[symmetric])
  apply(subst (asm) (1 2) resource_of_oracle_run_resource[symmetric])
  apply(drule trace_callee_eq'_obsf_resourceI)
  apply simp
  apply(simp add: resource_of_oracle_run_resource)
  done

lemma spmf_run_obsf_oracle_obsf_distinguisher [rule_format]:
  defines "eg1 \<equiv> exec_gpv" and "eg2 \<equiv> exec_gpv" shows
  "spmf (map_spmf fst (eg1 (obsf_oracle oracle) (obsf_distinguisher gpv) (OK s))) True =
   spmf (map_spmf fst (eg2 oracle gpv s)) True"
  (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs" unfolding eg1_def
  proof(induction arbitrary: gpv s rule: exec_gpv_fixp_induct_strong)
    case adm show ?case by simp
    case bottom show ?case by simp
    case (step exec_gpv')
    show ?case unfolding eg2_def
      apply(subst exec_gpv.simps)
      apply(clarsimp simp add: obsf_distinguisher_def bind_map_spmf map_bind_spmf o_def)
      apply(subst (1 2) spmf_bind)
      apply(rule Bochner_Integration.integral_mono)
        apply(rule measure_spmf.integrable_const_bound[where B=1]; simp add: pmf_le_1)
       apply(rule measure_spmf.integrable_const_bound[where B=1]; simp add: pmf_le_1)
      apply(clarsimp split: generat.split simp add: map_bind_spmf o_def)
      apply(simp add: try_spmf_def bind_spmf_pmf_assoc bind_map_pmf)
      apply(simp add: bind_spmf_def)
      apply(subst (1 2) pmf_bind)
      apply(rule Bochner_Integration.integral_mono)
        apply(rule measure_pmf.integrable_const_bound[where B=1]; simp add: pmf_le_1)
       apply(rule measure_pmf.integrable_const_bound[where B=1]; simp add: pmf_le_1)
      apply(clarsimp split!: option.split simp add: bind_return_pmf)
       apply(rule antisym)
        apply(rule order_trans)
         apply(rule step.hyps[THEN ord_spmf_map_spmfI, THEN ord_spmf_eq_leD])
        apply simp
       apply(simp)
      apply(rule step.IH[unfolded eg2_def obsf_distinguisher_def])
      done
  qed

  show "?rhs \<le> ?lhs" unfolding eg2_def 
  proof(induction arbitrary: gpv s rule: exec_gpv_fixp_induct_strong)
    case adm show ?case by simp
    case bottom show ?case by simp
    case (step exec_gpv')
    show ?case unfolding eg1_def
      apply(subst exec_gpv.simps)
      apply(clarsimp simp add: obsf_distinguisher_def bind_map_spmf map_bind_spmf o_def)
      apply(subst (1 2) spmf_bind)
      apply(rule Bochner_Integration.integral_mono)
        apply(rule measure_spmf.integrable_const_bound[where B=1]; simp add: pmf_le_1)
       apply(rule measure_spmf.integrable_const_bound[where B=1]; simp add: pmf_le_1)
      apply(clarsimp split: generat.split simp add: map_bind_spmf o_def)
      apply(simp add: try_spmf_def bind_spmf_pmf_assoc bind_map_pmf)
      apply(simp add: bind_spmf_def)
      apply(subst (1 2) pmf_bind)
      apply(rule Bochner_Integration.integral_mono)
        apply(rule measure_pmf.integrable_const_bound[where B=1]; simp add: pmf_le_1)
       apply(rule measure_pmf.integrable_const_bound[where B=1]; simp add: pmf_le_1)
      apply(clarsimp split!: option.split simp add: bind_return_pmf)
      apply(rule step.IH[unfolded eg1_def obsf_distinguisher_def])
      done
  qed
qed

lemma spmf_obsf_distinguisher_obsf_resource_True:
  "spmf (connect_obsf (obsf_distinguisher \<A>) (obsf_resource res)) True = spmf (connect \<A> res) True"
  unfolding connect_def
  apply(subst (2) resource_of_oracle_run_resource[symmetric])
  apply(simp add: exec_gpv_resource_of_oracle spmf.map_comp spmf_run_obsf_oracle_obsf_distinguisher)
  done

lemma advantage_obsf_distinguisher: 
  "advantage (obsf_distinguisher \<A>) (obsf_resource ideal_resource) (obsf_resource real_resource) =
   advantage \<A> ideal_resource real_resource"
  unfolding advantage_def by(simp add: spmf_obsf_distinguisher_obsf_resource_True)

end
