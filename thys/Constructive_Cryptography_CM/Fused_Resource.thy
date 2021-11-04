theory Fused_Resource imports
  Fold_Spmf
begin

(* TODO: move these somewhere *)
context includes \<I>.lifting begin
lift_definition e\<I> :: "('a, 'b) \<I> \<Rightarrow> ('a, 'b \<times> 'c) \<I>" is "\<lambda>\<I> x. \<I> x \<times> UNIV" .

lemma outs_\<I>_e\<I>[simp]: "outs_\<I> (e\<I> \<I>) = outs_\<I> \<I>"
  by transfer simp

lemma responses_\<I>_e\<I> [simp]: "responses_\<I> (e\<I> \<I>) x = responses_\<I> \<I> x \<times> UNIV"
  by transfer simp

lemma e\<I>_map_\<I>: "e\<I> (map_\<I> f g \<I>) = map_\<I> f (apfst g) (e\<I> \<I>)"
  by transfer(auto simp add: fun_eq_iff intro: rev_image_eqI)

lemma e\<I>_inverse [simp]: "map_\<I> id fst (e\<I> \<I>) = \<I>"
  by transfer auto
end
lifting_update \<I>.lifting
lifting_forget \<I>.lifting


section \<open>Fused Resource\<close>

subsection \<open>Event Oracles -- they generate events\<close>

type_synonym 
  ('state, 'event, 'input, 'output) eoracle = "('state, 'input, 'output \<times> 'event list) oracle'" 

definition
  parallel_eoracle :: "
    ('s1, 'e1, 'i1, 'o1) eoracle \<Rightarrow> ('s2, 'e2, 'i2, 'o2) eoracle \<Rightarrow>
      ('s1 \<times> 's2, 'e1 + 'e2, 'i1 + 'i2, 'o1 + 'o2) eoracle"
  where
    "parallel_eoracle eoracle1 eoracle2 state \<equiv>
       comp
        (map_spmf 
          (map_prod 
            (case_sum 
              (map_prod Inl (map Inl)) 
              (map_prod Inr (map Inr))) 
            id))
        (parallel_oracle eoracle1 eoracle2 state)"

definition
  plus_eoracle :: "
    ('s, 'e1, 'i1, 'o1) eoracle \<Rightarrow> ('s, 'e2, 'i2, 'o2) eoracle \<Rightarrow>
      ('s, 'e1 + 'e2, 'i1 + 'i2, 'o1 + 'o2) eoracle"
  where
    "plus_eoracle eoracle1 eoracle2 state \<equiv>
       comp
        (map_spmf 
          (map_prod 
            (case_sum 
              (map_prod Inl (map Inl)) 
              (map_prod Inr (map Inr))) 
            id))
        (plus_oracle eoracle1 eoracle2 state)"

definition
  translate_eoracle :: "
    ('s_event, 'e1, 'e2 list) oracle' \<Rightarrow> ('s_event \<times> 's, 'e1, 'i, 'o) eoracle \<Rightarrow>
      ('s_event \<times> 's, 'e2, 'i, 'o) eoracle"
  where
    "translate_eoracle translator eoracle state inp \<equiv> 
      bind_spmf
        (eoracle state inp)
        (\<lambda>((out, e_in), s).
          let conc = (\<lambda>(es, st) e. map_spmf (map_prod ((@) es) id) (translator st e)) in do {
          (e_out, s_event) \<leftarrow> foldl_spmf conc (return_spmf ([], fst s)) e_in;
          return_spmf ((out, e_out), s_event, snd s)
        })"


subsection \<open>Event Handlers -- they absorb (and silently handle) events\<close>

type_synonym
  ('state, 'event) handler = "'state \<Rightarrow> 'event \<Rightarrow> 'state spmf"

fun
  parallel_handler :: "('s1, 'e1) handler \<Rightarrow> ('s2, 'e2) handler \<Rightarrow> ('s1 \<times> 's2, 'e1 + 'e2) handler"
  where
    "parallel_handler left _ s (Inl e1) = map_spmf (\<lambda>s1'. (s1', snd s)) (left (fst s) e1)"
  | "parallel_handler _ right s (Inr e2) = map_spmf (\<lambda>s2'. (fst s, s2')) (right (snd s) e2)"

definition
  plus_handler :: "('s, 'e1) handler \<Rightarrow> ('s, 'e2) handler \<Rightarrow> ('s, 'e1 + 'e2) handler"
  where
    "plus_handler left right s \<equiv> case_sum (left s) (right s)"

lemma parallel_handler_left:
  "map_fun id (map_fun Inl id) (parallel_handler left right) = 
    (\<lambda>(s_l, s_r) q. map_spmf (\<lambda>s_l'. (s_l', s_r)) (left s_l q))"
  by force

lemma parallel_handler_right:
  "map_fun id (map_fun Inr id) (parallel_handler left right) = 
    (\<lambda>(s_l, s_r) q. map_spmf (\<lambda>s_r'. (s_l, s_r')) (right s_r q))"
  by force

lemma in_set_spmf_parallel_handler:
  "s' \<in> set_spmf (parallel_handler left right s x) \<longleftrightarrow>
  (case x of Inl e \<Rightarrow> fst s' \<in> set_spmf (left (fst s) e) \<and> snd s' = snd s
    | Inr e \<Rightarrow> snd s' \<in> set_spmf (right (snd s) e) \<and> fst s' = fst s)"
  by(cases s; cases s'; auto split: sum.split)

subsection \<open>Fused Resource Construction\<close>

codatatype 
  ('s_core, 'event, 'iadv_core, 'iusr_core, 'oadv_core, 'ousr_core) core =
    Core
      (cpoke: "('s_core, 'event) handler")
      (cfunc_adv: "('s_core, 'iadv_core, 'oadv_core) oracle'")
      (cfunc_usr: "('s_core, 'iusr_core, 'ousr_core) oracle'")

declare core.sel_transfer[transfer_rule del]
declare core.ctr_transfer[transfer_rule del]
declare core.case_transfer[transfer_rule del]

context 
  includes lifting_syntax 
begin

inductive 
  rel_core':: "
    ('s_core \<Rightarrow> 's_core' \<Rightarrow> bool) \<Rightarrow> 
    ('event \<Rightarrow> 'event' \<Rightarrow> bool) \<Rightarrow> 
    ('iadv_core \<Rightarrow> 'iadv_core' \<Rightarrow> bool) \<Rightarrow>
    ('iusr_core \<Rightarrow> 'iusr_core' \<Rightarrow> bool) \<Rightarrow> 
    ('oadv_core \<Rightarrow> 'oadv_core' \<Rightarrow> bool) \<Rightarrow> 
    ('ousr_core \<Rightarrow> 'ousr_core' \<Rightarrow> bool) \<Rightarrow>
    ('s_core, 'event, 'iadv_core, 'iusr_core, 'oadv_core, 'ousr_core) core \<Rightarrow> 
    ('s_core', 'event', 'iadv_core', 'iusr_core', 'oadv_core', 'ousr_core') core \<Rightarrow> bool"
  for S E IA IU OA OU
  where "rel_core' S E IA IU OA OU (Core cpoke cfunc_adv cfunc_usr) (Core cpoke' cfunc_adv' cfunc_usr')"
  if 
    "(S ===> E ===> rel_spmf S) cpoke cpoke'" and 
    "(S ===> IA ===> rel_spmf (rel_prod OA S)) cfunc_adv cfunc_adv'" and 
    "(S ===> IU ===> rel_spmf (rel_prod OU S)) cfunc_usr cfunc_usr'"
  for cpoke cfunc_adv cfunc_usr

inductive_simps 
  rel_core'_simps [simp]: 
    "rel_core' S E IA IU OA OU (Core cpoke' cfunc_adv' cfunc_usr') (Core cpoke'' cfunc_adv'' cfunc_usr'')"

lemma 
  rel_core'_eq [relator_eq]:
    "rel_core' (=) (=) (=) (=) (=) (=) = (=)"
  apply(intro ext)
  subgoal for x y by(cases x; cases y)(auto simp add: fun_eq_iff rel_fun_def relator_eq)
  done

lemma 
  rel_core'_mono [relator_mono]:
    "rel_core' S E IA IU OA OU \<le> rel_core' S E' IA' IU' OA' OU'"
  if "E' \<le> E" "IA' \<le> IA" "IU' \<le> IU" "OA \<le> OA'" "OU \<le> OU'"
  apply(rule predicate2I)
  subgoal for x y
    apply(cases x; cases y; clarsimp; intro conjI)
      apply(erule rel_fun_mono rel_spmf_mono prod.rel_mono[THEN predicate2D, rotated -1] |
        rule impI that order_refl | erule that[THEN predicate2D] | erule rel_spmf_mono | assumption)+
    done
  done

lemma 
  cpoke_parametric [transfer_rule]:
    "(rel_core' S E IA IU OA OU ===> S ===> E ===> rel_spmf S) cpoke cpoke"
  by(rule rel_funI; erule rel_core'.cases; simp)

lemma 
  cfunc_adv_parametric [transfer_rule]:
    "(rel_core' S E IA IU OA OU ===> S ===> IA ===> rel_spmf (rel_prod OA S)) cfunc_adv cfunc_adv"
  by(rule rel_funI; erule rel_core'.cases; simp)

lemma 
  cfunc_usr_parametric [transfer_rule]:
    "(rel_core' S E IA IU OA OU ===> S ===> IU ===> rel_spmf (rel_prod OU S)) cfunc_usr cfunc_usr"
  by(rule rel_funI; erule rel_core'.cases; simp)

lemma 
  Core_parametric [transfer_rule]:
    "((S ===> E ===> rel_spmf S) ===> (S ===> IA ===> rel_spmf (rel_prod OA S)) ===> (S ===> IU ===> rel_spmf (rel_prod OU S))
   ===> rel_core' S E IA IU OA OU) Core Core"
  by(rule rel_funI)+ simp

lemma 
  case_core_parametric [transfer_rule]:
    "(((S ===> E ===> rel_spmf S) ===> 
        (S ===> IA ===> rel_spmf (rel_prod OA S)) ===> 
        (S ===> IU ===> rel_spmf (rel_prod OU S)) ===> X) ===> 
      rel_core' S E IA IU OA OU ===> X) case_core case_core"
  by(rule rel_funI)+(auto 4 4 split: core.split dest: rel_funD)

lemma 
  corec_core_parametric [transfer_rule]:
    "((X ===> S ===> E ===> rel_spmf S) ===> 
      (X ===> S ===> IA ===> rel_spmf (rel_prod OA S)) ===> 
      (X ===> S ===> IU ===> rel_spmf (rel_prod OU S)) ===> 
      X ===> rel_core' S E IA IU OA OU) corec_core corec_core"
  by(rule rel_funI)+(auto simp add: core.corec dest: rel_funD)

primcorec map_core' ::
   "('event' \<Rightarrow> 'event) \<Rightarrow> 
    ('iadv_core' \<Rightarrow> 'iadv_core) \<Rightarrow>
    ('iusr_core' \<Rightarrow> 'iusr_core) \<Rightarrow> 
    ('oadv_core \<Rightarrow> 'oadv_core') \<Rightarrow> 
    ('ousr_core \<Rightarrow> 'ousr_core') \<Rightarrow>
    ('s_core, 'event, 'iadv_core, 'iusr_core, 'oadv_core, 'ousr_core) core \<Rightarrow> 
    ('s_core, 'event', 'iadv_core', 'iusr_core', 'oadv_core', 'ousr_core') core"
   where
  "cpoke (map_core' e ia iu oa ou core) = (id ---> e ---> id) (cpoke core)"
| "cfunc_adv (map_core' e ia iu oa ou core) = (id ---> ia ---> map_spmf (map_prod oa id)) (cfunc_adv core)"
| "cfunc_usr (map_core' e ia iu oa ou core) = (id ---> iu ---> map_spmf (map_prod ou id)) (cfunc_usr core)"

lemmas map_core'_simps [simp] = map_core'.ctr[where core="Core _ _ _", simplified]

parametric_constant map_core'_parametric[transfer_rule]: map_core'_def

lemma core'_rel_Grp:
  "rel_core' (=) (BNF_Def.Grp UNIV e)\<inverse>\<inverse> (BNF_Def.Grp UNIV ia)\<inverse>\<inverse> (BNF_Def.Grp UNIV iu)\<inverse>\<inverse> (BNF_Def.Grp UNIV oa) (BNF_Def.Grp UNIV ou)
   = BNF_Def.Grp UNIV (map_core' e ia iu oa ou)"
  apply(intro ext)
  subgoal for x y
    apply(cases x; cases y; clarsimp)
    apply(subst (2 4 6) eq_alt_conversep)
    apply(subst (2 3 4) eq_alt)
    apply(simp add: pmf.rel_Grp option.rel_Grp prod.rel_Grp rel_fun_conversep_grp_grp)
    apply(auto simp add: Grp_def spmf.map_id[abs_def] id_def[symmetric])
    done
  done

end

inductive WT_core :: "('iadv, 'oadv) \<I> \<Rightarrow> ('iusr, 'ousr) \<I> \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s, 'event, 'iadv, 'iusr, 'oadv, 'ousr) core \<Rightarrow> bool"
  for \<I>_adv \<I>_usr I core where
  "WT_core \<I>_adv \<I>_usr I core" if
  "\<And>s e s'. \<lbrakk> s' \<in> set_spmf (cpoke core s e); I s \<rbrakk> \<Longrightarrow> I s'"
  "\<And>s x y s'. \<lbrakk> (y, s') \<in> set_spmf (cfunc_adv core s x); x \<in> outs_\<I> \<I>_adv; I s \<rbrakk> \<Longrightarrow> y \<in> responses_\<I> \<I>_adv x \<and> I s'"
  "\<And>s x y s'. \<lbrakk> (y, s') \<in> set_spmf (cfunc_usr core s x); x \<in> outs_\<I> \<I>_usr; I s \<rbrakk> \<Longrightarrow> y \<in> responses_\<I> \<I>_usr x \<and> I s'"

lemma WT_coreD:
  assumes "WT_core \<I>_adv \<I>_usr I core"
  shows WT_coreD_cpoke: "\<And>s e s'. \<lbrakk> s' \<in> set_spmf (cpoke core s e); I s \<rbrakk> \<Longrightarrow> I s'"
    and WT_coreD_cfunc_adv: "\<And>s x y s'. \<lbrakk> (y, s') \<in> set_spmf (cfunc_adv core s x); x \<in> outs_\<I> \<I>_adv; I s \<rbrakk> \<Longrightarrow> y \<in> responses_\<I> \<I>_adv x \<and> I s'"
    and WT_coreD_cfund_usr: "\<And>s x y s'. \<lbrakk> (y, s') \<in> set_spmf (cfunc_usr core s x); x \<in> outs_\<I> \<I>_usr; I s \<rbrakk> \<Longrightarrow> y \<in> responses_\<I> \<I>_usr x \<and> I s'"
  using assms by(auto elim!: WT_core.cases)

lemma WT_coreD_foldl_spmf_cpoke:
  assumes "WT_core \<I>_adv \<I>_usr I core"
    and "s' \<in> set_spmf (foldl_spmf (cpoke core) p es)"
    and "\<forall>s \<in> set_spmf p. I s"
  shows "I s'"
  using assms(2, 3)
  by(induction es arbitrary: p)(fastforce dest: WT_coreD_cpoke[OF assms(1)] simp add: bind_UNION)+

lemma WT_core_trivial:
  assumes adv: "\<And>s. \<I>_adv \<turnstile>c cfunc_adv core s \<surd>"
    and usr: "\<And>s. \<I>_usr \<turnstile>c cfunc_usr core s \<surd>"
  shows "WT_core \<I>_adv \<I>_usr (\<lambda>_. True) core"
  by(rule WT_core.intros)(auto dest: assms[THEN WT_calleeD])

codatatype 
  ('s_rest, 'event, 'iadv_rest, 'iusr_rest, 'oadv_rest, 'ousr_rest, 'more) rest_scheme =
    Rest
      (rinit: "'more")
      (rfunc_adv: "('s_rest, 'event, 'iadv_rest, 'oadv_rest) eoracle")
      (rfunc_usr: "('s_rest, 'event, 'iusr_rest, 'ousr_rest) eoracle")

declare rest_scheme.sel_transfer[transfer_rule del]
declare rest_scheme.ctr_transfer[transfer_rule del]
declare rest_scheme.case_transfer[transfer_rule del]

context 
  includes lifting_syntax 
begin

inductive 
  rel_rest':: "
    ('s_rest \<Rightarrow> 's_rest' \<Rightarrow> bool) \<Rightarrow> 
    ('event \<Rightarrow> 'event' \<Rightarrow> bool) \<Rightarrow> 
    ('iadv_rest \<Rightarrow> 'iadv_rest' \<Rightarrow> bool) \<Rightarrow>
    ('iusr_rest \<Rightarrow> 'iusr_rest' \<Rightarrow> bool) \<Rightarrow> 
    ('oadv_rest \<Rightarrow> 'oadv_rest' \<Rightarrow> bool) \<Rightarrow> 
    ('ousr_rest \<Rightarrow> 'ousr_rest' \<Rightarrow> bool) \<Rightarrow>
    ('more \<Rightarrow> 'more' \<Rightarrow> bool) \<Rightarrow> 
    ('s_rest, 'event, 'iadv_rest, 'iusr_rest, 'oadv_rest, 'ousr_rest, 'more) rest_scheme \<Rightarrow> 
    ('s_rest', 'event', 'iadv_rest', 'iusr_rest', 'oadv_rest', 'ousr_rest', 'more') rest_scheme \<Rightarrow> bool"
  for S E IA IU OA OU M
  where "rel_rest' S E IA IU OA OU M (Rest rinit rfunc_adv rfunc_usr) (Rest rinit' rfunc_adv' rfunc_usr')"
  if 
    "M rinit rinit'" and 
    "(S ===> IA ===> rel_spmf (rel_prod (rel_prod OA (list_all2 E)) S)) rfunc_adv rfunc_adv'" and 
    "(S ===> IU ===> rel_spmf (rel_prod (rel_prod OU (list_all2 E)) S)) rfunc_usr rfunc_usr'"
  for rinit rfunc_adv rfunc_usr

inductive_simps 
  rel_rest'_simps [simp]: 
    "rel_rest' S E IA IU OA OU M (Rest rinit' rfunc_adv' rfunc_usr') (Rest rinit'' rfunc_adv'' rfunc_usr'')"

lemma 
  rel_rest'_eq [relator_eq]:
    "rel_rest' (=) (=) (=) (=) (=) (=) (=) = (=)"
  apply(intro ext)
  subgoal for x y by(cases x; cases y)(auto simp add: fun_eq_iff rel_fun_def relator_eq)
  done

lemma 
  rel_rest'_mono [relator_mono]:
    "rel_rest' S E IA IU OA OU M \<le> rel_rest' S E' IA' IU' OA' OU' M'"
  if "E \<le> E'" "IA' \<le> IA" "IU' \<le> IU" "OA \<le> OA'" "OU \<le> OU'" "M \<le> M'"
  apply(rule predicate2I)
  subgoal for x y
    apply(cases x; cases y; clarsimp; intro conjI)
      apply(erule rel_fun_mono rel_spmf_mono prod.rel_mono[THEN predicate2D, rotated -1] |
        rule impI that order_refl prod.rel_mono list.rel_mono | erule that[THEN predicate2D] | erule rel_spmf_mono | assumption)+
    done
  done

lemma rel_rest'_sel: "rel_rest' S E IA IU OA OU M rest1 rest2"
  if "M (rinit rest1) (rinit rest2)"
  and "(S ===> IA ===> rel_spmf (rel_prod (rel_prod OA (list_all2 E)) S)) (rfunc_adv rest1) (rfunc_adv rest2)" 
  and "(S ===> IU ===> rel_spmf (rel_prod (rel_prod OU (list_all2 E)) S)) (rfunc_usr rest1) (rfunc_usr rest2)"
  using that by(cases rest1; cases rest2) simp

lemma rinit_parametric [transfer_rule]: "(rel_rest' S E IA IU OA OU M ===> M) rinit rinit"
  by(rule rel_funI; erule rel_rest'.cases; simp)

lemma rfunc_adv_parametric [transfer_rule]:
  "(rel_rest' S E IA IU OA OU M ===> S ===> IA ===> rel_spmf (rel_prod (rel_prod OA (list_all2 E)) S)) rfunc_adv rfunc_adv"
  by(rule rel_funI; erule rel_rest'.cases; simp)

lemma rfunc_usr_parametric [transfer_rule]:
  "(rel_rest' S E IA IU OA OU M ===> S ===> IU ===> rel_spmf (rel_prod (rel_prod OU (list_all2 E)) S)) rfunc_usr rfunc_usr"
  by(rule rel_funI; erule rel_rest'.cases; simp)

lemma Rest_parametric [transfer_rule]:
  "(M ===> (S ===> IA ===> rel_spmf (rel_prod (rel_prod OA (list_all2 E)) S))
    ===> (S ===> IU ===> rel_spmf (rel_prod (rel_prod OU (list_all2 E)) S))
   ===> rel_rest' S E IA IU OA OU M) Rest Rest"
  by(rule rel_funI)+ simp

lemma case_rest_scheme_parametric [transfer_rule]:
  "((M ===> 
    (S ===> IA ===> rel_spmf (rel_prod (rel_prod OA (list_all2 E)) S)) ===> 
    (S ===> IU ===> rel_spmf (rel_prod (rel_prod OU (list_all2 E)) S)) ===> X) ===> 
  rel_rest' S E IA IU OA OU M ===> X) case_rest_scheme case_rest_scheme"
  by(rule rel_funI)+(auto 4 4 split: rest_scheme.split dest: rel_funD)

lemma corec_rest_scheme_parametric [transfer_rule]:
    "((X ===> M) ===> 
      (X ===> S ===> IA ===> rel_spmf (rel_prod (rel_prod OA (list_all2 E)) S)) ===> 
      (X ===> S ===> IU ===> rel_spmf (rel_prod (rel_prod OU (list_all2 E)) S)) ===> 
      X ===> rel_rest' S E IA IU OA OU M) corec_rest_scheme corec_rest_scheme"
  by(rule rel_funI)+(auto simp add: rest_scheme.corec dest: rel_funD)

primcorec map_rest' ::
   "('event \<Rightarrow> 'event') \<Rightarrow> 
    ('iadv_rest' \<Rightarrow> 'iadv_rest) \<Rightarrow>
    ('iusr_rest' \<Rightarrow> 'iusr_rest) \<Rightarrow> 
    ('oadv_rest \<Rightarrow> 'oadv_rest') \<Rightarrow> 
    ('ousr_rest \<Rightarrow> 'ousr_rest') \<Rightarrow>
    ('more \<Rightarrow> 'more') \<Rightarrow>
    ('s_rest, 'event, 'iadv_rest, 'iusr_rest, 'oadv_rest, 'ousr_rest, 'more) rest_scheme \<Rightarrow> 
    ('s_rest, 'event', 'iadv_rest', 'iusr_rest', 'oadv_rest', 'ousr_rest', 'more') rest_scheme"
   where
  "rinit (map_rest' e ia iu oa ou m rest) = m (rinit rest)"
| "rfunc_adv (map_rest' e ia iu oa ou m rest) =
   (id ---> ia ---> map_spmf (map_prod (map_prod oa (map e)) id)) (rfunc_adv rest)"
| "rfunc_usr (map_rest' e ia iu oa ou m rest) =
   (id ---> iu ---> map_spmf (map_prod (map_prod ou (map e)) id)) (rfunc_usr rest)"

lemmas map_rest'_simps [simp] = map_rest'.ctr[where rest="Rest _ _ _", simplified]

parametric_constant map_rest'_parametric[transfer_rule]: map_rest'_def

lemma rest'_rel_Grp:
  "rel_rest' (=) (BNF_Def.Grp UNIV e) (BNF_Def.Grp UNIV ia)\<inverse>\<inverse> (BNF_Def.Grp UNIV iu)\<inverse>\<inverse> (BNF_Def.Grp UNIV oa) (BNF_Def.Grp UNIV ou) (BNF_Def.Grp UNIV m)
   = BNF_Def.Grp UNIV (map_rest' e ia iu oa ou m)"
  apply(intro ext)
  subgoal for x y
    apply(cases x; cases y; clarsimp)
    apply(subst (2 4) eq_alt_conversep)
    apply(subst (2 3) eq_alt)
    apply(simp add: pmf.rel_Grp list.rel_Grp option.rel_Grp prod.rel_Grp rel_fun_conversep_grp_grp)
    apply(auto simp add: Grp_def spmf.map_id[abs_def] id_def[symmetric])
    done
  done

end

type_synonym 
  ('s_rest, 'event, 'iadv_rest, 'iusr_rest, 'oadv_rest, 'ousr_rest) rest_wstate =
    "('s_rest, 'event, 'iadv_rest, 'iusr_rest, 'oadv_rest, 'ousr_rest, 's_rest) rest_scheme"

inductive WT_rest :: "('iadv, 'oadv) \<I> \<Rightarrow> ('iusr, 'ousr) \<I> \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s, 'event, 'iadv, 'iusr, 'oadv, 'ousr) rest_wstate \<Rightarrow> bool"
  for \<I>_adv \<I>_usr I rest where
  "WT_rest \<I>_adv \<I>_usr I rest" if
  "\<And>s x y es s'. \<lbrakk> ((y, es), s') \<in> set_spmf (rfunc_adv rest s x); x \<in> outs_\<I> \<I>_adv; I s \<rbrakk> \<Longrightarrow> y \<in> responses_\<I> \<I>_adv x \<and> I s'"
  "\<And>s x y es s'. \<lbrakk> ((y, es), s') \<in> set_spmf (rfunc_usr rest s x); x \<in> outs_\<I> \<I>_usr; I s \<rbrakk> \<Longrightarrow> y \<in> responses_\<I> \<I>_usr x \<and> I s'"
  "I (rinit rest)"

lemma WT_restD:
  assumes "WT_rest \<I>_adv \<I>_usr I rest"
  shows WT_restD_rfunc_adv: "\<And>s x y es s'. \<lbrakk> ((y, es), s') \<in> set_spmf (rfunc_adv rest s x); x \<in> outs_\<I> \<I>_adv; I s \<rbrakk> \<Longrightarrow> y \<in> responses_\<I> \<I>_adv x \<and> I s'"
    and WT_restD_rfunc_usr: "\<And>s x y es s'. \<lbrakk> ((y, es), s') \<in> set_spmf (rfunc_usr rest s x); x \<in> outs_\<I> \<I>_usr; I s \<rbrakk> \<Longrightarrow> y \<in> responses_\<I> \<I>_usr x \<and> I s'"
    and WT_restD_rinit: "I (rinit rest)"
  using assms by(auto elim!: WT_rest.cases)

abbreviation
  fuse_cfunc :: "
    ('o \<Rightarrow> 'x) \<Rightarrow> ('s_core, 'i, 'o) oracle' \<Rightarrow> ('s_core \<times> 's_rest, 'i , 'x) oracle'"
  where
  "fuse_cfunc redirect cfunc state inp  \<equiv> do {
    let handle = map_prod redirect (prod.swap o Pair (snd state));
    (os_cfunc :: 'o \<times> 's_core) \<leftarrow> cfunc (fst state) inp;
    return_spmf (handle os_cfunc)
  }"

abbreviation
  fuse_rfunc :: "
    ('o \<Rightarrow> 'x) \<Rightarrow> ('s_rest, 'e, 'i, 'o) eoracle \<Rightarrow> ('s_core, 'e) handler \<Rightarrow> 
      ('s_core \<times> 's_rest, 'i , 'x) oracle'"
  where
  "fuse_rfunc redirect rfunc notify state inp \<equiv> 
    bind_spmf 
      (rfunc (snd state) inp)
      (\<lambda>((o_rfunc, e_lst), s_rfunc). 
        bind_spmf 
          (foldl_spmf notify (return_spmf (fst state)) e_lst)
          (\<lambda>s_notify. return_spmf (redirect o_rfunc, s_notify, s_rfunc)))
  "


locale fused_resource =
  fixes 
    core :: "('s_core, 'event, 'iadv_core, 'iusr_core, 'oadv_core, 'ousr_core) core" and 
    core_init :: 's_core
begin

fun
  fuse :: "
    ('s_rest, 'event, 'iadv_rest, 'iusr_rest, 'oadv_rest, 'ousr_rest, 'm) rest_scheme \<Rightarrow>
    ('s_core \<times> 's_rest, 
      ('iadv_core + 'iadv_rest) + ('iusr_core + 'iusr_rest),  
      ('oadv_core + 'oadv_rest) + ('ousr_core + 'ousr_rest)) oracle'" 
  where
    "fuse rest state (Inl (Inl iadv_core)) = 
      fuse_cfunc (Inl o Inl) (cfunc_adv core) state iadv_core"
  | "fuse rest state (Inl (Inr iadv_rest)) = 
      fuse_rfunc (Inl o Inr) (rfunc_adv rest) (cpoke core) state iadv_rest"
  | "fuse rest state (Inr (Inl iusr_core)) = 
      fuse_cfunc (Inr o Inl) (cfunc_usr core) state iusr_core"
  | "fuse rest state (Inr (Inr iusr_rest)) = 
      fuse_rfunc (Inr o Inr) (rfunc_usr rest) (cpoke core) state iusr_rest"

case_of_simps fuse_case: fused_resource.fuse.simps

lemma callee_invariant_on_fuse:
  assumes "WT_core \<I>_adv_core \<I>_usr_core I_core core" 
    and "WT_rest \<I>_adv_rest \<I>_usr_rest I_rest rest"
  shows "callee_invariant_on (fuse rest) (pred_prod I_core I_rest) ((\<I>_adv_core \<oplus>\<^sub>\<I> \<I>_adv_rest) \<oplus>\<^sub>\<I> (\<I>_usr_core \<oplus>\<^sub>\<I> \<I>_usr_rest))"
proof(unfold_locales, goal_cases)
  case (1 s x y s')
  then show ?case using assms
    by(cases s; cases s')(auto 4 4 dest: WT_restD WT_coreD WT_coreD_foldl_spmf_cpoke)
next
  case (2 s)
  show ?case
    apply(rule WT_calleeI)
    subgoal for x y s' using 2 assms
      by (cases "(rest, s, x)" rule: fuse.cases) (auto simp add: pred_prod_beta dest: WT_restD WT_coreD )
    done
qed

definition 
  resource :: "
    ('s_rest, 'event, 'iadv_rest, 'iusr_rest, 'oadv_rest, 'ousr_rest) rest_wstate \<Rightarrow>
    (('iadv_core + 'iadv_rest) + ('iusr_core + 'iusr_rest),
      ('oadv_core + 'oadv_rest) + ('ousr_core + 'ousr_rest)) resource" 
  where
    "resource rest = resource_of_oracle (fuse rest) (core_init, rinit rest)"

lemma WT_resource [WT_intro]:
  assumes "WT_core \<I>_adv_core \<I>_usr_core I_core core"
    and "WT_rest \<I>_adv_rest \<I>_usr_rest I_rest rest"
    and "I_core core_init"
  shows "(\<I>_adv_core \<oplus>\<^sub>\<I> \<I>_adv_rest) \<oplus>\<^sub>\<I> (\<I>_usr_core \<oplus>\<^sub>\<I> \<I>_usr_rest) \<turnstile>res resource rest \<surd>"
proof -
  interpret callee_invariant_on "fuse rest" "pred_prod I_core I_rest" "(\<I>_adv_core \<oplus>\<^sub>\<I> \<I>_adv_rest) \<oplus>\<^sub>\<I> (\<I>_usr_core \<oplus>\<^sub>\<I> \<I>_usr_rest)"
    using assms(1,2) by(rule callee_invariant_on_fuse)
  show ?thesis unfolding resource_def
    by(rule WT_resource_of_oracle)(simp add: assms(3) WT_restD_rinit[OF assms(2)])
qed

end

parametric_constant 
  fuse_parametric [transfer_rule]: fused_resource.fuse_case

subsection \<open>More helpful construction functions\<close>

context
  fixes
    core1 :: "('s_core1, 'event1, 'iadv_core1, 'iusr_core1, 'oadv_core1, 'ousr_core1) core" and
    core2 :: "('s_core2, 'event2, 'iadv_core2, 'iusr_core2, 'oadv_core2, 'ousr_core2) core"
begin

primcorec parallel_core :: "
  ('s_core1 \<times> 's_core2, 'event1 + 'event2, 
   'iadv_core1 + 'iadv_core2, 'iusr_core1 + 'iusr_core2,
   'oadv_core1 + 'oadv_core2, 'ousr_core1 + 'ousr_core2) core" 
  where
    "cpoke parallel_core = parallel_handler (cpoke core1) (cpoke core2)"
  | "cfunc_adv parallel_core = parallel_oracle (cfunc_adv core1) (cfunc_adv core2)"
  | "cfunc_usr parallel_core = parallel_oracle (cfunc_usr core1) (cfunc_usr core2)"

end


context
  fixes
    cnv_adv :: "'s_adv \<Rightarrow> 'iadv \<Rightarrow> ('oadv \<times> 's_adv, 'iadv_core, 'oadv_core) gpv" and
    cnv_usr :: "'s_usr \<Rightarrow> 'iusr \<Rightarrow> ('ousr \<times> 's_usr, 'iusr_core, 'ousr_core) gpv" and
    core :: "('s_core, 'event, 'iadv_core, 'iusr_core, 'oadv_core, 'ousr_core) core"
begin

primcorec 
  attach_core :: "(('s_adv \<times> 's_usr) \<times> 's_core, 'event, 'iadv, 'iusr, 'oadv, 'ousr) core"
  where
    "cpoke attach_core = (\<lambda>(s_advusr, s_core) event. 
      map_spmf (\<lambda>s_core'. (s_advusr, s_core')) (cpoke core s_core event))"
  | "cfunc_adv attach_core = (\<lambda>((s_adv, s_usr), s_core) iadv. 
      map_spmf 
        (\<lambda>((oadv, s_adv'), s_core'). (oadv, ((s_adv', s_usr), s_core'))) 
        (exec_gpv (cfunc_adv core) (cnv_adv s_adv iadv) s_core))"
  | "cfunc_usr attach_core = (\<lambda>((s_adv, s_usr), s_core) iusr. 
      map_spmf 
        (\<lambda>((ousr, s_usr'), s_core'). (ousr, ((s_adv, s_usr'), s_core'))) 
        (exec_gpv (cfunc_usr core) (cnv_usr s_usr iusr) s_core))"

end


lemma 
  attach_core_id_oracle_adv: "cfunc_adv (attach_core 1\<^sub>I cnv core) = 
    (\<lambda>(s_cnv, s_core) q. map_spmf (\<lambda>(out, s_core'). (out, s_cnv, s_core')) (cfunc_adv core s_core q))"
  by(simp add: id_oracle_def split_def map_spmf_conv_bind_spmf)

lemma 
  attach_core_id_oracle_usr: "cfunc_usr (attach_core cnv 1\<^sub>I core) = 
    (\<lambda>(s_cnv, s_core) q. map_spmf (\<lambda>(out, s_core'). (out, s_cnv, s_core')) (cfunc_usr core s_core q))"
  by(simp add: id_oracle_def split_def map_spmf_conv_bind_spmf)


context
  fixes
    rest1 :: "('s_rest1, 'event1, 'iadv_rest1, 'iusr_rest1, 'oadv_rest1, 'ousr_rest1, 'more1) rest_scheme" and
    rest2 :: "('s_rest2, 'event2, 'iadv_rest2, 'iusr_rest2, 'oadv_rest2, 'ousr_rest2, 'more2) rest_scheme"
begin

primcorec parallel_rest :: "
    ('s_rest1 \<times> 's_rest2, 'event1 + 'event2, 'iadv_rest1 + 'iadv_rest2, 'iusr_rest1 + 'iusr_rest2, 
     'oadv_rest1 + 'oadv_rest2, 'ousr_rest1 + 'ousr_rest2, 'more1 \<times> 'more2) rest_scheme" 
  where
    "rinit parallel_rest = (rinit rest1, rinit rest2)"
  | "rfunc_adv parallel_rest = parallel_eoracle (rfunc_adv rest1) (rfunc_adv rest2)"
  | "rfunc_usr parallel_rest = parallel_eoracle (rfunc_usr rest1) (rfunc_usr rest2)"

end

lemma WT_parallel_rest [WT_intro]:
  "WT_rest (\<I>_adv1 \<oplus>\<^sub>\<I> \<I>_adv2) (\<I>_usr1 \<oplus>\<^sub>\<I> \<I>_usr2) (pred_prod I1 I2) (parallel_rest rest1 rest2)"
  if "WT_rest \<I>_adv1 \<I>_usr1 I1 rest1"
  and "WT_rest \<I>_adv2 \<I>_usr2 I2 rest2"
  by(rule WT_rest.intros)
    (auto 4 3 simp add: parallel_eoracle_def simp add: that[THEN WT_restD_rinit] dest: that[THEN WT_restD_rfunc_adv] that[THEN WT_restD_rfunc_usr])

context
  fixes
    cnv_adv :: "'s_adv \<Rightarrow> 'iadv \<Rightarrow> ('oadv \<times> 's_adv, 'iadv_rest, 'oadv_rest) gpv" and
    cnv_usr :: "'s_usr \<Rightarrow> 'iusr \<Rightarrow> ('ousr \<times> 's_usr, 'iusr_rest, 'ousr_rest) gpv" and
    f_init :: "'more \<Rightarrow> 'more'" and
    rest :: "('s_rest, 'event, 'iadv_rest, 'iusr_rest, 'oadv_rest, 'ousr_rest, 'more) rest_scheme"
begin

primcorec 
  attach_rest :: "
    (('s_adv \<times> 's_usr) \<times> 's_rest, 'event, 'iadv, 'iusr, 'oadv, 'ousr, 'more') rest_scheme"
  where
    "rinit attach_rest = f_init (rinit rest)"
  | "rfunc_adv attach_rest = (\<lambda>((s_adv, s_usr), s_rest) iadv.
      let orc_of = \<lambda>orc (s, es) q. map_spmf (\<lambda> ((out, e), s'). (out, s', es @ e)) (orc s q) in
      let eorc_of = \<lambda>((oadv, s_adv'), (s_rest', es)). ((oadv, es), ((s_adv', s_usr), s_rest')) in
      map_spmf eorc_of (exec_gpv (orc_of (rfunc_adv rest)) (cnv_adv s_adv iadv) (s_rest, [])))"
  | "rfunc_usr attach_rest = (\<lambda>((s_adv, s_usr), s_rest) iusr. 
      let orc_of = \<lambda>orc (s, es) q. map_spmf (\<lambda> ((out, e), s'). (out, s', es @ e)) (orc s q) in
      let eorc_of = \<lambda>((ousr, s_usr'), (s_rest', es)). ((ousr, es), ((s_adv, s_usr'), s_rest')) in
      map_spmf eorc_of (exec_gpv (orc_of (rfunc_usr rest)) (cnv_usr s_usr iusr) (s_rest, [])))"
  
end


lemma 
  attach_rest_id_oracle_adv: "rfunc_adv (attach_rest 1\<^sub>I cnv f_init rest) = 
    (\<lambda>(s_cnv, s_core) q. map_spmf (\<lambda>(out, s_core'). (out, s_cnv, s_core')) (rfunc_adv rest s_core q))"
  by(simp add: id_oracle_def split_def map_spmf_conv_bind_spmf fun_eq_iff)  

lemma
  attach_rest_id_oracle_usr: "rfunc_usr (attach_rest cnv 1\<^sub>I f_init rest) = 
    (\<lambda>(s_cnv, s_core) q. map_spmf (\<lambda>(out, s_core'). (out, s_cnv, s_core')) (rfunc_usr rest s_core q))"
  by(simp add: id_oracle_def split_def map_spmf_conv_bind_spmf)  



section \<open>Traces\<close>

type_synonym ('event, 'iadv_core, 'iusr_core, 'oadv_core, 'ousr_core) trace_core =
  "('event + 'iadv_core \<times> 'oadv_core + 'iusr_core \<times> 'ousr_core) list 
  \<Rightarrow> ('event \<Rightarrow> real)
  \<times> ('iadv_core \<Rightarrow> 'oadv_core spmf) 
  \<times> ('iusr_core \<Rightarrow> 'ousr_core spmf)"

context 
  fixes core :: "('s_core, 'event, 'iadv_core, 'iusr_core, 'oadv_core, 'ousr_core) core"
begin

primrec trace_core' :: "'s_core spmf \<Rightarrow> ('event, 'iadv_core, 'iusr_core, 'oadv_core, 'ousr_core) trace_core" where
  "trace_core' S [] = 
   (\<lambda>e. weight_spmf' (bind_spmf S (\<lambda>s. cpoke core s e)),
    \<lambda>ia. bind_spmf S (\<lambda>s. map_spmf fst (cfunc_adv core s ia)),
    \<lambda>iu. bind_spmf S (\<lambda>s. map_spmf fst (cfunc_usr core s iu)))"
| "trace_core' S (obs # tr) = (case obs of
     Inl e \<Rightarrow> trace_core' (mk_lossless (bind_spmf S (\<lambda>s. cpoke core s e))) tr
   | Inr (Inl (ia, oa)) \<Rightarrow> trace_core' (cond_spmf_fst (bind_spmf S (\<lambda>s. cfunc_adv core s ia)) oa) tr
   | Inr (Inr (iu, ou)) \<Rightarrow> trace_core' (cond_spmf_fst (bind_spmf S (\<lambda>s. cfunc_usr core s iu)) ou) tr
   )"

end

declare trace_core'.simps [simp del]
case_of_simps trace_core'_unfold: trace_core'.simps[unfolded weight_spmf'_def]
simps_of_case trace_core'_simps [simp]: trace_core'_unfold

context includes lifting_syntax begin

lemma trace_core'_parametric [transfer_rule]:
  "(rel_core' S E IA IU (=) (=) ===>
      rel_spmf S ===>
      list_all2 (rel_sum E (rel_sum (rel_prod IA (=)) (rel_prod IU (=)))) ===>
      rel_prod (E ===> (=)) (rel_prod (IA ===> (=)) (IU ===> (=))))
      trace_core' trace_core'"
  unfolding trace_core'_def by transfer_prover

definition trace_core_eq 
  :: "('s_core, 'event, 'iadv_core, 'iusr_core, 'oadv_core, 'ousr_core) core
  \<Rightarrow> ('s_core', 'event, 'iadv_core, 'iusr_core, 'oadv_core, 'ousr_core) core
  \<Rightarrow> 'event set \<Rightarrow> 'iadv_core set \<Rightarrow> 'iusr_core set
  \<Rightarrow> 's_core spmf \<Rightarrow> 's_core' spmf \<Rightarrow> bool" where
  "trace_core_eq core1 core2 E IA IU p q \<longleftrightarrow>
  (\<forall>tr. set tr \<subseteq> E <+> (IA \<times> UNIV) <+> (IU \<times> UNIV) \<longrightarrow> 
   rel_prod (eq_onp (\<lambda>e. e \<in> E) ===> (=)) (rel_prod (eq_onp (\<lambda>ia. ia \<in> IA) ===> (=)) (eq_onp (\<lambda>iu. iu \<in> IU) ===> (=)))
     (trace_core' core1 p tr) (trace_core' core2 q tr))"

end

lemma trace_core_eqD:
  assumes "trace_core_eq core1 core2 E IA IU p q"
    and "set tr \<subseteq> E <+> (IA \<times> UNIV) <+> (IU \<times> UNIV)"
  shows trace_core_eqD_cpoke: 
      "e \<in> E \<Longrightarrow> fst (trace_core' core1 p tr) e = fst (trace_core' core2 q tr) e"
    and trace_core_eqD_cfunc_adv: 
      "ia \<in> IA \<Longrightarrow> fst (snd (trace_core' core1 p tr)) ia = fst (snd (trace_core' core2 q tr)) ia"
    and trace_core_eqD_cfunc_usr:
      "iu \<in> IU \<Longrightarrow> snd (snd (trace_core' core1 p tr)) iu = snd (snd (trace_core' core2 q tr)) iu"
  using assms by(auto simp add: trace_core_eq_def rel_fun_def eq_onp_def rel_prod_sel)

lemma trace_core_eqI:
  assumes "\<And>tr e. \<lbrakk> set tr \<subseteq> E <+> (IA \<times> UNIV) <+> (IU \<times> UNIV); e \<in> E \<rbrakk> 
     \<Longrightarrow> fst (trace_core' core1 p tr) e = fst (trace_core' core2 q tr) e"
    and "\<And>tr ia. \<lbrakk> set tr \<subseteq> E <+> (IA \<times> UNIV) <+> (IU \<times> UNIV); ia \<in> IA \<rbrakk>
     \<Longrightarrow> fst (snd (trace_core' core1 p tr)) ia = fst (snd (trace_core' core2 q tr)) ia"
    and "\<And>tr iu. \<lbrakk> set tr \<subseteq> E <+> (IA \<times> UNIV) <+> (IU \<times> UNIV); iu \<in> IU \<rbrakk>
     \<Longrightarrow> snd (snd (trace_core' core1 p tr)) iu = snd (snd (trace_core' core2 q tr)) iu"
  shows "trace_core_eq core1 core2 E IA IU p q"
  using assms by(auto simp add: trace_core_eq_def rel_fun_def eq_onp_def rel_prod_sel)

lemma trace_core_return_pmf_None [simp]:
  "trace_core' core (return_pmf None) tr = (\<lambda>_. 0, \<lambda>_. return_pmf None, \<lambda>_. return_pmf None)"
  by(induction tr)(simp_all add: trace_core'.simps split: sum.split)

lemma rel_core'_into_trace_core_eq: "trace_core_eq core core' E IA IU p q" 
  if "rel_core' S (eq_onp (\<lambda>e. e \<in> E)) (eq_onp (\<lambda>ia. ia \<in> IA)) (eq_onp (\<lambda>iu. iu \<in> IU)) (=) (=) core core'"
     "rel_spmf S p q"
  using trace_core'_parametric[THEN rel_funD, THEN rel_funD, OF that]
  unfolding trace_core_eq_def
  apply(intro strip)
  subgoal for tr
    apply(simp add: eq_onp_True[symmetric] prod.rel_eq_onp sum.rel_eq_onp list.rel_eq_onp)
    apply(auto 4 3 simp add: eq_onp_def list_all_iff dest: rel_funD[where x=tr and y=tr])
    done
  done

lemma trace_core_eq_simI:
  fixes core1 :: "('s_core, 'event, 'iadv_core, 'iusr_core, 'oadv_core, 'ousr_core) core"
    and core2 :: "('s_core', 'event, 'iadv_core, 'iusr_core, 'oadv_core, 'ousr_core) core"
    and S :: "'s_core spmf \<Rightarrow> 's_core' spmf \<Rightarrow> bool"
  assumes start: "S p q"
    and step_cpoke: "\<And>p q e. \<lbrakk> S p q; e \<in> E \<rbrakk> \<Longrightarrow> 
      weight_spmf (bind_spmf p (\<lambda>s. cpoke core1 s e)) = weight_spmf (bind_spmf q (\<lambda>s. cpoke core2 s e))"
    and sim_cpoke: "\<And>p q e. \<lbrakk> S p q; e \<in> E \<rbrakk> \<Longrightarrow> 
      S (mk_lossless (bind_spmf p (\<lambda>s. cpoke core1 s e))) (mk_lossless (bind_spmf q (\<lambda>s. cpoke core2 s e)))"
    and step_cfunc_adv: "\<And>p q ia. \<lbrakk> S p q; ia \<in> IA \<rbrakk> \<Longrightarrow> 
      bind_spmf p (\<lambda>s1. map_spmf fst (cfunc_adv core1 s1 ia)) = bind_spmf q (\<lambda>s2. map_spmf fst (cfunc_adv core2 s2 ia))"
    and sim_cfunc_adv: "\<And>p q ia s1 s2 s1' s2' oa. \<lbrakk> S p q; ia \<in> IA; 
      s1 \<in> set_spmf p; s2 \<in> set_spmf q; (oa, s1') \<in> set_spmf (cfunc_adv core1 s1 ia); (oa, s2') \<in> set_spmf (cfunc_adv core2 s2 ia) \<rbrakk>
      \<Longrightarrow> S (cond_spmf_fst (bind_spmf p (\<lambda>s1. cfunc_adv core1 s1 ia)) oa) (cond_spmf_fst (bind_spmf q (\<lambda>s2. cfunc_adv core2 s2 ia)) oa)"
    and step_cfunc_usr: "\<And>p q iu. \<lbrakk> S p q; iu \<in> IU \<rbrakk> \<Longrightarrow> 
      bind_spmf p (\<lambda>s1. map_spmf fst (cfunc_usr core1 s1 iu)) = bind_spmf q (\<lambda>s2. map_spmf fst (cfunc_usr core2 s2 iu))"
    and sim_cfunc_usr: "\<And>p q iu s1 s2 s1' s2' ou. \<lbrakk> S p q; iu \<in> IU; 
      s1 \<in> set_spmf p; s2 \<in> set_spmf q; (ou, s1') \<in> set_spmf (cfunc_usr core1 s1 iu); (ou, s2') \<in> set_spmf (cfunc_usr core2 s2 iu) \<rbrakk>
      \<Longrightarrow> S (cond_spmf_fst (bind_spmf p (\<lambda>s1. cfunc_usr core1 s1 iu)) ou) (cond_spmf_fst (bind_spmf q (\<lambda>s2. cfunc_usr core2 s2 iu)) ou)"
  shows "trace_core_eq core1 core2 E IA IU p q"
proof(rule trace_core_eqI)
  fix tr :: " ('event + 'iadv_core \<times> 'oadv_core + 'iusr_core \<times> 'ousr_core) list"
  assume "set tr \<subseteq> E <+> IA \<times> UNIV <+> IU \<times> UNIV"
  then have "(\<forall>e\<in>E. fst (trace_core' core1 p tr) e = fst (trace_core' core2 q tr) e) \<and>
     (\<forall>ia\<in>IA. fst (snd (trace_core' core1 p tr)) ia = fst (snd (trace_core' core2 q tr)) ia) \<and>
     (\<forall>iu\<in>IU. snd (snd (trace_core' core1 p tr)) iu = snd (snd (trace_core' core2 q tr)) iu)"
    using start
  proof(induction tr arbitrary: p q)
    case Nil
    then show ?case by(simp add: step_cpoke step_cfunc_adv step_cfunc_usr)
  next
    case (Cons a tr)
    from Cons.prems(1) have tr: "set tr \<subseteq> E <+> IA \<times> UNIV <+> IU \<times> UNIV" by simp
    from Cons.prems(1)
    consider (cpoke) e where "a = Inl e" "e \<in> E"
      | (cfunc_adv) ia oa where "a = Inr (Inl (ia, oa))" "ia \<in> IA"
      | (cfunc_usr) iu ou where "a = Inr (Inr (iu, ou))" "iu \<in> IU" by auto
    then show ?case
    proof cases
      case cpoke
      then show ?thesis using tr Cons.prems(2) by(auto simp add: sim_cpoke intro!: Cons.IH)
    next
      case cfunc_adv
      let ?p = "bind_spmf p (\<lambda>s1. cfunc_adv core1 s1 ia)"
      let ?q = "bind_spmf q (\<lambda>s2. cfunc_adv core2 s2 ia)"
      show ?thesis
      proof(cases "oa \<in> fst ` set_spmf ?p")
        case True
        with step_cfunc_adv[OF Cons.prems(2) cfunc_adv(2), THEN arg_cong[where f=set_spmf]]
        have "oa \<in> fst ` set_spmf ?q"
          unfolding set_map_spmf[symmetric] by(simp only: map_bind_spmf o_def)
        then show ?thesis using True Cons.prems cfunc_adv
          by(clarsimp)(rule Cons.IH; blast intro: sim_cfunc_adv)
      next
        case False
        hence "cond_spmf_fst ?p oa = return_pmf None" by simp
        moreover
        from step_cfunc_adv[OF Cons.prems(2) cfunc_adv(2), THEN arg_cong[where f=set_spmf]] False
        have oa': "oa \<notin> fst ` set_spmf ?q"
          unfolding set_map_spmf[symmetric] by(simp only: map_bind_spmf o_def) simp
        hence "cond_spmf_fst ?q oa = return_pmf None" by simp
        ultimately show ?thesis using cfunc_adv by(simp del: cond_spmf_fst_eq_return_None)
      qed
    next
      case cfunc_usr
      let ?p = "bind_spmf p (\<lambda>s1. cfunc_usr core1 s1 iu)"
      let ?q = "bind_spmf q (\<lambda>s2. cfunc_usr core2 s2 iu)"
      show ?thesis
      proof(cases "ou \<in> fst ` set_spmf ?p")
        case True
        with step_cfunc_usr[OF Cons.prems(2) cfunc_usr(2), THEN arg_cong[where f=set_spmf]]
        have "ou \<in> fst ` set_spmf ?q"
          unfolding set_map_spmf[symmetric] by(simp only: map_bind_spmf o_def)
        then show ?thesis using True Cons.prems cfunc_usr
          by(clarsimp)(rule Cons.IH; blast intro: sim_cfunc_usr)
      next
        case False
        hence "cond_spmf_fst ?p ou = return_pmf None" by simp
        moreover
        from step_cfunc_usr[OF Cons.prems(2) cfunc_usr(2), THEN arg_cong[where f=set_spmf]] False
        have oa': "ou \<notin> fst ` set_spmf ?q"
          unfolding set_map_spmf[symmetric] by(simp only: map_bind_spmf o_def) simp
        hence "cond_spmf_fst ?q ou = return_pmf None" by simp
        ultimately show ?thesis using cfunc_usr by(simp del: cond_spmf_fst_eq_return_None)
      qed
    qed
  qed
  then show "e \<in> E \<Longrightarrow> fst (trace_core' core1 p tr) e = fst (trace_core' core2 q tr) e"
    and "ia \<in> IA \<Longrightarrow> fst (snd (trace_core' core1 p tr)) ia = fst (snd (trace_core' core2 q tr)) ia"
    and "iu \<in> IU \<Longrightarrow> snd (snd (trace_core' core1 p tr)) iu = snd (snd (trace_core' core2 q tr)) iu"
    for e ia iu by blast+
qed

context 
  fixes core :: "('s_core, 'event, 'iadv_core, 'iusr_core, 'oadv_core, 'ousr_core) core"
begin

fun trace_core_aux 
  :: "'s_core spmf \<Rightarrow> ('event + 'iadv_core \<times> 'oadv_core + 'iusr_core \<times> 'ousr_core) list \<Rightarrow> 's_core spmf" where
  "trace_core_aux p [] = p"
| "trace_core_aux p (Inl e # tr) = trace_core_aux (mk_lossless (bind_spmf p (\<lambda>s. cpoke core s e))) tr"
| "trace_core_aux p (Inr (Inl (ia, oa)) # tr) = trace_core_aux (cond_spmf_fst (bind_spmf p (\<lambda>s. cfunc_adv core s ia)) oa) tr"
| "trace_core_aux p (Inr (Inr (iu, ou)) # tr) = trace_core_aux (cond_spmf_fst (bind_spmf p (\<lambda>s. cfunc_usr core s iu)) ou) tr"

end

lemma trace_core_conv_trace_core_aux:
  "trace_core' core p tr = 
   (\<lambda>e. weight_spmf (bind_spmf (trace_core_aux core p tr) (\<lambda>s. cpoke core s e)),
    \<lambda>ia. bind_spmf (trace_core_aux core p tr) (\<lambda>s. map_spmf fst (cfunc_adv core s ia)),
    \<lambda>iu. bind_spmf (trace_core_aux core p tr) (\<lambda>s. map_spmf fst (cfunc_usr core s iu)))"
  by(induction p tr rule: trace_core_aux.induct) simp_all

lemma trace_core_aux_append:
  "trace_core_aux core p (tr @ tr') = trace_core_aux core (trace_core_aux core p tr) tr'"
  by(induction p tr rule: trace_core_aux.induct) auto

inductive trace_core_closure 
  :: "('s_core, 'event, 'iadv_core, 'iusr_core, 'oadv_core, 'ousr_core) core
  \<Rightarrow> ('s_core', 'event, 'iadv_core, 'iusr_core, 'oadv_core, 'ousr_core) core
  \<Rightarrow> 'event set \<Rightarrow> 'iadv_core set \<Rightarrow> 'iusr_core set
  \<Rightarrow> 's_core spmf \<Rightarrow> 's_core' spmf \<Rightarrow> 's_core spmf \<Rightarrow> 's_core' spmf \<Rightarrow> bool"
  for core1 core2 E IA IU p q where
  "trace_core_closure core1 core2 E IA IU p q (trace_core_aux core1 p tr) (trace_core_aux core2 q tr)"
  if "set tr \<subseteq> E <+> IA \<times> UNIV <+> IU \<times> UNIV"

lemma trace_core_closure_start: "trace_core_closure core1 core2 E IA IU p q p q"
  by(simp add: trace_core_closure.simps exI[where x="[]"])

lemma trace_core_closure_step:
  assumes "trace_core_eq core1 core2 E IA IU p q"
    and "trace_core_closure core1 core2 E IA IU p q p' q'"
  shows trace_core_closure_step_cpoke:
    "e \<in> E \<Longrightarrow> weight_spmf (bind_spmf p' (\<lambda>s. cpoke core1 s e)) = weight_spmf (bind_spmf q' (\<lambda>s. cpoke core2 s e))"
    (is "PROP ?thesis1")
    and trace_core_closure_step_cfunc_adv: 
    "ia \<in> IA \<Longrightarrow> bind_spmf p' (\<lambda>s1. map_spmf fst (cfunc_adv core1 s1 ia)) = bind_spmf q' (\<lambda>s2. map_spmf fst (cfunc_adv core2 s2 ia))"
    (is "PROP ?thesis2")
    and trace_core_closure_step_cfunc_usr:
    "iu \<in> IU \<Longrightarrow> bind_spmf p' (\<lambda>s1. map_spmf fst (cfunc_usr core1 s1 iu)) = bind_spmf q' (\<lambda>s2. map_spmf fst (cfunc_usr core2 s2 iu))"
    (is "PROP ?thesis3")
proof -
  from assms(2) obtain tr where p: "p' = trace_core_aux core1 p tr"
    and q: "q' = trace_core_aux core2 q tr"
    and tr: "set tr \<subseteq> E <+> IA \<times> UNIV <+> IU \<times> UNIV" by cases
  from trace_core_eqD[OF assms(1) tr] p q
  show "PROP ?thesis1" and "PROP ?thesis2" "PROP ?thesis3"
    by(simp_all add: trace_core_conv_trace_core_aux)
qed

lemma trace_core_closure_sim:
  fixes core1 core2 E IA IU p q
  defines "S \<equiv> trace_core_closure core1 core2 E IA IU p q"
  assumes "S p' q'"
  shows trace_core_closure_sim_cpoke:
    "e \<in> E \<Longrightarrow> S (mk_lossless (bind_spmf p' (\<lambda>s. cpoke core1 s e))) (mk_lossless (bind_spmf q' (\<lambda>s. cpoke core2 s e)))"
    (is "PROP ?thesis1")
    and trace_core_closure_sim_cfunc_adv: "ia \<in> IA 
    \<Longrightarrow> S (cond_spmf_fst (bind_spmf p' (\<lambda>s1. cfunc_adv core1 s1 ia)) oa) 
          (cond_spmf_fst (bind_spmf q' (\<lambda>s2. cfunc_adv core2 s2 ia)) oa)"
    (is "PROP ?thesis2")
    and trace_core_closure_sim_cfunc_usr: "iu \<in> IU 
    \<Longrightarrow> S (cond_spmf_fst (bind_spmf p' (\<lambda>s1. cfunc_usr core1 s1 iu)) ou)
          (cond_spmf_fst (bind_spmf q' (\<lambda>s2. cfunc_usr core2 s2 iu)) ou)"
    (is "PROP ?thesis3")
proof -
  from assms(2) obtain tr where p: "p' = trace_core_aux core1 p tr"
    and q: "q' = trace_core_aux core2 q tr"
    and tr: "set tr \<subseteq> E <+> IA \<times> UNIV <+> IU \<times> UNIV" unfolding S_def by cases
  show "PROP ?thesis1" using p q tr
    by(auto simp add: S_def trace_core_closure.simps trace_core_aux_append intro!: exI[where x="tr @ [Inl _]"])
  show "PROP ?thesis2" using p q tr
    by(auto simp add: S_def trace_core_closure.simps trace_core_aux_append intro!: exI[where x="tr @ [Inr (Inl (_, _))]"])
  show "PROP ?thesis3" using p q tr
    by(auto simp add: S_def trace_core_closure.simps trace_core_aux_append intro!: exI[where x="tr @ [Inr (Inr (_, _))]"])
qed

proposition trace_core_eq_complete:
  assumes "trace_core_eq core1 core2 E IA IU p q"
  obtains S
  where "S p q"
    and "\<And>p q e. \<lbrakk> S p q; e \<in> E \<rbrakk> \<Longrightarrow> 
      weight_spmf (bind_spmf p (\<lambda>s. cpoke core1 s e)) = weight_spmf (bind_spmf q (\<lambda>s. cpoke core2 s e))"
    and "\<And>p q e. \<lbrakk> S p q; e \<in> E \<rbrakk> \<Longrightarrow> 
      S (mk_lossless (bind_spmf p (\<lambda>s. cpoke core1 s e))) (mk_lossless (bind_spmf q (\<lambda>s. cpoke core2 s e)))"
    and "\<And>p q ia. \<lbrakk> S p q; ia \<in> IA \<rbrakk> \<Longrightarrow> 
      bind_spmf p (\<lambda>s1. map_spmf fst (cfunc_adv core1 s1 ia)) = bind_spmf q (\<lambda>s2. map_spmf fst (cfunc_adv core2 s2 ia))"
    and "\<And>p q ia oa. \<lbrakk> S p q; ia \<in> IA \<rbrakk>
      \<Longrightarrow> S (cond_spmf_fst (bind_spmf p (\<lambda>s1. cfunc_adv core1 s1 ia)) oa) (cond_spmf_fst (bind_spmf q (\<lambda>s2. cfunc_adv core2 s2 ia)) oa)"
    and "\<And>p q iu. \<lbrakk> S p q; iu \<in> IU \<rbrakk> \<Longrightarrow> 
      bind_spmf p (\<lambda>s1. map_spmf fst (cfunc_usr core1 s1 iu)) = bind_spmf q (\<lambda>s2. map_spmf fst (cfunc_usr core2 s2 iu))"
    and "\<And>p q iu ou. \<lbrakk> S p q; iu \<in> IU \<rbrakk>
      \<Longrightarrow> S (cond_spmf_fst (bind_spmf p (\<lambda>s1. cfunc_usr core1 s1 iu)) ou) (cond_spmf_fst (bind_spmf q (\<lambda>s2. cfunc_usr core2 s2 iu)) ou)"
proof -
  show thesis
    by(rule that[where S="trace_core_closure core1 core2 E IA IU p q"])
      (auto intro: trace_core_closure_start trace_core_closure_step[OF assms] trace_core_closure_sim (* trace_core_closure_weight[OF assms] *))
qed



type_synonym ('event, 'iadv_rest, 'iusr_rest, 'oadv_rest, 'ousr_rest) trace_rest =
  "('iadv_rest \<times> 'oadv_rest \<times> 'event list + 'iusr_rest \<times> 'ousr_rest \<times> 'event list) list
  \<Rightarrow> ('iadv_rest \<Rightarrow> ('oadv_rest \<times> 'event list) spmf) 
  \<times> ('iusr_rest \<Rightarrow> ('ousr_rest \<times> 'event list) spmf)"

context
  fixes rest :: "('s_rest, 'event, 'iadv_rest, 'iusr_rest, 'oadv_rest, 'ousr_rest, 'more) rest_scheme"
begin

primrec trace_rest' :: "'s_rest spmf \<Rightarrow> ('event, 'iadv_rest, 'iusr_rest, 'oadv_rest, 'ousr_rest) trace_rest" where
  "trace_rest' S [] =
  (\<lambda>ia. bind_spmf S (\<lambda>s. map_spmf fst (rfunc_adv rest s ia)),
   \<lambda>iu. bind_spmf S (\<lambda>s. map_spmf fst (rfunc_usr rest s iu)))"
| "trace_rest' S (obs # tr) = (case obs of
     Inl (ia, oa) \<Rightarrow> trace_rest' (cond_spmf_fst (bind_spmf S (\<lambda>s. rfunc_adv rest s ia)) oa) tr
   | Inr (iu, ou) \<Rightarrow> trace_rest' (cond_spmf_fst (bind_spmf S (\<lambda>s. rfunc_usr rest s iu)) ou) tr)"

end

declare trace_rest'.simps [simp del]
case_of_simps trace_rest'_unfold: trace_rest'.simps
simps_of_case trace_rest'_simps [simp]: trace_rest'_unfold

context includes lifting_syntax begin

lemma trace_rest'_parametric [transfer_rule]:
  "(rel_rest' S (=) IA IU (=) (=) M ===> rel_spmf S ===>
      list_all2 (rel_sum (rel_prod IA (=)) (rel_prod IU (=))) ===>
      rel_prod (IA ===> (=)) (IU ===> (=)))
      trace_rest' trace_rest'"
  unfolding trace_rest'_def by transfer_prover

definition trace_rest_eq
  :: "('s_rest, 'event, 'iadv_rest, 'iusr_rest, 'oadv_rest, 'ousr_rest, 'more1) rest_scheme
  \<Rightarrow> ('s_rest', 'event, 'iadv_rest, 'iusr_rest, 'oadv_rest, 'ousr_rest, 'more2) rest_scheme
  \<Rightarrow> 'iadv_rest set \<Rightarrow> 'iusr_rest set
  \<Rightarrow> 's_rest spmf \<Rightarrow> 's_rest' spmf \<Rightarrow> bool" where
  "trace_rest_eq rest1 rest2 IA IU p q \<longleftrightarrow>
  (\<forall>tr. set tr \<subseteq> (IA \<times> UNIV) <+> (IU \<times> UNIV) \<longrightarrow>
   rel_prod (eq_onp (\<lambda>ia. ia \<in> IA) ===> (=)) (eq_onp (\<lambda>iu. iu \<in> IU) ===> (=))
     (trace_rest' rest1 p tr) (trace_rest' rest2 q tr))"

end

lemma trace_rest_eqD:
  assumes "trace_rest_eq rest1 rest2 IA IU p q"
    and "set tr \<subseteq> (IA \<times> UNIV) <+> (IU \<times> UNIV)"
  shows trace_rest_eqD_rfunc_adv:
     "ia \<in> IA \<Longrightarrow> fst (trace_rest' rest1 p tr) ia = fst (trace_rest' rest2 q tr) ia"
    and trace_rest_eqD_rfunc_usr:
     "iu \<in> IU \<Longrightarrow> snd (trace_rest' rest1 p tr) iu = snd (trace_rest' rest2 q tr) iu"
  using assms by(auto simp add: trace_rest_eq_def rel_fun_def rel_prod_sel eq_onp_def)

lemma trace_rest_eqI:
  assumes "\<And>tr ia. \<lbrakk> set tr \<subseteq> (IA \<times> UNIV) <+> (IU \<times> UNIV); ia \<in> IA \<rbrakk>
     \<Longrightarrow> fst (trace_rest' rest1 p tr) ia = fst (trace_rest' rest2 q tr) ia"
    and "\<And>tr iu. \<lbrakk> set tr \<subseteq> (IA \<times> UNIV) <+> (IU \<times> UNIV); iu \<in> IU \<rbrakk>
      \<Longrightarrow> snd (trace_rest' rest1 p tr) iu = snd (trace_rest' rest2 q tr) iu"
  shows "trace_rest_eq rest1 rest2 IA IU p q"
  using assms by(auto simp add: trace_rest_eq_def rel_fun_def eq_onp_def rel_prod_sel)

lemma trace_rest_return_pmf_None [simp]:
  "trace_rest' rest (return_pmf None) tr = (\<lambda>_. return_pmf None, \<lambda>_. return_pmf None)"
  by(induction tr)(simp_all add: trace_rest'.simps split: sum.split)

lemma rel_rest'_into_trace_rest_eq: "trace_rest_eq rest rest' IA IU p q" 
  if "rel_rest' S (=) (eq_onp (\<lambda>ia. ia \<in> IA)) (eq_onp (\<lambda>iu. iu \<in> IU)) (=) (=) M rest rest'"
     "rel_spmf S p q"
  using trace_rest'_parametric[THEN rel_funD, THEN rel_funD, OF that]
  unfolding trace_rest_eq_def
  apply(intro strip)
  subgoal for tr
    apply(simp add: eq_onp_True[symmetric] prod.rel_eq_onp sum.rel_eq_onp list.rel_eq_onp)
    apply(auto 4 3 simp add: eq_onp_def list_all_iff dest: rel_funD[where x=tr and y=tr])
    done
  done

lemma trace_rest_eq_simI:
  fixes rest1 :: "('s_rest, 'event, 'iadv_rest, 'iusr_rest, 'oadv_rest, 'ousr_rest, 'more) rest_scheme"
    and rest2 :: "('s_rest', 'event, 'iadv_rest, 'iusr_rest, 'oadv_rest, 'ousr_rest, 'more) rest_scheme"
    and S :: "'s_rest spmf \<Rightarrow> 's_rest' spmf \<Rightarrow> bool"
  assumes start: "S p q"
    and step_rfunc_adv: "\<And>p q ia. \<lbrakk> S p q; ia \<in> IA \<rbrakk> \<Longrightarrow> 
      bind_spmf p (\<lambda>s1. map_spmf fst (rfunc_adv rest1 s1 ia)) = bind_spmf q (\<lambda>s2. map_spmf fst (rfunc_adv rest2 s2 ia))"
    and sim_rfunc_adv: "\<And>p q ia s1 s2 s1' s2' oa. \<lbrakk> S p q; ia \<in> IA; 
      s1 \<in> set_spmf p; s2 \<in> set_spmf q; (oa, s1') \<in> set_spmf (rfunc_adv rest1 s1 ia); (oa, s2') \<in> set_spmf (rfunc_adv rest2 s2 ia) \<rbrakk>
      \<Longrightarrow> S (cond_spmf_fst (bind_spmf p (\<lambda>s1. rfunc_adv rest1 s1 ia)) oa) (cond_spmf_fst (bind_spmf q (\<lambda>s2. rfunc_adv rest2 s2 ia)) oa)"
    and step_rfunc_usr: "\<And>p q iu. \<lbrakk> S p q; iu \<in> IU \<rbrakk> \<Longrightarrow> 
      bind_spmf p (\<lambda>s1. map_spmf fst (rfunc_usr rest1 s1 iu)) = bind_spmf q (\<lambda>s2. map_spmf fst (rfunc_usr rest2 s2 iu))"
    and sim_rfunc_usr: "\<And>p q iu s1 s2 s1' s2' ou. \<lbrakk> S p q; iu \<in> IU; 
      s1 \<in> set_spmf p; s2 \<in> set_spmf q; (ou, s1') \<in> set_spmf (rfunc_usr rest1 s1 iu); (ou, s2') \<in> set_spmf (rfunc_usr rest2 s2 iu) \<rbrakk>
      \<Longrightarrow> S (cond_spmf_fst (bind_spmf p (\<lambda>s1. rfunc_usr rest1 s1 iu)) ou) (cond_spmf_fst (bind_spmf q (\<lambda>s2. rfunc_usr rest2 s2 iu)) ou)"
  shows "trace_rest_eq rest1 rest2 IA IU p q"
proof(rule trace_rest_eqI)
  fix tr :: "('iadv_rest \<times> 'oadv_rest \<times> 'event list + 'iusr_rest \<times> 'ousr_rest \<times> 'event list) list"
  assume "set tr \<subseteq> IA \<times> UNIV <+> IU \<times> UNIV"
  then have "(\<forall>ia\<in>IA. fst (trace_rest' rest1 p tr) ia = fst (trace_rest' rest2 q tr) ia) \<and>
       (\<forall>iu\<in>IU. snd (trace_rest' rest1 p tr) iu = snd (trace_rest' rest2 q tr) iu)"
    using start
  proof(induction tr arbitrary: p q)
    case Nil
    then show ?case by(simp add: step_rfunc_adv step_rfunc_usr)
  next
    case (Cons a tr)
    from Cons.prems(1) have tr: "set tr \<subseteq> IA \<times> UNIV <+> IU \<times> UNIV" by simp
    from Cons.prems(1)
    consider (rfunc_adv) ia oa where "a = Inl (ia, oa)" "ia \<in> IA"
      | (rfunc_usr) iu ou where "a = Inr (iu, ou)" "iu \<in> IU" by auto
    then show ?case
    proof cases
      case rfunc_adv
      let ?p = "bind_spmf p (\<lambda>s1. rfunc_adv rest1 s1 ia)"
      let ?q = "bind_spmf q (\<lambda>s2. rfunc_adv rest2 s2 ia)"
      show ?thesis
      proof(cases "oa \<in> fst ` set_spmf ?p")
        case True
        with step_rfunc_adv[OF Cons.prems(2) rfunc_adv(2), THEN arg_cong[where f=set_spmf]]
        have "oa \<in> fst ` set_spmf ?q"
          unfolding set_map_spmf[symmetric] by(simp only: map_bind_spmf o_def)
        then show ?thesis using True Cons.prems rfunc_adv
          by(clarsimp)(rule Cons.IH; blast intro: sim_rfunc_adv)
      next
        case False
        hence "cond_spmf_fst ?p oa = return_pmf None" by simp
        moreover
        from step_rfunc_adv[OF Cons.prems(2) rfunc_adv(2), THEN arg_cong[where f=set_spmf]] False
        have oa': "oa \<notin> fst ` set_spmf ?q"
          unfolding set_map_spmf[symmetric] by(simp only: map_bind_spmf o_def) simp
        hence "cond_spmf_fst ?q oa = return_pmf None" by simp
        ultimately show ?thesis using rfunc_adv by(simp del: cond_spmf_fst_eq_return_None)
      qed
    next
      case rfunc_usr
      let ?p = "bind_spmf p (\<lambda>s1. rfunc_usr rest1 s1 iu)"
      let ?q = "bind_spmf q (\<lambda>s2. rfunc_usr rest2 s2 iu)"
      show ?thesis
      proof(cases "ou \<in> fst ` set_spmf ?p")
        case True
        with step_rfunc_usr[OF Cons.prems(2) rfunc_usr(2), THEN arg_cong[where f=set_spmf]]
        have "ou \<in> fst ` set_spmf ?q"
          unfolding set_map_spmf[symmetric] by(simp only: map_bind_spmf o_def)
        then show ?thesis using True Cons.prems rfunc_usr
          by(clarsimp)(rule Cons.IH; blast intro: sim_rfunc_usr)
      next
        case False
        hence "cond_spmf_fst ?p ou = return_pmf None" by simp
        moreover
        from step_rfunc_usr[OF Cons.prems(2) rfunc_usr(2), THEN arg_cong[where f=set_spmf]] False
        have oa': "ou \<notin> fst ` set_spmf ?q"
          unfolding set_map_spmf[symmetric] by(simp only: map_bind_spmf o_def) simp
        hence "cond_spmf_fst ?q ou = return_pmf None" by simp
        ultimately show ?thesis using rfunc_usr by(simp del: cond_spmf_fst_eq_return_None)
      qed
    qed
  qed
  then show "ia \<in> IA \<Longrightarrow> fst (trace_rest' rest1 p tr) ia = fst (trace_rest' rest2 q tr) ia"
    and "iu \<in> IU \<Longrightarrow> snd (trace_rest' rest1 p tr) iu = snd (trace_rest' rest2 q tr) iu"
    for ia iu by blast+
qed

context 
  fixes rest :: "('s_rest, 'event, 'iadv_rest, 'iusr_rest, 'oadv_rest, 'ousr_rest, 'more) rest_scheme"
begin

fun trace_rest_aux 
  :: "'s_rest spmf \<Rightarrow> ('iadv_rest \<times> 'oadv_rest \<times> 'event list + 'iusr_rest \<times> 'ousr_rest \<times> 'event list) list \<Rightarrow> 's_rest spmf" where
  "trace_rest_aux p [] = p"
| "trace_rest_aux p (Inl (ia, oaes) # tr) = trace_rest_aux (cond_spmf_fst (bind_spmf p (\<lambda>s. rfunc_adv rest s ia)) oaes) tr"
| "trace_rest_aux p (Inr (iu, oues) # tr) = trace_rest_aux (cond_spmf_fst (bind_spmf p (\<lambda>s. rfunc_usr rest s iu)) oues) tr"

end

lemma trace_rest_conv_trace_rest_aux:
  "trace_rest' rest p tr = 
   (\<lambda>ia. bind_spmf (trace_rest_aux rest p tr) (\<lambda>s. map_spmf fst (rfunc_adv rest s ia)),
    \<lambda>iu. bind_spmf (trace_rest_aux rest p tr) (\<lambda>s. map_spmf fst (rfunc_usr rest s iu)))"
  by(induction p tr rule: trace_rest_aux.induct) simp_all

lemma trace_rest_aux_append:
  "trace_rest_aux rest p (tr @ tr') = trace_rest_aux rest (trace_rest_aux rest p tr) tr'"
  by(induction p tr rule: trace_rest_aux.induct) auto

inductive trace_rest_closure 
  :: "('s_rest, 'event, 'iadv_rest, 'iusr_rest, 'oadv_rest, 'ousr_rest, 'more) rest_scheme
  \<Rightarrow> ('s_rest', 'event, 'iadv_rest, 'iusr_rest, 'oadv_rest, 'ousr_rest, 'more') rest_scheme
  \<Rightarrow> 'iadv_rest set \<Rightarrow> 'iusr_rest set
  \<Rightarrow> 's_rest spmf \<Rightarrow> 's_rest' spmf \<Rightarrow> 's_rest spmf \<Rightarrow> 's_rest' spmf \<Rightarrow> bool"
  for rest1 rest2 IA IU p q where
  "trace_rest_closure rest1 rest2 IA IU p q (trace_rest_aux rest1 p tr) (trace_rest_aux rest2 q tr)"
  if "set tr \<subseteq> IA \<times> UNIV <+> IU \<times> UNIV"

lemma trace_rest_closure_start: "trace_rest_closure rest1 rest2 IA IU p q p q"
  by(simp add: trace_rest_closure.simps exI[where x="[]"])

lemma trace_rest_closure_step:
  assumes "trace_rest_eq rest1 rest2 IA IU p q"
    and "trace_rest_closure rest1 rest2 IA IU p q p' q'"
  shows trace_rest_closure_step_rfunc_adv: 
    "ia \<in> IA \<Longrightarrow> bind_spmf p' (\<lambda>s1. map_spmf fst (rfunc_adv rest1 s1 ia)) = bind_spmf q' (\<lambda>s2. map_spmf fst (rfunc_adv rest2 s2 ia))"
    (is "PROP ?thesis1")
    and trace_rest_closure_step_rfunc_usr:
    "iu \<in> IU \<Longrightarrow> bind_spmf p' (\<lambda>s1. map_spmf fst (rfunc_usr rest1 s1 iu)) = bind_spmf q' (\<lambda>s2. map_spmf fst (rfunc_usr rest2 s2 iu))"
    (is "PROP ?thesis2")
proof -
  from assms(2) obtain tr where p: "p' = trace_rest_aux rest1 p tr"
    and q: "q' = trace_rest_aux rest2 q tr"
    and tr: "set tr \<subseteq> IA \<times> UNIV <+> IU \<times> UNIV" by cases
  from trace_rest_eqD[OF assms(1) tr] p q
  show "PROP ?thesis1" and "PROP ?thesis2"
    by(simp_all add: trace_rest_conv_trace_rest_aux)
qed

lemma trace_rest_closure_sim:
  fixes rest1 rest2 IA IU p q
  defines "S \<equiv> trace_rest_closure rest1 rest2 IA IU p q"
  assumes "S p' q'"
  shows trace_rest_closure_sim_rfunc_adv: "ia \<in> IA 
    \<Longrightarrow> S (cond_spmf_fst (bind_spmf p' (\<lambda>s1. rfunc_adv rest1 s1 ia)) oa) 
          (cond_spmf_fst (bind_spmf q' (\<lambda>s2. rfunc_adv rest2 s2 ia)) oa)"
    (is "PROP ?thesis1")
    and trace_rest_closure_sim_rfunc_usr: "iu \<in> IU 
    \<Longrightarrow> S (cond_spmf_fst (bind_spmf p' (\<lambda>s1. rfunc_usr rest1 s1 iu)) ou)
          (cond_spmf_fst (bind_spmf q' (\<lambda>s2. rfunc_usr rest2 s2 iu)) ou)"
    (is "PROP ?thesis2")
proof -
  from assms(2) obtain tr where p: "p' = trace_rest_aux rest1 p tr"
    and q: "q' = trace_rest_aux rest2 q tr"
    and tr: "set tr \<subseteq> IA \<times> UNIV <+> IU \<times> UNIV" unfolding S_def by cases
  show "PROP ?thesis1" using p q tr
    by(auto simp add: S_def trace_rest_closure.simps trace_rest_aux_append intro!: exI[where x="tr @ [Inl (_, _)]"])
  show "PROP ?thesis2" using p q tr
    by(auto simp add: S_def trace_rest_closure.simps trace_rest_aux_append intro!: exI[where x="tr @ [Inr (_, _)]"])
qed

proposition trace_rest_eq_complete:
  assumes "trace_rest_eq rest1 rest2 IA IU p q"
  obtains S
  where "S p q"
    and "\<And>p q ia. \<lbrakk> S p q; ia \<in> IA \<rbrakk> \<Longrightarrow> 
      bind_spmf p (\<lambda>s1. map_spmf fst (rfunc_adv rest1 s1 ia)) = bind_spmf q (\<lambda>s2. map_spmf fst (rfunc_adv rest2 s2 ia))"
    and "\<And>p q ia oa. \<lbrakk> S p q; ia \<in> IA \<rbrakk>
      \<Longrightarrow> S (cond_spmf_fst (bind_spmf p (\<lambda>s1. rfunc_adv rest1 s1 ia)) oa) (cond_spmf_fst (bind_spmf q (\<lambda>s2. rfunc_adv rest2 s2 ia)) oa)"
    and "\<And>p q iu. \<lbrakk> S p q; iu \<in> IU \<rbrakk> \<Longrightarrow> 
      bind_spmf p (\<lambda>s1. map_spmf fst (rfunc_usr rest1 s1 iu)) = bind_spmf q (\<lambda>s2. map_spmf fst (rfunc_usr rest2 s2 iu))"
    and "\<And>p q iu ou. \<lbrakk> S p q; iu \<in> IU \<rbrakk>
      \<Longrightarrow> S (cond_spmf_fst (bind_spmf p (\<lambda>s1. rfunc_usr rest1 s1 iu)) ou) (cond_spmf_fst (bind_spmf q (\<lambda>s2. rfunc_usr rest2 s2 iu)) ou)"
proof -
  show thesis
    by(rule that[where S="trace_rest_closure rest1 rest2 IA IU p q"])
      (auto intro: trace_rest_closure_start trace_rest_closure_step[OF assms] trace_rest_closure_sim (* trace_rest_closure_weight[OF assms] *))
qed

definition callee_of_core
  :: "('s_core, 'event, 'iadv_core, 'iusr_core, 'oadv_core, 'ousr_core) core
    \<Rightarrow> ('s_core, 'event + 'iadv_core + 'iusr_core, unit + 'oadv_core + 'ousr_core) oracle'" where
  "callee_of_core core =
   map_fun id (map_fun id (map_spmf (Pair ()))) (cpoke core) \<oplus>\<^sub>O cfunc_adv core \<oplus>\<^sub>O cfunc_usr core"

lemma callee_of_core_simps [simp]:
  "callee_of_core core s (Inl e) = map_spmf (Pair (Inl ())) (cpoke core s e)"
  "callee_of_core core s (Inr (Inl iadv_core)) = map_spmf (apfst (Inr \<circ> Inl)) (cfunc_adv core s iadv_core)"
  "callee_of_core core s (Inr (Inr iusr_core)) = map_spmf (apfst (Inr \<circ> Inr)) (cfunc_usr core s iusr_core)"
  by(simp_all add: callee_of_core_def spmf.map_comp o_def apfst_def prod.map_comp id_def)

lemma WT_callee_of_core [WT_intro]:
  assumes WT: "WT_core \<I>_adv \<I>_usr I core"
     and I: "I s"
   shows "\<I>_full \<oplus>\<^sub>\<I> (\<I>_adv \<oplus>\<^sub>\<I> \<I>_usr) \<turnstile>c callee_of_core core s \<surd>"
  apply(rule WT_calleeI)
  subgoal for x y s' using I WT_coreD[OF WT]
    by(auto simp add: callee_of_core_def plus_oracle_def split!: sum.splits)
  done

lemma WT_core_callee_invariant_on [WT_intro]:
  assumes WT: "WT_core \<I>_adv \<I>_usr I core"
  shows "callee_invariant_on (callee_of_core core) I (\<I>_full \<oplus>\<^sub>\<I> (\<I>_adv \<oplus>\<^sub>\<I> \<I>_usr))"
  apply unfold_locales
  subgoal for s x y s' by(auto simp add: callee_of_core_def plus_oracle_def split!: sum.splits dest: WT_coreD[OF assms])
  subgoal by(rule WT_callee_of_core[OF WT])
  done

definition callee_of_rest
  :: "('s_rest, 'event, 'iadv_rest, 'iusr_rest, 'oadv_rest, 'ousr_rest, 'more) rest_scheme
    \<Rightarrow> ('s_rest, 'iadv_rest + 'iusr_rest, 'oadv_rest \<times> 'event list + 'ousr_rest \<times> 'event list) oracle'" where
  "callee_of_rest rest = rfunc_adv rest \<oplus>\<^sub>O rfunc_usr rest"

lemma callee_of_rest_simps [simp]:
  "callee_of_rest rest s (Inl iadv_rest) = map_spmf (apfst Inl) (rfunc_adv rest s iadv_rest)"
  "callee_of_rest rest s (Inr iusr_rest) = map_spmf (apfst Inr) (rfunc_usr rest s iusr_rest)"
  by(simp_all add: callee_of_rest_def)

lemma WT_callee_of_rest [WT_intro]:
  assumes WT: "WT_rest \<I>_adv \<I>_usr I rest"
    and I: "I s"
  shows "e\<I> \<I>_adv \<oplus>\<^sub>\<I> e\<I> \<I>_usr \<turnstile>c callee_of_rest rest s \<surd>"
  apply(rule WT_calleeI)
  subgoal for x y s' using I WT_restD[OF WT]
    by(auto simp add: callee_of_core_def plus_oracle_def split!: sum.splits)
  done

fun fuse_callee 
  :: "('iadv_core + 'iadv_rest) + ('iusr_core + 'iusr_rest) \<Rightarrow>
      (('oadv_core + 'oadv_rest) + ('ousr_core + 'ousr_rest),
       ('event + 'iadv_core + 'iusr_core) + ('iadv_rest + 'iusr_rest),
       (unit + 'oadv_core + 'ousr_core) + ('oadv_rest \<times> 'event list + 'ousr_rest \<times> 'event list)) gpv"
  where
  "fuse_callee (Inl (Inl iadv_core)) = Pause (Inl (Inr (Inl iadv_core))) (\<lambda>x. case x of
       Inl (Inr (Inl oadv_core)) \<Rightarrow> Done (Inl (Inl oadv_core))
     | _ \<Rightarrow> Fail)"
| "fuse_callee (Inl (Inr iadv_rest)) = Pause (Inr (Inl iadv_rest)) (\<lambda>x. case x of
       Inr (Inl (oadv_rest, es)) \<Rightarrow> bind_gpv (pauses (map (Inl \<circ> Inl) es)) (\<lambda>_. Done (Inl (Inr oadv_rest)))
     | _ \<Rightarrow> Fail)"
| "fuse_callee (Inr (Inl iusr_core)) = Pause (Inl (Inr (Inr iusr_core))) (\<lambda>x. case x of
       Inl (Inr (Inr oadv_core)) \<Rightarrow> Done (Inr (Inl oadv_core)))"
| "fuse_callee (Inr (Inr iusr_rest)) = Pause (Inr (Inr iusr_rest)) (\<lambda>x. case x of
       Inr (Inr (ousr_rest, es)) \<Rightarrow> bind_gpv (pauses (map (Inl \<circ> Inl) es)) (\<lambda>_. Done (Inr (Inr ousr_rest))))"

case_of_simps fuse_callee_case: fuse_callee.simps

(* parametric_constant fuse_callee_parametric [transfer_rule]: fuse_callee_case *)

definition fuse_converter 
  :: "(('iadv_core + 'iadv_rest) + ('iusr_core + 'iusr_rest), 
       ('oadv_core + 'oadv_rest) + ('ousr_core + 'ousr_rest),
       ('event + 'iadv_core + 'iusr_core) + ('iadv_rest + 'iusr_rest),
       (unit + 'oadv_core + 'ousr_core) + ('oadv_rest \<times> 'event list + 'ousr_rest \<times> 'event list)) converter"
  where
  "fuse_converter = converter_of_callee (stateless_callee fuse_callee) ()"

lemma fuse_converter:
  "resource_of_oracle (fused_resource.fuse core rest) (s_core, s_rest) = 
  fuse_converter \<rhd> (resource_of_oracle (callee_of_core core) s_core \<parallel> resource_of_oracle (callee_of_rest rest) s_rest)"
  unfolding fuse_converter_def resource_of_parallel_oracle[symmetric] attach_CNV_RES attach_stateless_callee resource_of_oracle_extend_state_oracle
proof(rule arg_cong2[where f=resource_of_oracle]; clarsimp simp add: fun_eq_iff)
  interpret fused_resource core core_init for core_init .
  have "foldl_spmf (map_fun id (map_fun (Inl \<circ> Inl) id) (map_fun id (map_fun id (map_spmf snd)) (callee_of_core core \<ddagger>\<^sub>O callee_of_rest rest))) (return_spmf (s_core, s_rest)) xs
     = map_spmf (\<lambda>s_core. (s_core, s_rest)) (foldl_spmf (cpoke core) (return_spmf s_core) xs)" for s_core s_rest xs
    by(induction xs arbitrary: s_core)
      (simp_all add: spmf.map_comp foldl_spmf_Cons' map_bind_spmf bind_map_spmf o_def del: foldl_spmf_Cons)
  then show "fuse rest (s_core, s_rest) q = exec_gpv (callee_of_core core \<ddagger>\<^sub>O callee_of_rest rest) (fuse_callee q) (s_core, s_rest)"
    for s_core s_rest q
    by(cases q rule: fuse_callee.cases; clarsimp simp add: map_bind_spmf bind_map_spmf exec_gpv_bind exec_gpv_pauses intro!: bind_spmf_cong[OF refl]; simp add: map_spmf_conv_bind_spmf[symmetric])
qed

lemma trace_eq_callee_of_coreI:
  "trace_callee_eq (callee_of_core core1) (callee_of_core core2) (E <+> IA <+> IU) p q"
  if "trace_core_eq core1 core2 E IA IU p q"
proof -
  from that obtain S_core 
    where core_start: "S_core p q"
      and step_cpoke: "\<And>p q e. S_core p q \<Longrightarrow> e \<in> E
        \<Longrightarrow> weight_spmf (bind_spmf p (\<lambda>s. cpoke core1 s e)) = weight_spmf (bind_spmf q (\<lambda>s. cpoke core2 s e))"
      and sim_cpoke: "\<And>p q e. S_core p q \<Longrightarrow> e \<in> E 
       \<Longrightarrow> S_core (mk_lossless (bind_spmf p (\<lambda>s. cpoke core1 s e))) (mk_lossless (bind_spmf q (\<lambda>s. cpoke core2 s e)))"
      and step_cfunc_adv: "\<And>p q ia. \<lbrakk> S_core p q; ia \<in> IA \<rbrakk>
       \<Longrightarrow> bind_spmf p (\<lambda>s1. map_spmf fst (cfunc_adv core1 s1 ia)) = bind_spmf q (\<lambda>s2. map_spmf fst (cfunc_adv core2 s2 ia))"
      and sim_cfunc_adv: "\<And>p q ia oa. \<lbrakk> S_core p q; ia \<in> IA \<rbrakk> \<Longrightarrow>
        S_core (cond_spmf_fst (bind_spmf p (\<lambda>s1. cfunc_adv core1 s1 ia)) oa)
               (cond_spmf_fst (bind_spmf q (\<lambda>s2. cfunc_adv core2 s2 ia)) oa)"
      and step_cfunc_usr: "\<And>p q iu. \<lbrakk> S_core p q; iu \<in> IU \<rbrakk>
        \<Longrightarrow> bind_spmf p (\<lambda>s1. map_spmf fst (cfunc_usr core1 s1 iu)) = bind_spmf q (\<lambda>s2. map_spmf fst (cfunc_usr core2 s2 iu))"
      and sim_cfunc_usr: "\<And>p q iu ou. \<lbrakk> S_core p q; iu \<in> IU \<rbrakk> \<Longrightarrow>
        S_core (cond_spmf_fst (bind_spmf p (\<lambda>s1. cfunc_usr core1 s1 iu)) ou)
               (cond_spmf_fst (bind_spmf q (\<lambda>s2. cfunc_usr core2 s2 iu)) ou)"
    by(rule trace_core_eq_complete) blast

  show ?thesis using core_start
  proof(coinduct rule: trace'_eqI_sim[consumes 1, case_names step sim])
    case (step p q a)
    then consider (cpoke) e where "a = Inl e" "e \<in> E"
      | (cfunc_adv) ia where "a = Inr (Inl ia)" "ia \<in> IA"
      | (cfunc_usr) iu where "a = Inr (Inr iu)" "iu \<in> IU" by auto
    then show ?case
    proof cases
      case cpoke
      with step_cpoke[OF step(1), of e] show ?thesis 
        by(simp add: spmf.map_comp o_def map_spmf_const weight_bind_spmf)
          (auto intro!: spmf_eqI simp add: spmf_bind spmf_scale_spmf max_def min_absorb2 weight_spmf_le_1)
    next
      case cfunc_adv
      with step_cfunc_adv[OF step(1) cfunc_adv(2)] show ?thesis
        by(simp add: spmf.map_comp)(simp add: spmf.map_comp[symmetric] map_bind_spmf[unfolded o_def, symmetric])
    next
      case cfunc_usr
      with step_cfunc_usr[OF step(1) cfunc_usr(2)] show ?thesis
        by(simp add: spmf.map_comp)(simp add: spmf.map_comp[symmetric] map_bind_spmf[unfolded o_def, symmetric])
    qed 
  next
    case (sim p q a res b s')
    then consider (cpoke) e where "a = Inl e" "e \<in> E"
      | (cfunc_adv) ia where "a = Inr (Inl ia)" "ia \<in> IA"
      | (cfunc_usr) iu where "a = Inr (Inr iu)" "iu \<in> IU" by auto
    then show ?case
    proof cases
      case cpoke
      with sim_cpoke[OF sim(1) , of e] sim show ?thesis 
        by(clarsimp simp add: map_bind_spmf[unfolded o_def, symmetric])
    next
      case cfunc_adv
      with sim_cfunc_adv[OF sim(1) cfunc_adv(2)] sim show ?thesis
        apply(clarsimp simp add: map_bind_spmf[unfolded o_def, symmetric] apfst_def map_prod_def)
        apply(subst (1 2) cond_spmf_fst_map_prod_inj)
         apply(simp_all add: o_def[symmetric] inj_compose del: o_apply)
        done
    next
      case cfunc_usr
      with sim_cfunc_usr[OF sim(1) cfunc_usr(2)] sim show ?thesis
        apply(clarsimp simp add: map_bind_spmf[unfolded o_def, symmetric] apfst_def map_prod_def)
        apply(subst (1 2) cond_spmf_fst_map_prod_inj)
         apply(simp_all add: o_def[symmetric] inj_compose del: o_apply)
        done
    qed
  qed
qed

lemma trace_eq_callee_of_restI:
  "trace_callee_eq (callee_of_rest rest1) (callee_of_rest rest2) (IA <+> IU) p q"
  if "trace_rest_eq rest1 rest2 IA IU p q"
proof -
  from that obtain S_rest 
    where rest_start: "S_rest p q"
      and step_rfunc_adv: "\<And>p q ia. \<lbrakk> S_rest p q; ia \<in> IA \<rbrakk>
       \<Longrightarrow> bind_spmf p (\<lambda>s1. map_spmf fst (rfunc_adv rest1 s1 ia)) = bind_spmf q (\<lambda>s2. map_spmf fst (rfunc_adv rest2 s2 ia))"
      and sim_rfunc_adv: "\<And>p q ia oa. \<lbrakk> S_rest p q; ia \<in> IA \<rbrakk> \<Longrightarrow>
        S_rest (cond_spmf_fst (bind_spmf p (\<lambda>s1. rfunc_adv rest1 s1 ia)) oa)
               (cond_spmf_fst (bind_spmf q (\<lambda>s2. rfunc_adv rest2 s2 ia)) oa)"
      and step_rfunc_usr: "\<And>p q iu. \<lbrakk> S_rest p q; iu \<in> IU \<rbrakk>
        \<Longrightarrow> bind_spmf p (\<lambda>s1. map_spmf fst (rfunc_usr rest1 s1 iu)) = bind_spmf q (\<lambda>s2. map_spmf fst (rfunc_usr rest2 s2 iu))"
      and sim_rfunc_usr: "\<And>p q iu ou. \<lbrakk> S_rest p q; iu \<in> IU \<rbrakk> \<Longrightarrow>
        S_rest (cond_spmf_fst (bind_spmf p (\<lambda>s1. rfunc_usr rest1 s1 iu)) ou)
               (cond_spmf_fst (bind_spmf q (\<lambda>s2. rfunc_usr rest2 s2 iu)) ou)"
    by(rule trace_rest_eq_complete) blast

  show ?thesis using rest_start
  proof(coinduct rule: trace'_eqI_sim[consumes 1, case_names step sim])
    case (step p q a)
    then consider (rfunc_adv) ia where "a = Inl ia" "ia \<in> IA"
      | (rfunc_usr) iu where "a = Inr iu" "iu \<in> IU" by auto
    then show ?case
    proof cases
      case rfunc_adv
      with step_rfunc_adv[OF step(1) rfunc_adv(2)] show ?thesis
        by(simp add: spmf.map_comp)(simp add: spmf.map_comp[symmetric] map_bind_spmf[unfolded o_def, symmetric])
    next
      case rfunc_usr
      with step_rfunc_usr[OF step(1) rfunc_usr(2)] show ?thesis
        by(simp add: spmf.map_comp)(simp add: spmf.map_comp[symmetric] map_bind_spmf[unfolded o_def, symmetric])
    qed 
  next
    case (sim p q a res b s')
    then consider (rfunc_adv) ia where "a = Inl ia" "ia \<in> IA"
      | (rfunc_usr) iu where "a = Inr iu" "iu \<in> IU" by auto
    then show ?case
    proof cases
      case rfunc_adv
      with sim_rfunc_adv[OF sim(1) rfunc_adv(2)] sim show ?thesis
        by(clarsimp simp add: map_bind_spmf[unfolded o_def, symmetric] apfst_def map_prod_def)
          (subst (1 2) cond_spmf_fst_map_prod_inj; simp)
    next
      case rfunc_usr
      with sim_rfunc_usr[OF sim(1) rfunc_usr(2)] sim show ?thesis
        by(clarsimp simp add: map_bind_spmf[unfolded o_def, symmetric] apfst_def map_prod_def)
          (subst (1 2) cond_spmf_fst_map_prod_inj; simp)
    qed
  qed
qed

lemma trace_callee_resource_of_oracle:
  "trace_callee run_resource (map_spmf (resource_of_oracle callee) p) = trace_callee callee p"
  (is "?lhs = ?rhs")
proof(intro ext)
  show "?lhs tr x = ?rhs tr x" for tr x
  proof(induction tr arbitrary: p)
    case Nil show ?case by(simp add: bind_map_spmf o_def spmf.map_comp)
  next
    case (Cons a tr)
    obtain y z where a [simp]: "a = (y, z)" by(cases a)
    have "trace_callee run_resource (map_spmf (RES callee) p) (a # tr) x =
      trace_callee run_resource (cond_spmf_fst (map_spmf (\<lambda>(x, y). (x, RES callee y)) (p \<bind> (\<lambda>x. (callee x y)))) z) tr x"
      by(clarsimp simp add: bind_map_spmf o_def map_prod_def map_bind_spmf)
    also have "\<dots> = trace_callee run_resource (map_spmf (RES callee) (cond_spmf_fst (p \<bind> (\<lambda>x. (callee x y))) z)) tr x"
      by(subst cond_spmf_fst_map_prod_inj) simp_all
    finally show ?case using Cons.IH by simp
  qed
qed

lemma trace_callee_resource_of_oracle':
  "trace_callee run_resource (return_spmf (resource_of_oracle callee s)) = trace_callee callee (return_spmf s)"
  using trace_callee_resource_of_oracle[where p="return_spmf s"]
  by simp

lemma trace_eq_resource_of_oracle:
  "trace_eq A (map_spmf (resource_of_oracle callee1) p) (map_spmf (resource_of_oracle callee2) q) =
   trace_callee_eq callee1 callee2 A p q"
  unfolding trace_callee_eq_def trace_callee_resource_of_oracle by(rule refl)

lemma WT_fuse_converter [WT_intro]:
  "(\<I>AC \<oplus>\<^sub>\<I> map_\<I> id fst \<I>AR) \<oplus>\<^sub>\<I> (\<I>UC \<oplus>\<^sub>\<I> map_\<I> id fst \<I>UR), (\<I>E \<oplus>\<^sub>\<I> (\<I>AC \<oplus>\<^sub>\<I> \<I>UC)) \<oplus>\<^sub>\<I> (\<I>AR \<oplus>\<^sub>\<I> \<I>UR) \<turnstile>\<^sub>C fuse_converter \<surd>"
  if "\<forall>x. \<forall>(y, es)\<in>responses_\<I> \<I>AR x. set es \<subseteq> outs_\<I> \<I>E" "\<forall>x. \<forall>(y, es)\<in>responses_\<I> \<I>UR x. set es \<subseteq> outs_\<I> \<I>E"
  unfolding fuse_converter_def using that
  by(intro WT_converter_of_callee)
    (fastforce simp add: stateless_callee_def image_image intro: rev_image_eqI intro!: WT_gpv_pauses split: if_split_asm)+

theorem fuse_trace_eq:
  fixes core1 :: "('s_core, 'event, 'iadv_core, 'iusr_core, 'oadv_core, 'ousr_core) core"
    and core2 :: "('s_core', 'event, 'iadv_core, 'iusr_core, 'oadv_core, 'ousr_core) core"
    and rest1 :: "('s_rest, 'event, 'iadv_rest, 'iusr_rest, 'oadv_rest, 'ousr_rest, 'more1) rest_scheme"
    and rest2 :: "('s_rest', 'event, 'iadv_rest, 'iusr_rest, 'oadv_rest, 'ousr_rest, 'more2) rest_scheme"
  assumes core: "trace_core_eq core1 core2 (outs_\<I> \<I>E) (outs_\<I> \<I>CA) (outs_\<I> \<I>CU) (return_spmf s_core) (return_spmf s_core')"
    and rest: "trace_rest_eq rest1 rest2 (outs_\<I> \<I>RA) (outs_\<I> \<I>RU) (return_spmf s_rest) (return_spmf s_rest')"
    and IC1: "callee_invariant_on (callee_of_core core1) IC1 (\<I>E \<oplus>\<^sub>\<I> (\<I>CA \<oplus>\<^sub>\<I> \<I>CU))" "IC1 s_core"
    and IC2: "callee_invariant_on (callee_of_core core2) IC2 (\<I>E \<oplus>\<^sub>\<I> (\<I>CA \<oplus>\<^sub>\<I> \<I>CU))" "IC2 s_core'"
    and IR1: "callee_invariant_on (callee_of_rest rest1) IR1 (\<I>RA \<oplus>\<^sub>\<I> \<I>RU)" "IR1 s_rest"
    and IR2: "callee_invariant_on (callee_of_rest rest2) IR2 (\<I>RA \<oplus>\<^sub>\<I> \<I>RU)" "IR2 s_rest'"
    and E1 [WT_intro]: "\<forall>x. \<forall>(y, es)\<in>responses_\<I> \<I>RA x. set es \<subseteq> outs_\<I> \<I>E"
    and E2 [WT_intro]: "\<forall>x. \<forall>(y, es)\<in>responses_\<I> \<I>RU x. set es \<subseteq> outs_\<I> \<I>E"
  shows "trace_callee_eq (fused_resource.fuse core1 rest1) (fused_resource.fuse core2 rest2)
    ((outs_\<I> \<I>CA <+> outs_\<I> \<I>RA) <+> (outs_\<I> \<I>CU <+> outs_\<I> \<I>RU)) (return_spmf (s_core, s_rest)) (return_spmf (s_core', s_rest'))"
proof -
  let ?\<I>C = "\<I>E \<oplus>\<^sub>\<I> (\<I>CA \<oplus>\<^sub>\<I> \<I>CU)"
  let ?\<I>R = "\<I>RA \<oplus>\<^sub>\<I> \<I>RU"
  let ?\<I>' = "?\<I>C \<oplus>\<^sub>\<I> ?\<I>R"
  let ?\<I> = "(\<I>CA \<oplus>\<^sub>\<I> map_\<I> id fst \<I>RA) \<oplus>\<^sub>\<I> (\<I>CU \<oplus>\<^sub>\<I> map_\<I> id fst \<I>RU)"

  interpret fuse1: fused_resource core1 s1 for s1 .
  interpret fuse2: fused_resource core2 s2 for s2 .
  interpret IC1: callee_invariant_on "callee_of_core core1" IC1 ?\<I>C by fact
  interpret IC2: callee_invariant_on "callee_of_core core2" IC2 ?\<I>C by fact
  interpret IR1: callee_invariant_on "callee_of_rest rest1" IR1 ?\<I>R by fact
  interpret IR2: callee_invariant_on "callee_of_rest rest2" IR2 ?\<I>R by fact

  from core have "outs_\<I> ?\<I>C \<turnstile>\<^sub>C callee_of_core core1(s_core) \<approx> callee_of_core core2(s_core')"
    by(simp add: trace_eq_callee_of_coreI)
  hence "outs_\<I> ?\<I>C \<turnstile>\<^sub>R RES (callee_of_core core1) s_core \<approx> RES (callee_of_core core2) s_core'" by simp
  moreover have "outs_\<I> ?\<I>R \<turnstile>\<^sub>C callee_of_rest rest1(s_rest) \<approx> callee_of_rest rest2(s_rest')" using rest
    by(simp add: trace_eq_callee_of_restI)
  hence "outs_\<I> ?\<I>R \<turnstile>\<^sub>R RES (callee_of_rest rest1) s_rest \<approx> RES (callee_of_rest rest2) s_rest'" by simp
  ultimately have "outs_\<I> ?\<I>' \<turnstile>\<^sub>R
    RES (callee_of_core core1) s_core \<parallel> RES (callee_of_rest rest1) s_rest \<approx>
    RES (callee_of_core core2) s_core' \<parallel> RES (callee_of_rest rest2) s_rest'"
    by(simp add: trace_eq'_parallel_resource)
  hence "outs_\<I> ?\<I> \<turnstile>\<^sub>R fuse_converter \<rhd> (RES (callee_of_core core1) s_core \<parallel> RES (callee_of_rest rest1) s_rest) \<approx>
                      fuse_converter \<rhd> (RES (callee_of_core core2) s_core' \<parallel> RES (callee_of_rest rest2) s_rest')"
    by(rule attach_trace_eq')(intro WT_intro IC1.WT_resource_of_oracle IC1 IC2.WT_resource_of_oracle IC2 IR1.WT_resource_of_oracle IR1 IR2.WT_resource_of_oracle IR2)+
  hence "trace_eq' (outs_\<I> ?\<I>) (resource_of_oracle (fuse1.fuse rest1) (s_core, s_rest)) (resource_of_oracle (fuse2.fuse rest2) (s_core', s_rest'))"
    unfolding fuse_converter by simp
  then show ?thesis by simp
qed


inductive trace_eq_simcl :: "('s1 spmf \<Rightarrow> 's2 spmf \<Rightarrow> bool) \<Rightarrow> 's1 spmf \<Rightarrow> 's2 spmf \<Rightarrow> bool"
  for S where
  base: "trace_eq_simcl S p q" if "S p q" for p q
| bind_nat: "trace_eq_simcl S (bind_spmf p f) (bind_spmf p g)" 
if "\<And>x :: nat. x \<in> set_spmf p \<Longrightarrow> S (f x) (g x)"

lemma trace_eq_simcl_bindI [intro?]: "trace_eq_simcl S (bind_spmf p f) (bind_spmf p g)"
  if "\<And>x. x \<in> set_spmf p \<Longrightarrow> S (f x) (g x)"
  by(subst (1 2) bind_spmf_to_nat_on[symmetric])(auto intro!: trace_eq_simcl.bind_nat simp add: that)

lemma trace_eq_simcl_bind: "trace_eq_simcl S (bind_spmf p f) (bind_spmf p g)"
  if *: "\<And>x :: 'a. x \<in> set_spmf p \<Longrightarrow> trace_eq_simcl S (f x) (g x)"
proof -
  obtain P :: "'a \<Rightarrow> nat spmf" and F G where
    **: "\<And>x. x \<in> set_spmf p \<Longrightarrow> f x = bind_spmf (P x) (F x) \<and> g x = bind_spmf (P x) (G x) \<and> (\<forall>y\<in>set_spmf (P x). S (F x y) (G x y))"
    apply(atomize_elim)
    apply(subst choice_iff[symmetric])+
    apply(fastforce dest!: * elim!: trace_eq_simcl.cases intro: exI[where x="return_spmf _"])
    done
  have "bind_spmf p f = bind_spmf (bind_spmf p (\<lambda>x. map_spmf (Pair x) (P x))) (\<lambda>(x, y). F x y)"
    by(simp add: bind_map_spmf o_def ** cong: bind_spmf_cong)
  moreover have "bind_spmf p g = bind_spmf (bind_spmf p (\<lambda>x. map_spmf (Pair x) (P x))) (\<lambda>(x, y). G x y)"
    by(simp add: bind_map_spmf o_def ** cong: bind_spmf_cong)
  ultimately show ?thesis  by(simp only:)(rule trace_eq_simcl_bindI; clarsimp simp add: **)
qed

lemma trace_eq_simcl_bind1_scale: "trace_eq_simcl S (bind_spmf p f) (scale_spmf (weight_spmf p) q)"
  if "\<forall>x\<in>set_spmf p. trace_eq_simcl S (f x) q"
proof -
  have "trace_eq_simcl S (bind_spmf p f) (bind_spmf p (\<lambda>_. q))"
    by(rule trace_eq_simcl_bind)(simp add: that)
  thus ?thesis by(simp add: bind_spmf_const)
qed

lemma trace_eq_simcl_bind1: "trace_eq_simcl S (bind_spmf p f) q"
  if "\<forall>x\<in>set_spmf p. trace_eq_simcl S (f x) q" "lossless_spmf p"
  using trace_eq_simcl_bind1_scale[OF that(1)] that(2) by(simp add: lossless_weight_spmfD)

lemma trace_eq_simcl_bind2_scale: "trace_eq_simcl S (scale_spmf (weight_spmf q) p) (bind_spmf q f)"
  if "\<forall>x\<in>set_spmf q. trace_eq_simcl S p (f x)"
proof -
  have "trace_eq_simcl S (bind_spmf q (\<lambda>_. p)) (bind_spmf q f)"
    by(rule trace_eq_simcl_bind)(simp add: that)
  thus ?thesis by(simp add: bind_spmf_const)
qed

lemma trace_eq_simcl_bind2: "trace_eq_simcl S p (bind_spmf q f)"
  if "\<forall>x\<in>set_spmf q. trace_eq_simcl S p (f x)" "lossless_spmf q"
  using trace_eq_simcl_bind2_scale[OF that(1)] that(2) by(simp add: lossless_weight_spmfD)

lemma trace_eq_simcl_return_pmf_None [simp, intro!]: "trace_eq_simcl S (return_pmf None) (return_pmf None)" 
  for S :: "'s1 spmf \<Rightarrow> 's2 spmf \<Rightarrow> bool"
proof -
  have "trace_eq_simcl S (bind_spmf (return_pmf None) (undefined :: nat \<Rightarrow> 's1 spmf)) (bind_spmf (return_pmf None) (undefined :: nat \<Rightarrow> 's2 spmf))"
    by(rule trace_eq_simcl_bindI) simp
  then show ?thesis by simp
qed

lemma trace_eq_simcl_map: "trace_eq_simcl S (map_spmf f p) (map_spmf g p)"
  if "\<forall>x\<in>set_spmf p. S (return_spmf (f x)) (return_spmf (g x))"
  unfolding map_spmf_conv_bind_spmf
  by(rule trace_eq_simcl_bindI)(simp add: that)

lemma trace_eq_simcl_map1: "trace_eq_simcl S (map_spmf f p) q"
  if "\<forall>x\<in>set_spmf p. trace_eq_simcl S (return_spmf (f x)) q" "lossless_spmf p"
  unfolding map_spmf_conv_bind_spmf
  by(rule trace_eq_simcl_bind1)(simp_all add: that)

lemma trace_eq_simcl_map2: "trace_eq_simcl S p (map_spmf f q)"
  if "\<forall>x\<in>set_spmf q. trace_eq_simcl S p (return_spmf (f x))" "lossless_spmf q"
  unfolding map_spmf_conv_bind_spmf
  by(rule trace_eq_simcl_bind2)(simp_all add: that)

lemma trace_eq_simcl_return_spmf [simp]: "trace_eq_simcl S (return_spmf x) (return_spmf y) \<longleftrightarrow> S (return_spmf x) (return_spmf y)"
  apply(rule iffI)
  subgoal by(erule trace_eq_simcl.cases; clarsimp dest!: sym[where s="return_spmf _"])(auto 4 4 simp add: bind_eq_return_spmf dest!: lossless_spmfD_set_spmf_nonempty)
  by(simp add: trace_eq_simcl.base)

lemma trace_eq_simcl_callee:
  fixes callee1 :: "('a, 'b, 's1) callee" and callee2 :: "('a, 'b, 's2) callee"
  assumes step: "\<And>p q a. \<lbrakk> S p q; a \<in> A \<rbrakk> \<Longrightarrow>
      bind_spmf p (\<lambda>s. map_spmf fst (callee1 s a)) = bind_spmf q (\<lambda>s. map_spmf fst (callee2 s a))"
    and sim: "\<And>p q a res b s'. \<lbrakk> S p q; a \<in> A; res \<in> set_spmf q; (b, s') \<in> set_spmf (callee2 res a) \<rbrakk>
      \<Longrightarrow> trace_eq_simcl S (cond_spmf_fst (bind_spmf p (\<lambda>s. callee1 s a)) b)
            (cond_spmf_fst (bind_spmf q (\<lambda>s. callee2 s a)) b)"
    and start: "trace_eq_simcl S p q" and a: "a \<in> A"
  shows trace_eq_simcl_callee_step: "bind_spmf p (\<lambda>s. map_spmf fst (callee1 s a)) = bind_spmf q (\<lambda>s. map_spmf fst (callee2 s a))" (is "?step")
    and trace_eq_simcl_callee_sim: "\<And>res b s'. \<lbrakk> res \<in> set_spmf q; (b, s') \<in> set_spmf (callee2 res a) \<rbrakk>
      \<Longrightarrow> trace_eq_simcl S (cond_spmf_fst (bind_spmf p (\<lambda>s. callee1 s a)) b)
                            (cond_spmf_fst (bind_spmf q (\<lambda>s. callee2 s a)) b)" (is "\<And>res b s'. \<lbrakk> ?res res; ?b res b s' \<rbrakk> \<Longrightarrow> ?sim res b s'")
proof -
  show eq: ?step using start a by cases(auto intro!: bind_spmf_cong intro: step)
  show "?sim res b s'" if "?res res" "?b res b s'" for res b s' using start
  proof cases
    case base then show ?thesis using a that by(rule sim)
  next
    case (bind_nat X f g)
    let ?Y = "cond_bind_spmf_fst X (\<lambda>y. map_spmf fst (bind_spmf (f y) (\<lambda>s. callee1 s a))) b"
    let ?Y' = "cond_bind_spmf_fst X (\<lambda>y. map_spmf fst (bind_spmf (g y) (\<lambda>s. callee2 s a))) b"
    have "cond_spmf_fst (bind_spmf p (\<lambda>s. callee1 s a)) b = bind_spmf ?Y (\<lambda>x. cond_spmf_fst (bind_spmf (f x) (\<lambda>s. callee1 s a)) b)"
      unfolding bind_nat by(simp add: cond_spmf_fst_bind o_def)
    moreover have "cond_spmf_fst (bind_spmf q (\<lambda>s. callee2 s a)) b = bind_spmf ?Y' (\<lambda>x. cond_spmf_fst (bind_spmf (g x) (\<lambda>s. callee2 s a)) b)"
      unfolding bind_nat by(simp add: cond_spmf_fst_bind o_def)
    moreover have "?Y = ?Y'" using bind_nat eq
      by(intro spmf_eqI)(fastforce simp add: map_bind_spmf o_def spmf_eq_0_set_spmf dest: step[OF _ a])
    ultimately 
    show "trace_eq_simcl S (cond_spmf_fst (bind_spmf p (\<lambda>s. callee1 s a)) b)
        (cond_spmf_fst (bind_spmf q (\<lambda>s. callee2 s a)) b)" using bind_nat a
      by(simp)(rule trace_eq_simcl_bind; auto intro!: sim simp add: bind_UNION)
  qed
qed

proposition trace'_eqI_sim_upto:
  fixes callee1 :: "('a, 'b, 's1) callee" and callee2 :: "('a, 'b, 's2) callee"
  assumes start: "S p q"
    and step: "\<And>p q a. \<lbrakk> S p q; a \<in> A \<rbrakk> \<Longrightarrow>
      bind_spmf p (\<lambda>s. map_spmf fst (callee1 s a)) = bind_spmf q (\<lambda>s. map_spmf fst (callee2 s a))"
    and sim: "\<And>p q a res b s'. \<lbrakk> S p q; a \<in> A; res \<in> set_spmf q; (b, s') \<in> set_spmf (callee2 res a) \<rbrakk>
      \<Longrightarrow> trace_eq_simcl S (cond_spmf_fst (bind_spmf p (\<lambda>s. callee1 s a)) b)
            (cond_spmf_fst (bind_spmf q (\<lambda>s. callee2 s a)) b)"
  shows "trace_callee_eq callee1 callee2 A p q"
proof -
  let ?S = "trace_eq_simcl S"
  from start have "?S p q" by(rule trace_eq_simcl.base)
  then show ?thesis by(rule trace'_eqI_sim)(rule trace_eq_simcl_callee[OF step sim]; assumption)+
qed

lemma trace_core_eq_simI_upto:
  fixes core1 :: "('s_core, 'event, 'iadv_core, 'iusr_core, 'oadv_core, 'ousr_core) core"
    and core2 :: "('s_core', 'event, 'iadv_core, 'iusr_core, 'oadv_core, 'ousr_core) core"
    and S :: "'s_core spmf \<Rightarrow> 's_core' spmf \<Rightarrow> bool"
  assumes start: "S p q"
    and step_cpoke: "\<And>p q e. \<lbrakk> S p q; e \<in> E \<rbrakk> \<Longrightarrow> 
      weight_spmf (bind_spmf p (\<lambda>s. cpoke core1 s e)) = weight_spmf (bind_spmf q (\<lambda>s. cpoke core2 s e))"
    and sim_cpoke: "\<And>p q e. \<lbrakk> S p q; e \<in> E \<rbrakk> \<Longrightarrow> 
      trace_eq_simcl S (mk_lossless (bind_spmf p (\<lambda>s. cpoke core1 s e))) (mk_lossless (bind_spmf q (\<lambda>s. cpoke core2 s e)))"
    and step_cfunc_adv: "\<And>p q ia. \<lbrakk> S p q; ia \<in> IA \<rbrakk> \<Longrightarrow> 
      bind_spmf p (\<lambda>s1. map_spmf fst (cfunc_adv core1 s1 ia)) = bind_spmf q (\<lambda>s2. map_spmf fst (cfunc_adv core2 s2 ia))"
    and sim_cfunc_adv: "\<And>p q ia s1 s2 s1' s2' oa. \<lbrakk> S p q; ia \<in> IA; 
      s1 \<in> set_spmf p; s2 \<in> set_spmf q; (oa, s1') \<in> set_spmf (cfunc_adv core1 s1 ia); (oa, s2') \<in> set_spmf (cfunc_adv core2 s2 ia) \<rbrakk>
      \<Longrightarrow> trace_eq_simcl S (cond_spmf_fst (bind_spmf p (\<lambda>s1. cfunc_adv core1 s1 ia)) oa) (cond_spmf_fst (bind_spmf q (\<lambda>s2. cfunc_adv core2 s2 ia)) oa)"
    and step_cfunc_usr: "\<And>p q iu. \<lbrakk> S p q; iu \<in> IU \<rbrakk> \<Longrightarrow> 
      bind_spmf p (\<lambda>s1. map_spmf fst (cfunc_usr core1 s1 iu)) = bind_spmf q (\<lambda>s2. map_spmf fst (cfunc_usr core2 s2 iu))"
    and sim_cfunc_usr: "\<And>p q iu s1 s2 s1' s2' ou. \<lbrakk> S p q; iu \<in> IU; 
      s1 \<in> set_spmf p; s2 \<in> set_spmf q; (ou, s1') \<in> set_spmf (cfunc_usr core1 s1 iu); (ou, s2') \<in> set_spmf (cfunc_usr core2 s2 iu) \<rbrakk>
      \<Longrightarrow> trace_eq_simcl S (cond_spmf_fst (bind_spmf p (\<lambda>s1. cfunc_usr core1 s1 iu)) ou) (cond_spmf_fst (bind_spmf q (\<lambda>s2. cfunc_usr core2 s2 iu)) ou)"
  shows "trace_core_eq core1 core2 E IA IU p q"
proof -
  let ?S = "trace_eq_simcl S"
  from start have "?S p q" by(rule trace_eq_simcl.base)
  then show ?thesis 
  proof(rule trace_core_eq_simI, goal_cases Step_cpoke Sim_cpoke Step_cfunc_adv Sim_cfunc_adv Step_cfunc_usr Sim_cfunc_usr)
    { case (Step_cpoke p q e)
      then show ?case using step_cpoke
        by cases(auto simp add: weight_bind_spmf o_def intro!: Bochner_Integration.integral_cong_AE) }
    note eq = this

    case (Sim_cpoke p q e) then show ?case
    proof cases
      case base then show ?thesis using Sim_cpoke(2) by(rule sim_cpoke)
    next
      case (bind_nat X f g)
      then have "cond_bind_spmf X (\<lambda>y. f y \<bind> (\<lambda>s. cpoke core1 s e)) UNIV = cond_bind_spmf X (\<lambda>y. g y \<bind> (\<lambda>s. cpoke core2 s e)) UNIV"
        using eq[OF Sim_cpoke] step_cpoke Sim_cpoke
        by(intro spmf_eqI)(simp add: weight_spmf_def measure_spmf_zero_iff bind_UNION spmf_eq_0_set_spmf)
      then show ?thesis using bind_nat Sim_cpoke sim_cpoke
        by(auto simp add: cond_bind_spmf cond_spmf_UNIV[symmetric] simp del: cond_spmf_UNIV intro: trace_eq_simcl_bind)
    qed
  next 
    { case (Step_cfunc_adv p q ia)
      then show ?case using step_cfunc_adv by cases(auto intro!: bind_spmf_cong) }
    note eq = this

    case (Sim_cfunc_adv p q ia s1 s2 s1' s2' oa) then show ?case 
    proof cases
      case base then show ?thesis using Sim_cfunc_adv(2-) by(rule sim_cfunc_adv)
    next
      case (bind_nat X f g)
      then have "cond_bind_spmf_fst X (\<lambda>y. map_spmf fst (f y \<bind> (\<lambda>s1. cfunc_adv core1 s1 ia))) oa =
            cond_bind_spmf_fst X (\<lambda>y. map_spmf fst (g y \<bind> (\<lambda>s2. cfunc_adv core2 s2 ia))) oa"
        using eq[OF Sim_cfunc_adv(1,2)]
        by(intro spmf_eqI)(fastforce simp add: map_bind_spmf o_def spmf_eq_0_set_spmf dest: step_cfunc_adv[OF _ Sim_cfunc_adv(2)])
      then show ?thesis using bind_nat(3-) Sim_cfunc_adv(1-2)
        unfolding bind_nat(1,2) bind_spmf_assoc
        apply(subst (1 2) cond_spmf_fst_bind)
        apply(simp add: o_def)
        apply(rule trace_eq_simcl_bind)
        apply clarsimp
        apply(frule step_cfunc_adv[OF bind_nat(3) Sim_cfunc_adv(2), THEN arg_cong[where f="set_spmf"], THEN equalityD2])
        apply(clarsimp simp add: o_def bind_UNION)
        apply(drule subsetD)
         apply fastforce
        apply(auto intro: sim_cfunc_adv)
        done
    qed
  next
    { case (Step_cfunc_usr p q iu)
      then show ?case using step_cfunc_usr by cases(auto intro!: bind_spmf_cong) }
    note eq = this

    case (Sim_cfunc_usr p q iu s1 s2 s1' s2' ou) then show ?case
    proof cases
      case base then show ?thesis using Sim_cfunc_usr(2-) by(rule sim_cfunc_usr)
    next
      case (bind_nat X f g)
      then have "cond_bind_spmf_fst X (\<lambda>y. map_spmf fst (f y \<bind> (\<lambda>s1. cfunc_usr core1 s1 iu))) ou =
            cond_bind_spmf_fst X (\<lambda>y. map_spmf fst (g y \<bind> (\<lambda>s2. cfunc_usr core2 s2 iu))) ou"
        using eq[OF Sim_cfunc_usr(1,2)]
        by(intro spmf_eqI)(fastforce simp add: map_bind_spmf o_def spmf_eq_0_set_spmf dest: step_cfunc_usr[OF _ Sim_cfunc_usr(2)])
      then show ?thesis using bind_nat(3-) Sim_cfunc_usr(1-2)
        unfolding bind_nat(1,2) bind_spmf_assoc
        apply(subst (1 2) cond_spmf_fst_bind)
        apply(simp add: o_def)
        apply(rule trace_eq_simcl_bind)
        apply clarsimp
        apply(frule step_cfunc_usr[OF bind_nat(3) Sim_cfunc_usr(2), THEN arg_cong[where f="set_spmf"], THEN equalityD2])
        apply(clarsimp simp add: o_def bind_UNION)
        apply(drule subsetD)
         apply fastforce
        apply(auto intro: sim_cfunc_usr)
        done
    qed
  qed
qed



context
  fixes core :: "('s_core, 'event1 + 'event2, 'iadv_core, 'iusr_core, 'oadv_core, 'ousr_core) core"
    and rest :: "('s_rest, 'event2, 'iadv_rest, 'iusr_rest, 'oadv_rest, 'ousr_rest, 'more) rest_scheme" 
begin

primcorec core_with_rest :: 
  "('s_core \<times> 's_rest, 'event1, 'iadv_core + 'iadv_rest, 'iusr_core + 'iusr_rest, 'oadv_core + 'oadv_rest, 'ousr_core + 'ousr_rest) core" 
  where
    "cpoke core_with_rest = (\<lambda>(s_core, s_rest) e. map_spmf (\<lambda>s_core'. (s_core', s_rest)) (cpoke core s_core (Inl e)))"
  | "cfunc_adv core_with_rest = (\<lambda>(s_core, s_rest) iadv. case iadv of
       Inl iadv_core \<Rightarrow> map_spmf (\<lambda>(oadv_core, s_core'). (Inl oadv_core, (s_core', s_rest))) (cfunc_adv core s_core iadv_core)
     | Inr iadv_rest \<Rightarrow> 
       bind_spmf (rfunc_adv rest s_rest iadv_rest) (\<lambda>((oadv_rest, es), s_rest'). 
         map_spmf (\<lambda>s_core'. (Inr oadv_rest, (s_core', s_rest'))) (foldl_spmf (cpoke core) (return_spmf s_core) (map Inr es))))"
  | "cfunc_usr core_with_rest = (\<lambda>(s_core, s_rest) iusr. case iusr of
       Inl iusr_core \<Rightarrow> map_spmf (\<lambda>(ousr_core, s_core'). (Inl ousr_core, (s_core', s_rest))) (cfunc_usr core s_core iusr_core)
     | Inr iusr_rest \<Rightarrow>
       bind_spmf (rfunc_usr rest s_rest iusr_rest) (\<lambda>((ousr_rest, es), s_rest').
         map_spmf (\<lambda>s_core'. (Inr ousr_rest, (s_core', s_rest'))) (foldl_spmf (cpoke core) (return_spmf s_core) (map Inr es))))"

end

lemma fuse_core_with_rest:
  fixes core :: "('s_core, 'event1 + 'event2, 'iadv_core, 'iusr_core, 'oadv_core, 'ousr_core) core"
    and rest1 :: "('s_rest1, 'event1, 'iadv_rest1, 'iusr_rest1, 'oadv_rest1, 'ousr_rest1, 'more1) rest_scheme"
    and rest2 :: "('s_rest2, 'event2, 'iadv_rest2, 'iusr_rest2, 'oadv_rest2, 'ousr_rest2, 'more2) rest_scheme"
  shows
  "fused_resource.fuse core (parallel_rest rest1 rest2) (s_core, (s_rest1, s_rest2)) = 
   map_fun (map_sum (lsumr \<circ> map_sum id swap_sum) (lsumr \<circ> map_sum id swap_sum)) (map_spmf (map_prod (map_sum (map_sum id swap_sum \<circ> rsuml) (map_sum id swap_sum \<circ> rsuml)) (map_prod id prod.swap \<circ> rprodl)))
   (fused_resource.fuse (core_with_rest core rest2) rest1 ((s_core, s_rest2), s_rest1))"
  apply(rule ext)
  subgoal for x
    apply(cases "(parallel_rest rest1 rest2, (s_core, (s_rest1, s_rest2)), x)" rule: fused_resource.fuse.cases)
       apply(auto simp add: fused_resource.fuse.simps map_bind_spmf bind_map_spmf map_prod_def split_def o_def parallel_eoracle_def parallel_oracle_def split!: sum.split intro!: bind_spmf_cong)
     apply(subst foldl_spmf_pair_left[simplified split_def]; simp add: map_fun_def o_def bind_map_spmf)+
    done
  done

end