section\<open>Least Upper Bound\<close>
text\<open>The simplest way to merge a pair of transitions with identical outputs and updates is to
simply take the least upper bound of their \emph{guards}. This theory presents several variants on
this theme.\<close>

theory Least_Upper_Bound
  imports "../Inference"
begin

fun literal_args :: "'a gexp \<Rightarrow> bool" where
  "literal_args (Bc v) = False" |
  "literal_args (Eq (V _) (L _)) = True" |
  "literal_args (In _ _) = True" |
  "literal_args (Eq _ _) = False" |
  "literal_args (Gt va v) = False" |
  "literal_args (Nor v va) = (literal_args v \<and> literal_args va)"

lemma literal_args_eq:
  "literal_args (Eq a b) \<Longrightarrow> \<exists>v l. a = (V v) \<and> b = (L l)"
  apply (cases a)
     apply simp
      apply (cases b)
  by auto

definition "all_literal_args t = (\<forall>g \<in> set (Guards t). literal_args g)"

fun merge_in_eq :: "vname \<Rightarrow> value \<Rightarrow> vname gexp list \<Rightarrow> vname gexp list" where
  "merge_in_eq v l [] = [Eq (V v) (L l)]" |
  "merge_in_eq v l ((Eq (V v') (L l'))#t) = (if v = v' \<and> l \<noteq> l' then (In v [l, l'])#t else (Eq (V v') (L l'))#(merge_in_eq v l t))" |
  "merge_in_eq v l ((In v' l')#t) = (if v = v' then (In v (remdups (l#l')))#t else (In v' l')#(merge_in_eq v l t))" |
  "merge_in_eq v l (h#t) = h#(merge_in_eq v l t)"

fun merge_in_in :: "vname \<Rightarrow> value list \<Rightarrow> vname gexp list \<Rightarrow> vname gexp list" where
  "merge_in_in v l [] = [In v l]" |
  "merge_in_in v l ((Eq (V v') (L l'))#t) = (if v = v' then (In v (List.insert l' l))#t else (Eq (V v') (L l'))#(merge_in_in v l t))" |
  "merge_in_in v l ((In v' l')#t) = (if v = v' then (In v (List.union l l'))#t else (In v' l')#(merge_in_in v l t))" |
  "merge_in_in v l (h#t) = h#(merge_in_in v l t)"

fun merge_guards :: "vname gexp list \<Rightarrow> vname gexp list \<Rightarrow> vname gexp list" where
  "merge_guards [] g2 = g2" |
  "merge_guards ((Eq (V v) (L l))#t) g2 =  merge_guards t (merge_in_eq v l g2)" |
  "merge_guards ((In v l)#t) g2 = merge_guards t (merge_in_in v l g2)" |
  "merge_guards (h#t) g2 = h#(merge_guards t g2)"

text\<open>The ``least upper bound'' (lob) heuristic simply disjoins the guards of two transitions with
identical outputs and updates.\<close>
definition lob_aux :: "transition \<Rightarrow> transition \<Rightarrow> transition option" where
  "lob_aux t1 t2 = (if Outputs t1 = Outputs t2 \<and> Updates t1 = Updates t2 \<and> all_literal_args t1 \<and> all_literal_args t2 then
      Some \<lparr>Label = Label t1, Arity = Arity t1, Guards = remdups (merge_guards (Guards t1) (Guards t2)), Outputs = Outputs t1, Updates = Updates t1\<rparr>
     else None)"

fun lob :: update_modifier where
  "lob t1ID t2ID s new _ old _ = (let
     t1 = (get_by_ids new t1ID);
     t2 = (get_by_ids new t2ID) in
     case lob_aux t1 t2 of
       None \<Rightarrow> None |
       Some lob_t \<Rightarrow>
           Some (replace_transitions new [(t1ID, lob_t), (t2ID, lob_t)])
   )"

lemma lob_aux_some: "Outputs t1 = Outputs t2 \<Longrightarrow>
       Updates t1 = Updates t2 \<Longrightarrow>
       all_literal_args t1 \<Longrightarrow>
       all_literal_args t2 \<Longrightarrow>
       Label t = Label t1 \<Longrightarrow>
       Arity t = Arity t1 \<Longrightarrow>
       Guards t = remdups (merge_guards (Guards t1) (Guards t2)) \<Longrightarrow>
       Outputs t = Outputs t1 \<Longrightarrow>
       Updates t = Updates t1 \<Longrightarrow>
       lob_aux t1 t2 = Some t"
  by (simp add: lob_aux_def)

fun has_corresponding :: "vname gexp \<Rightarrow> vname gexp list \<Rightarrow> bool" where
  "has_corresponding g [] = False" |
  "has_corresponding (Eq (V v) (L l)) ((Eq (V v') (L l'))#t) = (if v = v' \<and> l = l' then True else has_corresponding (Eq (V v) (L l)) t)" |
  "has_corresponding (In v' l') ((Eq (V v) (L l))#t) = (if v = v' \<and> l \<in> set l' then True else has_corresponding (In v' l') t)" |
  "has_corresponding (In v l) ((In v' l')#t) = (if v = v' \<and> set l' \<subseteq> set l then True else has_corresponding (In v l) t)" |
  "has_corresponding g (h#t) = has_corresponding g t"

lemma no_corresponding_bc: "\<not>has_corresponding (Bc x1) G1"
  apply (induct G1)
  by auto

lemma no_corresponding_gt: "\<not>has_corresponding (Gt x1 y1) G1"
  apply (induct G1)
  by auto

lemma no_corresponding_nor: "\<not>has_corresponding (Nor x1 y1) G1"
  apply (induct G1)
  by auto

lemma has_corresponding_eq: "has_corresponding (Eq x21 x22) G1 \<Longrightarrow> (Eq x21 x22) \<in> set G1"
proof(induct G1)
  case (Cons a G1)
  then show ?case
    apply (cases a)
        apply simp
    subgoal for x21a x22a
      apply (case_tac "x21a")
          apply simp
         apply (case_tac "x22a")
             apply clarify
             apply simp
             apply (case_tac "x21")
                 apply simp
                apply (case_tac "x22")
                    apply (metis has_corresponding.simps(2))
      by auto
    by auto
qed auto

lemma has_corresponding_In: "has_corresponding (In v l) G1 \<Longrightarrow> (\<exists>l'. (In v l') \<in> set G1 \<and> set l' \<subseteq> set l) \<or> (\<exists>l' \<in> set l. (Eq (V v) (L l')) \<in> set G1)"
proof(induct G1)
  case (Cons a G1)
  then show ?case
    apply (cases a)
        apply simp
       defer
       apply simp
      apply simp
      defer
      apply simp
     apply simp
    subgoal for x21 x22 apply (case_tac x21)
          apply simp
         apply (case_tac x22)
             apply fastforce
            apply simp+
      done
    by metis
qed auto

lemma gval_each_one: "g \<in> set G \<Longrightarrow> apply_guards G s \<Longrightarrow> gval g s = true"
  using apply_guards_cons apply_guards_rearrange by blast

lemma has_corresponding_apply_guards:
  "\<forall>g\<in>set G2. has_corresponding g G1 \<Longrightarrow>
   apply_guards G1 s \<Longrightarrow>
   apply_guards G2 s"
proof(induct G2)
  case (Cons a G2)
  then show ?case
    apply (cases a)
        apply (simp add: no_corresponding_bc)
       apply simp
       apply (metis (full_types) has_corresponding_eq append_Cons append_self_conv2 apply_guards_append apply_guards_rearrange)
      apply (simp add: no_corresponding_gt)
     apply simp
    subgoal for v l
      apply (insert has_corresponding_In[of v l G1])
      apply simp
      apply (erule disjE)
       apply clarsimp
      subgoal for l'
        apply (insert apply_guards_rearrange[of "In v l'" G1 s])
        apply simp
        apply (simp only: apply_guards_cons[of "In v l" G2])
        apply (simp only: apply_guards_cons[of "In v l'" G1])
        apply simp
        apply (cases "s v")
         apply simp
        by force
      apply clarsimp
      subgoal for l'
        apply (insert apply_guards_rearrange[of "Eq (V v) (L l')" G1 s])
        apply simp
        apply (simp only: apply_guards_cons[of "In v l" G2])
        apply (simp only: apply_guards_cons[of "Eq (V v) (L l')" G1])
        apply (cases "s v")
         apply simp
        apply simp
        using trilean.distinct(1) by presburger
      done
    by (simp add: no_corresponding_nor)
qed auto

lemma correspondence_subsumption:
  "Label t1 = Label t2 \<Longrightarrow>
   Arity t1 = Arity t2 \<Longrightarrow>
   Outputs t1 = Outputs t2 \<Longrightarrow>
   Updates t1 = Updates t2 \<Longrightarrow>
   \<forall>g \<in> set (Guards t2). has_corresponding g (Guards t1) \<Longrightarrow>
   subsumes t2 c t1"
  by (simp add: can_take_def can_take_transition_def has_corresponding_apply_guards subsumption)

definition "is_lob t1 t2 = (
  Label t1 = Label t2 \<and>
  Arity t1 = Arity t2 \<and>
  Outputs t1 = Outputs t2 \<and>
  Updates t1 = Updates t2 \<and>
  (\<forall>g \<in> set (Guards t2). has_corresponding g (Guards t1)))"

lemma is_lob_direct_subsumption:
  "is_lob t1 t2 \<Longrightarrow> directly_subsumes e1 e2 s s' t2 t1"
  apply (rule subsumes_in_all_contexts_directly_subsumes)
  by (simp add: is_lob_def correspondence_subsumption)

fun has_distinguishing :: "vname gexp \<Rightarrow> vname gexp list \<Rightarrow> bool" where
  "has_distinguishing g [] = False" |
  "has_distinguishing (Eq (V v) (L l)) ((Eq (V v') (L l'))#t) = (if v = v' \<and> l \<noteq> l' then True else has_distinguishing (Eq (V v) (L l)) t)" |
  "has_distinguishing (In (I v') l') ((Eq (V (I v)) (L l))#t) = (if v = v' \<and> l \<notin> set l' then True else has_distinguishing (In (I v') l') t)" |
  "has_distinguishing (In (I v) l) ((In (I v') l')#t) = (if v = v' \<and> set l' \<supset> set l then True else has_distinguishing (In (I v) l) t)" |
  "has_distinguishing g (h#t) = has_distinguishing g t"

lemma has_distinguishing: "has_distinguishing g G \<Longrightarrow> (\<exists>v l. g = (Eq (V v) (L l))) \<or> (\<exists>v l. g = In v l)"
proof(induct G)
  case (Cons a G)
  then show ?case
    apply (cases g)
         apply simp
        apply (case_tac x21)
           apply simp
          apply (case_tac x22)
    by auto
qed auto

lemma has_distinguishing_Eq: "has_distinguishing (Eq (V v) (L l)) G \<Longrightarrow> \<exists>l'. (Eq (V v) (L l')) \<in> set G \<and> l \<noteq> l'"
proof (induct G)
  case (Cons a G)
  then show ?case
    apply (cases a)
         apply simp
        apply (case_tac x21)
           apply simp
          apply (case_tac x22)
             apply (metis has_distinguishing.simps(2) list.set_intros(1) list.set_intros(2))
    by auto
qed auto

lemma ex_mutex: "Eq (V v) (L l) \<in> set G1 \<Longrightarrow>
       Eq (V v) (L l') \<in> set G2 \<Longrightarrow>
       l \<noteq> l' \<Longrightarrow>
       apply_guards G1 s \<Longrightarrow>
       \<not> apply_guards G2 s"
  apply (simp add: apply_guards_def Bex_def)
  apply (rule_tac x="Eq (V v) (L l')" in exI)
  apply simp
  apply (case_tac "s v")
  by auto

lemma has_distinguishing_In:
  "has_distinguishing (In v l) G \<Longrightarrow>
   (\<exists>l' i. v = I i \<and> Eq (V v) (L l') \<in> set G \<and> l' \<notin> set l) \<or> (\<exists>l' i. v = I i \<and> In v l' \<in> set G \<and> set l' \<supset> set l)"
proof(induct G)
  case (Cons a G)
  then show ?case
    apply (case_tac v)
    subgoal for x
      apply simp
      apply (cases a)
          apply simp
      subgoal for x21 x22
        apply (case_tac x21)
            apply simp
           apply (case_tac x22)
               apply (case_tac x2)
                apply fastforce
               apply simp+
        done
      subgoal by simp
      subgoal for x41
        apply (case_tac x41)
         apply (simp, metis)
        by auto
      by auto
    by auto
qed auto

lemma Eq_apply_guards:
  "Eq (V v) (L l) \<in> set G1 \<Longrightarrow>
   apply_guards G1 s \<Longrightarrow>
   s v = Some l"
  apply (simp add: apply_guards_rearrange)
  apply (simp add: apply_guards_cons)
  apply (cases "s v")
   apply simp
  apply simp
  using trilean.distinct(1) by presburger

lemma In_neq_apply_guards:
  "In v l \<in> set G2 \<Longrightarrow>
   Eq (V v) (L l') \<in> set G1 \<Longrightarrow>
   l' \<notin> set l \<Longrightarrow>
   apply_guards G1 s \<Longrightarrow>
   \<not>apply_guards G2 s"
proof(induct G1)
  case (Cons a G1)
  then show ?case
    apply (simp add: apply_guards_def Bex_def)
    apply (rule_tac x="In v l" in exI)
    using Eq_apply_guards[of v l' "a#G1" s]
    by (simp add: Cons.prems(4) image_iff)
qed auto

lemma In_apply_guards: "In v l \<in> set G1 \<Longrightarrow> apply_guards G1 s \<Longrightarrow> \<exists>v' \<in> set l. s v = Some v'"
  apply (simp add: apply_guards_rearrange)
  apply (simp add: apply_guards_cons)
  apply (cases "s v")
   apply simp
  apply simp
  by (meson image_iff trilean.simps(2))

lemma input_not_constrained_aval_swap_inputs:
  "\<not> aexp_constrains a (V (I v)) \<Longrightarrow>
   aval a (join_ir i c) = aval a (join_ir (list_update i v x) c)"
  apply(induct a rule: aexp_induct_separate_V_cases)
       apply simp
      apply (metis aexp_constrains.simps(2) aval.simps(2) input2state_nth input2state_out_of_bounds join_ir_def length_list_update not_le nth_list_update_neq vname.simps(5))
  using join_ir_def by auto

lemma input_not_constrained_gval_swap_inputs:
  "\<not> gexp_constrains a (V (I v)) \<Longrightarrow>
   gval a (join_ir i c) = gval a (join_ir (i[v := x]) c)"
proof(induct a)
  case (Bc x)
  then show ?case
    by (metis (full_types) gval.simps(1) gval.simps(2))
next
  case (Eq x1a x2)
  then show ?case
    using input_not_constrained_aval_swap_inputs by auto
next
  case (Gt x1a x2)
  then show ?case
    using input_not_constrained_aval_swap_inputs by auto
next
  case (In x1a x2)
  then show ?case
    apply simp
    apply (case_tac "join_ir i c x1a")
     apply (case_tac "join_ir (i[v := x]) c x1a")
      apply simp
     apply (metis In.prems aval.simps(2) gexp_constrains.simps(5) input_not_constrained_aval_swap_inputs option.discI)
    apply (case_tac "join_ir (i[v := x]) c x1a")
     apply (metis In.prems aval.simps(2) gexp_constrains.simps(5) input_not_constrained_aval_swap_inputs option.discI)
    by (metis In.prems aval.simps(2) gexp_constrains.simps(5) input_not_constrained_aval_swap_inputs)
qed auto

lemma test_aux: "\<forall>g\<in>set (removeAll (In (I v) l) G1). \<not> gexp_constrains g (V (I v)) \<Longrightarrow>
      apply_guards G1 (join_ir i c) \<Longrightarrow>
      x \<in> set l \<Longrightarrow>
      apply_guards G1 (join_ir (i[v := x]) c)"
proof(induct G1)
  case (Cons a G1)
  then show ?case
    apply (simp only: apply_guards_cons)
    apply (case_tac "a = In (I v) l")
     apply simp
     apply (case_tac "join_ir i c (I v)")
      apply simp
     apply (case_tac "join_ir (i[v := x]) c (I v)")
      apply (metis join_ir_nth le_less_linear length_list_update list_update_beyond option.discI)
     apply simp
     apply (metis join_ir_nth le_less_linear length_list_update list_update_beyond nth_list_update_eq option.inject trilean.distinct(1))
    apply (case_tac "join_ir (i[v := x]) c (I v)")
     apply (metis join_ir_nth le_less_linear length_list_update list_update_beyond option.discI)
    apply simp
    using input_not_constrained_gval_swap_inputs by auto
qed auto

lemma test:
  assumes
    p1: "In (I v) l \<in> set G2" and
    p2: "In (I v) l' \<in> set G1" and
    p3: "x \<in> set l'" and
    p4: "x \<notin> set l" and
    p5: "apply_guards G1 (join_ir i c)" and
    p6: "length i = a" and
    p7: "\<forall>g \<in> set (removeAll (In (I v) l') G1). \<not> gexp_constrains g (V (I v))"
  shows "\<exists>i. length i = a \<and> apply_guards G1 (join_ir i c) \<and> (length i = a \<longrightarrow> \<not> apply_guards G2 (join_ir i c))"
  apply (rule_tac x="list_update i v x" in exI)
  apply standard
   apply (simp add: p6)
  apply standard
  using p3 p5 p7 test_aux apply blast
  using p1 p4
  apply (simp add: apply_guards_rearrange)
  apply (simp add: apply_guards_cons join_ir_def)
  apply (case_tac "input2state (i[v := x]) $ v")
   apply simp
  apply simp
  by (metis input2state_nth input2state_within_bounds length_list_update nth_list_update_eq option.inject)

definition get_Ins :: "vname gexp list \<Rightarrow> (nat \<times> value list) list" where
  "get_Ins G = map (\<lambda>g. case g of (In (I v) l) \<Rightarrow> (v, l)) (filter (\<lambda>g. case g of (In (I _) _ ) \<Rightarrow> True | _ \<Rightarrow> False) G)"

lemma get_Ins_Cons_equiv: "\<nexists>v l. a = In (I v) l \<Longrightarrow> get_Ins (a # G) = get_Ins G"
  apply (simp add: get_Ins_def)
  apply (cases a)
       apply simp+
   apply (metis (full_types) vname.exhaust vname.simps(6))
  by simp

lemma Ball_Cons: "(\<forall>x \<in> set (a#l). P x) = (P a \<and> (\<forall>x \<in> set l. P x))"
  by simp

lemma In_in_get_Ins: "(In (I v) l \<in> set G) = ((v, l) \<in> set (get_Ins G))"
proof(induct G)
  case Nil
  then show ?case
    by (simp add: get_Ins_def)
next
  case (Cons a G)
  then show ?case
    apply (simp add: get_Ins_def)
    apply (cases a)
        apply simp+
    subgoal for x by (case_tac x, auto)
    apply auto
    done
qed

definition "check_get_Ins G = (\<forall>(v, l') \<in> set (get_Ins G). \<forall>g \<in> set (removeAll (In (I v) l') G). \<not> gexp_constrains g (V (I v)))"

lemma no_Ins: "[] = get_Ins G \<Longrightarrow> set G - {In (I i) l} = set G"
proof(induct G)
  case (Cons a G)
  then show ?case
    apply (cases a)
        apply (simp add: get_Ins_Cons_equiv insert_Diff_if)+
    subgoal for x41 x42
      apply (case_tac x41)
       apply simp
       apply (metis In_in_get_Ins equals0D list.set(1) list.set_intros(1))
      apply (simp add: get_Ins_Cons_equiv)
      done
    by (simp add: get_Ins_Cons_equiv insert_Diff_if)
qed auto

lemma test2: "In (I i) l \<in> set (Guards t2) \<Longrightarrow>
       In (I i) l' \<in> set (Guards t1) \<Longrightarrow>
       length ia = Arity t1 \<Longrightarrow>
       apply_guards (Guards t1) (join_ir ia c) \<Longrightarrow>
       x \<in> set l' \<Longrightarrow>
       x \<notin> set l \<Longrightarrow>
       \<forall>(v, l')\<in>insert (0, []) (set (get_Ins (Guards t1))). \<forall>g\<in>set (removeAll (In (I v) l') (Guards t1)). \<not> gexp_constrains g (V (I v)) \<Longrightarrow>
       Arity t1 = Arity t2 \<Longrightarrow>
       \<exists>i. length i = Arity t2 \<and> apply_guards (Guards t1) (join_ir i c) \<and> (length i = Arity t2 \<longrightarrow> \<not> apply_guards (Guards t2) (join_ir i c))"
  using test[of i l "Guards t2" l' "Guards t1" x ia  c "Arity t2"]
  apply simp
  apply (case_tac "\<forall>g\<in>set (Guards t1) - {In (I i) l'}. \<not> gexp_constrains g (V (I i))")
   apply simp
  apply simp
  using In_in_get_Ins by blast

lemma distinguishing_subsumption:
  assumes
    p1: "\<exists>g \<in> set (Guards t2). has_distinguishing g (Guards t1)" and
    p2: "Arity t1 = Arity t2" and
    p3: "\<exists>i. can_take_transition t1 i c" and
    p4: "(\<forall>(v, l') \<in> insert (0, []) (set (get_Ins (Guards t1))). \<forall>g \<in> set (removeAll (In (I v) l') (Guards t1)). \<not> gexp_constrains g (V (I v)))"
  shows
   "\<not> subsumes t2 c t1"
proof-
  show ?thesis
    apply (rule bad_guards)
    apply (simp add: can_take_transition_def can_take_def p2)
    apply (insert p1, simp add: Bex_def)
    apply (erule exE)
    apply (case_tac "\<exists>v l. x = (Eq (V v) (L l))")
     apply (metis can_take_def can_take_transition_def ex_mutex p2 p3 has_distinguishing_Eq)
    apply (case_tac "\<exists>v l. x = In v l")
     defer
    using has_distinguishing apply blast
    apply clarify
    apply (case_tac "\<exists>l' i. v = I i \<and> Eq (V v) (L l') \<in> set (Guards t1) \<and> l' \<notin> set l")
     apply (metis In_neq_apply_guards can_take_def can_take_transition_def p2 p3)
    apply (case_tac "(\<exists>l' i. v = I i \<and> In v l' \<in> set (Guards t1) \<and> set l' \<supset> set l)")
     defer
    using has_distinguishing_In apply blast
    apply simp
    apply (erule conjE)
    apply (erule exE)+
    apply (erule conjE)
    apply (insert p3, simp only: can_take_transition_def can_take_def)
    apply (case_tac "\<exists>x. x \<in> set l' \<and> x \<notin> set l")
    apply (erule exE)+
    apply (erule conjE)+
    apply (insert p4 p2)
    using test2
     apply blast
    by auto
qed

definition "lob_distinguished t1 t2 = (
(\<exists>g \<in> set (Guards t2). has_distinguishing g (Guards t1)) \<and>
Arity t1 = Arity t2 \<and>
(\<forall>(v, l') \<in> insert (0, []) (set (get_Ins (Guards t1))). \<forall>g \<in> set (removeAll (In (I v) l') (Guards t1)). \<not> gexp_constrains g (V (I v))))"

lemma must_be_another:
  "1 < size (fset_of_list b) \<Longrightarrow>
   x \<in> set b \<Longrightarrow>
   \<exists>x' \<in> set b. x \<noteq> x'"
proof(induct b)
  case (Cons a b)
  then show ?case
    apply (simp add: Bex_def)
    by (metis List.finite_set One_nat_def card.insert card_gt_0_iff card_mono fset_of_list.rep_eq insert_absorb le_0_eq less_nat_zero_code less_numeral_extra(4) not_less_iff_gr_or_eq set_empty2 subsetI)
qed auto

lemma another_swap_inputs:
  "apply_guards G (join_ir i c) \<Longrightarrow>
  filter (\<lambda>g. gexp_constrains g (V (I a))) G = [In (I a) b] \<Longrightarrow>
  xa \<in> set b \<Longrightarrow>
  apply_guards G (join_ir (i[a := xa]) c)"
proof(induct G)
  case (Cons g G)
  then show ?case
    apply (simp add: apply_guards_cons)
    apply (case_tac "gexp_constrains g (V (I a))")
     defer
    using input_not_constrained_gval_swap_inputs apply auto[1]
     apply simp
    apply (case_tac "join_ir i c (I a) \<in> Some ` set b")
     defer
     apply simp
    apply clarify
    apply standard
    using apply_guards_def input_not_constrained_gval_swap_inputs
      apply (simp add: filter_empty_conv)
      apply (case_tac "join_ir i c (I a)")
       apply simp
      apply (case_tac "join_ir (i[a := xa]) c (I a)")
       apply simp
       apply (metis image_eqI trilean.distinct(1))
      apply simp
      apply (metis image_eqI trilean.distinct(1))
     apply (case_tac "join_ir i c (I a)")
      apply simp
     apply simp
     apply (metis image_eqI trilean.distinct(1))
    apply (case_tac "join_ir i c (I a)")
     apply simp
    apply (case_tac "join_ir (i[a := xa]) c (I a)")
     apply simp
     apply (metis join_ir_nth le_less_linear length_list_update list_update_beyond option.discI)
    apply simp
    apply standard
     apply (metis (no_types, lifting) Cons.hyps Cons.prems(2) filter_empty_conv removeAll_id set_ConsD test_aux)
    by (metis in_these_eq join_ir_nth le_less_linear length_list_update list_update_beyond nth_list_update_eq these_image_Some_eq)
qed auto

lemma lob_distinguished_2_not_subsumes:
  "\<exists>(i, l) \<in> set (get_Ins (Guards t2)). filter (\<lambda>g. gexp_constrains g (V (I i))) (Guards t2) = [(In (I i) l)] \<and>
    (\<exists>l' \<in> set l. i < Arity t1 \<and> Eq (V (I i)) (L l') \<in> set (Guards t1) \<and> size (fset_of_list l) > 1) \<Longrightarrow>
   Arity t1 = Arity t2 \<Longrightarrow>
   \<exists>i. can_take_transition t2 i c \<Longrightarrow>
   \<not> subsumes t1 c t2"
  apply (rule bad_guards)
  apply simp
  apply (simp add: can_take_def can_take_transition_def Bex_def)
  apply clarify
  apply (case_tac "\<exists>x' \<in> set b. x \<noteq> x'")
   defer
   apply (simp add: must_be_another)
  apply (simp add: Bex_def)
  apply (erule exE)
  apply (rule_tac x="list_update i a xa" in exI)
  apply simp
  apply standard
   apply (simp add: another_swap_inputs)
  by (metis Eq_apply_guards input2state_nth join_ir_def length_list_update nth_list_update_eq option.inject vname.simps(5))

definition "lob_distinguished_2 t1 t2 =
  (\<exists>(i, l) \<in> set (get_Ins (Guards t2)). filter (\<lambda>g. gexp_constrains g (V (I i))) (Guards t2) = [(In (I i) l)] \<and>
    (\<exists>l' \<in> set l. i < Arity t1 \<and> Eq (V (I i)) (L l') \<in> set (Guards t1) \<and> size (fset_of_list l) > 1) \<and>
  Arity t1 = Arity t2)"

lemma lob_distinguished_3_not_subsumes:
  "\<exists>(i, l) \<in> set (get_Ins (Guards t2)). filter (\<lambda>g. gexp_constrains g (V (I i))) (Guards t2) = [(In (I i) l)] \<and>
    (\<exists>(i', l') \<in> set (get_Ins (Guards t1)). i = i' \<and> set l' \<subset> set l) \<Longrightarrow>
   Arity t1 = Arity t2 \<Longrightarrow>
   \<exists>i. can_take_transition t2 i c \<Longrightarrow>
   \<not> subsumes t1 c t2"
  apply (rule bad_guards)
  apply simp
  apply (simp add: can_take_def can_take_transition_def Bex_def)
  apply (erule exE)+
  apply (erule conjE)+
  apply (erule exE)+
  apply (erule conjE)+
  apply (case_tac "\<exists>x. x \<in> set b \<and> x \<notin> set ba")
   defer
  apply auto[1]
  apply (erule exE)+
  apply (erule conjE)+
  apply (rule_tac x="list_update i a x" in exI)
  apply simp
  apply standard
  using another_swap_inputs apply blast
  by (metis In_apply_guards In_in_get_Ins input2state_not_None input2state_nth join_ir_def nth_list_update_eq option.distinct(1) option.inject vname.simps(5))


definition "lob_distinguished_3 t1 t2 = (\<exists>(i, l) \<in> set (get_Ins (Guards t2)). filter (\<lambda>g. gexp_constrains g (V (I i))) (Guards t2) = [(In (I i) l)] \<and>
    (\<exists>(i', l') \<in> set (get_Ins (Guards t1)). i = i' \<and> set l' \<subset> set l) \<and>
   Arity t1 = Arity t2)"

fun is_In :: "'a gexp \<Rightarrow> bool" where
  "is_In (In _ _) = True" |
  "is_In _ = False"

text\<open>The ``greatest upper bound'' (gob) heuristic is similar to \texttt{lob} but applies a more
intellegent approach to guard merging.\<close>

definition gob_aux :: "transition \<Rightarrow> transition \<Rightarrow> transition option" where
  "gob_aux t1 t2 = (if Outputs t1 = Outputs t2 \<and> Updates t1 = Updates t2 \<and> all_literal_args t1 \<and> all_literal_args t2 then
      Some \<lparr>Label = Label t1, Arity = Arity t1, Guards = remdups (filter (Not \<circ> is_In) (merge_guards (Guards t1) (Guards t2))), Outputs = Outputs t1, Updates = Updates t1\<rparr>
     else None)"

fun gob :: update_modifier where
  "gob t1ID t2ID s new _ old _ = (let
     t1 = (get_by_ids new t1ID);
     t2 = (get_by_ids new t2ID) in
     case gob_aux t1 t2 of
       None \<Rightarrow> None |
       Some gob_t \<Rightarrow>
           Some (replace_transitions new [(t1ID, gob_t), (t2ID, gob_t)])
   )"

text\<open>The ``Gung Ho'' heuristic simply drops the guards of both transitions, making them identical.\<close>
definition gung_ho_aux :: "transition \<Rightarrow> transition \<Rightarrow> transition option" where
  "gung_ho_aux t1 t2 = (if Outputs t1 = Outputs t2 \<and> Updates t1 = Updates t2 \<and> all_literal_args t1 \<and> all_literal_args t2 then
      Some \<lparr>Label = Label t1, Arity = Arity t1, Guards = [], Outputs = Outputs t1, Updates = Updates t1\<rparr>
     else None)"

fun gung_ho :: update_modifier where
  "gung_ho t1ID t2ID s new _ old _ = (let
     t1 = (get_by_ids new t1ID);
     t2 = (get_by_ids new t2ID) in
     case gung_ho_aux t1 t2 of
       None \<Rightarrow> None |
       Some gob_t \<Rightarrow>
           Some (replace_transitions new [(t1ID, gob_t), (t2ID, gob_t)])
   )"

lemma guard_subset_eq_outputs_updates_subsumption:
  "Label t1 = Label t2 \<Longrightarrow>
   Arity t1 = Arity t2 \<Longrightarrow>
   Outputs t1 = Outputs t2 \<Longrightarrow>
   Updates t1 = Updates t2 \<Longrightarrow>
   set (Guards t2) \<subseteq> set (Guards t1) \<Longrightarrow>
   subsumes t2 c t1"
  apply (simp add: subsumes_def)
  by (meson can_take_def can_take_subset can_take_transition_def)

lemma guard_subset_eq_outputs_updates_direct_subsumption:
  "Label t1 = Label t2 \<Longrightarrow>
   Arity t1 = Arity t2 \<Longrightarrow>
   Outputs t1 = Outputs t2 \<Longrightarrow>
   Updates t1 = Updates t2 \<Longrightarrow>
   set (Guards t2) \<subseteq> set (Guards t1) \<Longrightarrow>
   directly_subsumes m1 m2 s1 s2 t2 t1"
  apply (rule subsumes_in_all_contexts_directly_subsumes)
  by (simp add: guard_subset_eq_outputs_updates_subsumption)

lemma unconstrained_input:
  "\<forall>g\<in>set G. \<not> gexp_constrains g (V (I i)) \<Longrightarrow>
   apply_guards G (join_ir ia c) \<Longrightarrow>
   apply_guards G (join_ir (ia[i := x']) c)"
proof(induct G)
  case (Cons a G)
  then show ?case
    apply (simp add: apply_guards_cons)
    using input_not_constrained_gval_swap_inputs[of a i ia c x']
    by simp
qed auto

lemma each_input_guarded_once_cons:
   "\<forall>i\<in>\<Union> (enumerate_gexp_inputs ` set (a # G)). length (filter (\<lambda>g. gexp_constrains g (V (I i))) (a # G)) \<le> 1 \<Longrightarrow>
    \<forall>i\<in>\<Union> (enumerate_gexp_inputs ` set G). length (filter (\<lambda>g. gexp_constrains g (V (I i))) G) \<le> 1"
  apply (simp add: Ball_def)
  apply clarify
proof -
  fix x :: nat and xa :: "vname gexp"
  assume a1: "\<forall>x. (x \<in> enumerate_gexp_inputs a \<longrightarrow> length (if gexp_constrains a (V (I x)) then a # filter (\<lambda>g. gexp_constrains g (V (I x))) G else filter (\<lambda>g. gexp_constrains g (V (I x))) G) \<le> 1) \<and> ((\<exists>xa\<in>set G. x \<in> enumerate_gexp_inputs xa) \<longrightarrow> length (if gexp_constrains a (V (I x)) then a # filter (\<lambda>g. gexp_constrains g (V (I x))) G else filter (\<lambda>g. gexp_constrains g (V (I x))) G) \<le> 1)"
  assume a2: "xa \<in> set G"
  assume "x \<in> enumerate_gexp_inputs xa"
  then have "if gexp_constrains a (V (I x)) then length (a # filter (\<lambda>g. gexp_constrains g (V (I x))) G) \<le> 1 else length (filter (\<lambda>g. gexp_constrains g (V (I x))) G) \<le> 1"
    using a2 a1 by fastforce
  then show "length (filter (\<lambda>g. gexp_constrains g (V (I x))) G) \<le> 1"
    by (metis (no_types) impossible_Cons le_cases order.trans)
qed

lemma literal_args_can_take:
  "\<forall>g\<in>set G. \<exists>i v s. g = Eq (V (I i)) (L v) \<or> g = In (I i) s \<and> s \<noteq> [] \<Longrightarrow>
   \<forall>i\<in>\<Union> (enumerate_gexp_inputs ` set G). i < a \<Longrightarrow>
   \<forall>i\<in>\<Union> (enumerate_gexp_inputs ` set G). length (filter (\<lambda>g. gexp_constrains g (V (I i))) G) \<le> 1 \<Longrightarrow>
   \<exists>i. length i = a \<and> apply_guards G (join_ir i c)"
proof(induct G)
  case Nil
  then show ?case
    using Ex_list_of_length
    by auto
next
  case (Cons a G)
  then show ?case
    apply simp
    apply (case_tac "\<forall>y\<in>set G. \<forall>i\<in>enumerate_gexp_inputs y. length (filter (\<lambda>g. gexp_constrains g (V (I i))) G) \<le> 1")
     defer
    using each_input_guarded_once_cons apply auto[1]
    apply (simp add: ball_Un)
    apply clarsimp
    apply (induct a)
        apply simp
       apply simp
    subgoal for x2 i ia
      apply (case_tac x2)
          apply (rule_tac x="list_update i ia x1" in exI)
          apply (simp add: apply_guards_cons unconstrained_input filter_empty_conv)
         apply simp+
      done
      apply simp
    subgoal for _ x2 i ia
      apply (case_tac x2)
       apply simp
      subgoal for aa
        apply (rule_tac x="list_update i ia aa" in exI)
        apply (simp add: apply_guards_cons unconstrained_input filter_empty_conv)
        done
      done
    by simp
qed

lemma "(SOME x'. x' \<noteq> (v::value)) \<noteq> v"
proof(induct v)
  case (Num x)
  then show ?case
    by (metis (full_types) someI_ex value.simps(4))
next
  case (Str x)
  then show ?case
    by (metis (full_types) someI_ex value.simps(4))
qed

lemma opposite_gob_subsumption: "\<forall>g \<in> set (Guards t1). \<exists>i v s. g = Eq (V (I i)) (L v) \<or> (g = In (I i) s \<and> s \<noteq> []) \<Longrightarrow>
       \<forall>g \<in> set (Guards t2). \<exists>i v s. g = Eq (V (I i)) (L v) \<or> (g = In (I i) s \<and> s \<noteq> []) \<Longrightarrow>
       \<exists> i. \<exists>v. Eq (V (I i)) (L v) \<in> set (Guards t1) \<and>
         (\<forall>g \<in> set (Guards t2). \<not> gexp_constrains g (V (I i))) \<Longrightarrow>
       Arity t1 = Arity t2 \<Longrightarrow>
       \<forall>i \<in> enumerate_inputs t2. i < Arity t2 \<Longrightarrow>
       \<forall>i \<in> enumerate_inputs t2. length (filter (\<lambda>g. gexp_constrains g (V (I i))) (Guards t2)) \<le> 1 \<Longrightarrow>
       \<not> subsumes t1 c t2"
  apply (rule bad_guards)
  apply (simp add: enumerate_inputs_def can_take_transition_def can_take_def Bex_def)
  using literal_args_can_take[of "Guards t2" "Arity t2" c]
  apply simp
  apply clarify
  subgoal for i ia v
    apply (rule_tac x="list_update ia i (Eps (\<lambda>x'. x' \<noteq> v))" in exI)
    apply simp
    apply standard
     apply (simp add: apply_guards_def)
    using input_not_constrained_gval_swap_inputs apply simp
    apply (simp add: apply_guards_def Bex_def)
    apply (rule_tac x="Eq (V (I i)) (L v)" in exI)
    apply (simp add: join_ir_def)
    apply (case_tac "input2state (ia[i := SOME x'. x' \<noteq> v]) $ i")
     apply simp
    apply simp
    apply (case_tac "i < length ia")
     apply (simp add: input2state_nth)
     apply (case_tac v)
      apply (metis (mono_tags) someI_ex value.simps(4))
     apply (metis (mono_tags) someI_ex value.simps(4))
    by (metis input2state_within_bounds length_list_update)
  done

fun is_lit_eq :: "vname gexp \<Rightarrow> nat \<Rightarrow> bool" where
  "is_lit_eq (Eq (V (I i)) (L v)) i' = (i = i')" |
  "is_lit_eq _ _ = False"

lemma "(\<exists>v. Eq (V (I i)) (L v) \<in> set G) = (\<exists>g \<in> set G. is_lit_eq g i)"
  by (metis is_lit_eq.elims(2) is_lit_eq.simps(1))

fun is_lit_eq_general :: "vname gexp \<Rightarrow> bool" where
  "is_lit_eq_general (Eq (V (I _)) (L _)) = True" |
  "is_lit_eq_general _ = False"

fun is_input_in :: "vname gexp \<Rightarrow> bool" where
  "is_input_in (In (I i) s) = (s \<noteq> [])" |
  "is_input_in _ = False"

definition "opposite_gob t1 t2 = (
       (\<forall>g \<in> set (Guards t1). is_lit_eq_general g \<or> is_input_in g) \<and>
       (\<forall>g \<in> set (Guards t2). is_lit_eq_general g \<or> is_input_in g) \<and>
       (\<exists> i \<in> (enumerate_inputs t1 \<union> enumerate_inputs t2). (\<exists>g \<in> set (Guards t1). is_lit_eq g i) \<and>
         (\<forall>g \<in> set (Guards t2). \<not> gexp_constrains g (V (I i)))) \<and>
       Arity t1 = Arity t2 \<and>
       (\<forall>i \<in> enumerate_inputs t2. i < Arity t2) \<and>
       (\<forall>i \<in> enumerate_inputs t2. length (filter (\<lambda>g. gexp_constrains g (V (I i))) (Guards t2)) \<le> 1))"

lemma "is_lit_eq_general g \<or> is_input_in g \<Longrightarrow>
       \<exists>i v s. g = Eq (V (I i)) (L v) \<or> g = In (I i) s \<and> s \<noteq> []"
  by (meson is_input_in.elims(2) is_lit_eq_general.elims(2))

lemma opposite_gob_directly_subsumption:
  "opposite_gob t1 t2 \<Longrightarrow> \<not> subsumes t1 c t2"
  apply (rule opposite_gob_subsumption)
  unfolding opposite_gob_def
       apply (meson is_input_in.elims(2) is_lit_eq_general.elims(2))+
     apply (metis is_lit_eq.elims(2))
  by auto

fun get_in :: "'a gexp \<Rightarrow> ('a \<times> value list) option" where
  "get_in (In v s) = Some (v, s)" |
  "get_in _ = None"

lemma not_subset_not_in: "(\<not> s1 \<subseteq> s2) = (\<exists>i. i \<in> s1 \<and> i \<notin> s2)"
  by auto

lemma get_in_is: "(get_in x = Some (v, s1)) = (x = In v s1)"
  by (induct x, auto)

lemma gval_rearrange:
  "g \<in> set G \<Longrightarrow>
   gval g s = true \<Longrightarrow>
   apply_guards (removeAll g G) s \<Longrightarrow>
   apply_guards G s"
proof(induct G)
  case (Cons a G)
  then show ?case
    apply (simp only: apply_guards_cons)
    apply standard
     apply (metis apply_guards_cons removeAll.simps(2))
    by (metis apply_guards_cons removeAll.simps(2) removeAll_id)
qed auto

lemma singleton_list: "(length l = 1) = (\<exists>e. l = [e])"
  by (induct l, auto)

lemma remove_restricted:
  "g \<in> set G \<Longrightarrow>
   gexp_constrains g (V v) \<Longrightarrow>
   restricted_once v G \<Longrightarrow>
   not_restricted v (removeAll g G)"
  apply (simp add: restricted_once_def not_restricted_def singleton_list)
  apply clarify
  subgoal for e 
    apply (case_tac "e = g")
     defer
     apply (metis (no_types, lifting) DiffE Diff_insert_absorb Set.set_insert empty_set filter.simps(2) filter_append in_set_conv_decomp insert_iff list.set(2))
    apply (simp add: filter_empty_conv)
  proof -
    fix e :: "'a gexp"
    assume "filter (\<lambda>g. gexp_constrains g (V v)) G = [g]"
    then have "{g \<in> set G. gexp_constrains g (V v)} = {g}"
      by (metis (no_types) empty_set list.simps(15) set_filter)
    then show "\<forall>g\<in>set G - {g}. \<not> gexp_constrains g (V v)"
      by blast
  qed
  done

lemma unrestricted_input_swap:
  "not_restricted (I i) G \<Longrightarrow>
   apply_guards G (join_ir iaa c) \<Longrightarrow>
   apply_guards (removeAll g G) (join_ir (iaa[i := ia]) c)"
proof(induct G)
  case (Cons a G)
  then show ?case
    apply (simp add: apply_guards_cons not_restricted_def)
    apply safe
      apply (meson neq_Nil_conv)
     apply (metis input_not_constrained_gval_swap_inputs list.distinct(1))
    by (metis list.distinct(1))
qed auto

lemma apply_guards_remove_restricted:
  "g \<in> set G \<Longrightarrow>
   gexp_constrains g (V (I i)) \<Longrightarrow>
   restricted_once (I i) G \<Longrightarrow>
   apply_guards G (join_ir iaa c) \<Longrightarrow>
   apply_guards (removeAll g G) (join_ir (iaa[i := ia]) c)"
proof(induct G)
  case (Cons a G)
  then show ?case
    apply simp
    apply safe
      apply (rule unrestricted_input_swap)
       apply (simp add: not_restricted_def restricted_once_def)
      apply (meson apply_guards_subset set_subset_Cons)
     apply (simp add: apply_guards_rearrange not_restricted_def restricted_once_def unrestricted_input_swap)
    by (metis apply_guards_cons filter.simps(2) filter_empty_conv input_not_constrained_gval_swap_inputs list.inject restricted_once_def singleton_list)
qed auto

lemma In_swap_inputs:
  "In (I i) s2 \<in> set G \<Longrightarrow>
   restricted_once (I i) G \<Longrightarrow>
   ia \<in> set s2 \<Longrightarrow>
   apply_guards G (join_ir iaa c) \<Longrightarrow>
   apply_guards G (join_ir (iaa[i := ia]) c)"
  using apply_guards_remove_restricted[of "In (I i) s2" G i iaa c ia]
  apply simp
  apply (rule gval_rearrange[of "In (I i) s2"])
    apply simp
   apply (metis filter_empty_conv gval_each_one input_not_constrained_gval_swap_inputs length_0_conv not_restricted_def remove_restricted test_aux)
  by blast

definition these :: "'a option list \<Rightarrow> 'a list" where
  "these as = map (\<lambda>x. case x of Some y \<Rightarrow> y) (filter (\<lambda>x. x \<noteq> None) as)"

lemma these_cons: "these (a#as) = (case a of None \<Rightarrow> these as | Some x \<Rightarrow> x#(these as))"
  apply (cases a)
   apply (simp add: these_def)
  by (simp add: these_def)

definition get_ins :: "vname gexp list \<Rightarrow> (nat \<times> value list) list" where
  "get_ins g = map (\<lambda>(v, s). case v of I i \<Rightarrow> (i, s)) (filter (\<lambda>(v, _). case v of I _ \<Rightarrow> True | R _ \<Rightarrow> False) (these (map get_in g)))"

lemma in_get_ins:
  "(I x1a, b) \<in> set (these (map get_in G)) \<Longrightarrow>
   In (I x1a) b \<in> set G"
proof(induct G)
  case Nil
  then show ?case
    by (simp add: these_def)
next
  case (Cons a G)
  then show ?case
    apply simp
    apply (simp add: these_cons)
    apply (cases a)
    by auto
qed

lemma restricted_head: "\<forall>v. restricted_once v (Eq (V x2) (L x1) # G) \<or> not_restricted v (Eq (V x2) (L x1) # G) \<Longrightarrow>
      not_restricted x2 G"
  apply (erule_tac x=x2 in allE)
  by (simp add: restricted_once_def not_restricted_def)

fun atomic :: "'a gexp \<Rightarrow> bool" where
  "atomic (Eq (V _) (L _)) = True" |
  "atomic (In _ _) = True" |
  "atomic _ = False"

lemma restricted_max_once_cons: "\<forall>v. restricted_once v (g#gs) \<or> not_restricted v (g#gs) \<Longrightarrow>
       \<forall>v. restricted_once v gs \<or> not_restricted v gs"
  apply (simp add: restricted_once_def not_restricted_def)
  apply safe
  subgoal for v 
    by (erule_tac x=v in allE)
      (metis (mono_tags, lifting) list.distinct(1) list.inject singleton_list)
  done

lemma not_restricted_swap_inputs:
  "not_restricted (I x1a) G \<Longrightarrow>
   apply_guards G (join_ir i r) \<Longrightarrow>
   apply_guards G (join_ir (i[x1a := x1]) r)"
proof(induct G)
  case (Cons a G)
  then show ?case
    apply (simp add: apply_guards_cons not_restricted_cons)
    using input_not_constrained_gval_swap_inputs by auto
qed auto
end
